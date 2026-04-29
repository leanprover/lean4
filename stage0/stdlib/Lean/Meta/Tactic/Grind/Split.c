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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Meta_Grind_Goal_isCongruent(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
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
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6_value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "may be irrelevant\na: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\nb: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\neq: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_a: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\narg_b: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", gen: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14;
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
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5_value;
static const lean_string_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__6 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__6_value;
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value_aux_3),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7 = (const lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7_value;
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 96, 222, 221, 183, 249, 85, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_isSorryAlt___closed__1_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_0),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7_value_aux_1),((lean_object*)&l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
lean_inc(v___y_119_);
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
lean_inc(v___y_94_);
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
lean_inc(v___y_101_);
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
lean_dec(v___x_643_);
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
uint8_t v___x_9418__boxed_668_; uint8_t v_d_boxed_669_; lean_object* v_res_670_; 
v___x_9418__boxed_668_ = lean_unbox(v___x_653_);
v_d_boxed_669_ = lean_unbox(v_d_654_);
v_res_670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_652_, v___x_9418__boxed_668_, v_d_boxed_669_, v_a_655_, v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
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
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
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
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v_as_786_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_804_, v_x_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
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
v_split_836_ = lean_ctor_get(v_toGoalState_835_, 14);
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
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
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
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec(v___y_874_);
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
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
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
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
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
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec(v___y_984_);
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
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v_vals_1024_);
lean_dec_ref(v_keys_1023_);
return v_res_1039_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
lean_ctor_set(v___x_1045_, 2, v___x_1044_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
lean_ctor_set(v___x_1045_, 4, v___x_1043_);
lean_ctor_set(v___x_1045_, 5, v___x_1043_);
lean_ctor_set(v___x_1045_, 6, v___x_1043_);
lean_ctor_set(v___x_1045_, 7, v___x_1043_);
lean_ctor_set(v___x_1045_, 8, v___x_1043_);
lean_ctor_set(v___x_1045_, 9, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(32u);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1049_ = ((size_t)5ULL);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_unsigned_to_nat(32u);
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1054_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
lean_ctor_set(v___x_1054_, 2, v___x_1050_);
lean_ctor_set(v___x_1054_, 3, v___x_1050_);
lean_ctor_set_usize(v___x_1054_, 4, v___x_1049_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_box(1);
v___x_1056_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1056_);
lean_ctor_set(v___x_1058_, 2, v___x_1055_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1080_, lean_object* v_declHint_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_env_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_st_ref_get(v___y_1082_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1086_ = l_Lean_Name_isAnonymous(v_declHint_1081_);
if (v___x_1086_ == 0)
{
uint8_t v_isExporting_1087_; 
v_isExporting_1087_ = lean_ctor_get_uint8(v_env_1085_, sizeof(void*)*8);
if (v_isExporting_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_msg_1080_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
lean_inc_ref(v_env_1085_);
v___x_1089_ = l_Lean_Environment_setExporting(v_env_1085_, v___x_1086_);
lean_inc(v_declHint_1081_);
lean_inc_ref(v___x_1089_);
v___x_1090_ = l_Lean_Environment_contains(v___x_1089_, v_declHint_1081_, v_isExporting_1087_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v___x_1089_);
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_msg_1080_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_c_1097_; lean_object* v___x_1098_; 
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1094_ = l_Lean_Options_empty;
v___x_1095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1089_);
lean_ctor_set(v___x_1095_, 1, v___x_1092_);
lean_ctor_set(v___x_1095_, 2, v___x_1093_);
lean_ctor_set(v___x_1095_, 3, v___x_1094_);
lean_inc(v_declHint_1081_);
v___x_1096_ = l_Lean_MessageData_ofConstName(v_declHint_1081_, v___x_1086_);
v_c_1097_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1097_, 0, v___x_1095_);
lean_ctor_set(v_c_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1085_, v_declHint_1081_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_c_1097_);
v___x_1101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_note(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_msg_1080_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1141_; 
v_val_1106_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1108_ = v___x_1098_;
v_isShared_1109_ = v_isSharedCheck_1141_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_val_1106_);
lean_dec(v___x_1098_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1141_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_mod_1113_; uint8_t v___x_1114_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_Environment_header(v_env_1085_);
lean_dec_ref(v_env_1085_);
v___x_1112_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1111_);
v_mod_1113_ = lean_array_get(v___x_1110_, v___x_1112_, v_val_1106_);
lean_dec(v_val_1106_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = l_Lean_isPrivateName(v_declHint_1081_);
lean_dec(v_declHint_1081_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_c_1097_);
v___x_1117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_MessageData_ofName(v_mod_1113_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_MessageData_note(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_msg_1080_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1124_);
v___x_1126_ = v___x_1108_;
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
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_c_1097_);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_ofName(v_mod_1113_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_MessageData_note(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_msg_1080_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1137_);
v___x_1139_ = v___x_1108_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_msg_1080_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1143_, lean_object* v_declHint_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1143_, v_declHint_1144_, v___y_1145_);
lean_dec(v___y_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1148_, lean_object* v_declHint_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
v___x_1161_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1148_, v_declHint_1149_, v___y_1159_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = l_Lean_unknownIdentifierMessageTag;
v___x_1167_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1172_, lean_object* v_declHint_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1172_, v_declHint_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec(v___y_1174_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; lean_object* v_mctx_1195_; lean_object* v_lctx_1196_; lean_object* v_options_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_st_ref_get(v___y_1188_);
v_mctx_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_ref(v_mctx_1195_);
lean_dec(v___x_1194_);
v_lctx_1196_ = lean_ctor_get(v___y_1187_, 2);
v_options_1197_ = lean_ctor_get(v___y_1189_, 2);
lean_inc_ref(v_options_1197_);
lean_inc_ref(v_lctx_1196_);
v___x_1198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1198_, 0, v_env_1193_);
lean_ctor_set(v___x_1198_, 1, v_mctx_1195_);
lean_ctor_set(v___x_1198_, 2, v_lctx_1196_);
lean_ctor_set(v___x_1198_, 3, v_options_1197_);
v___x_1199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_msgData_1186_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_ref_1214_ = lean_ctor_get(v___y_1211_, 5);
v___x_1215_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_inc(v_ref_1214_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_ref_1214_);
lean_ctor_set(v___x_1220_, 1, v_a_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 1);
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1232_, lean_object* v_msg_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_fileName_1245_; lean_object* v_fileMap_1246_; lean_object* v_options_1247_; lean_object* v_currRecDepth_1248_; lean_object* v_maxRecDepth_1249_; lean_object* v_ref_1250_; lean_object* v_currNamespace_1251_; lean_object* v_openDecls_1252_; lean_object* v_initHeartbeats_1253_; lean_object* v_maxHeartbeats_1254_; lean_object* v_quotContext_1255_; lean_object* v_currMacroScope_1256_; uint8_t v_diag_1257_; lean_object* v_cancelTk_x3f_1258_; uint8_t v_suppressElabErrors_1259_; lean_object* v_inheritedTraceOptions_1260_; lean_object* v_ref_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_fileName_1245_ = lean_ctor_get(v___y_1242_, 0);
v_fileMap_1246_ = lean_ctor_get(v___y_1242_, 1);
v_options_1247_ = lean_ctor_get(v___y_1242_, 2);
v_currRecDepth_1248_ = lean_ctor_get(v___y_1242_, 3);
v_maxRecDepth_1249_ = lean_ctor_get(v___y_1242_, 4);
v_ref_1250_ = lean_ctor_get(v___y_1242_, 5);
v_currNamespace_1251_ = lean_ctor_get(v___y_1242_, 6);
v_openDecls_1252_ = lean_ctor_get(v___y_1242_, 7);
v_initHeartbeats_1253_ = lean_ctor_get(v___y_1242_, 8);
v_maxHeartbeats_1254_ = lean_ctor_get(v___y_1242_, 9);
v_quotContext_1255_ = lean_ctor_get(v___y_1242_, 10);
v_currMacroScope_1256_ = lean_ctor_get(v___y_1242_, 11);
v_diag_1257_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*14);
v_cancelTk_x3f_1258_ = lean_ctor_get(v___y_1242_, 12);
v_suppressElabErrors_1259_ = lean_ctor_get_uint8(v___y_1242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1260_ = lean_ctor_get(v___y_1242_, 13);
v_ref_1261_ = l_Lean_replaceRef(v_ref_1232_, v_ref_1250_);
lean_inc_ref(v_inheritedTraceOptions_1260_);
lean_inc(v_cancelTk_x3f_1258_);
lean_inc(v_currMacroScope_1256_);
lean_inc(v_quotContext_1255_);
lean_inc(v_maxHeartbeats_1254_);
lean_inc(v_initHeartbeats_1253_);
lean_inc(v_openDecls_1252_);
lean_inc(v_currNamespace_1251_);
lean_inc(v_maxRecDepth_1249_);
lean_inc(v_currRecDepth_1248_);
lean_inc_ref(v_options_1247_);
lean_inc_ref(v_fileMap_1246_);
lean_inc_ref(v_fileName_1245_);
v___x_1262_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1262_, 0, v_fileName_1245_);
lean_ctor_set(v___x_1262_, 1, v_fileMap_1246_);
lean_ctor_set(v___x_1262_, 2, v_options_1247_);
lean_ctor_set(v___x_1262_, 3, v_currRecDepth_1248_);
lean_ctor_set(v___x_1262_, 4, v_maxRecDepth_1249_);
lean_ctor_set(v___x_1262_, 5, v_ref_1261_);
lean_ctor_set(v___x_1262_, 6, v_currNamespace_1251_);
lean_ctor_set(v___x_1262_, 7, v_openDecls_1252_);
lean_ctor_set(v___x_1262_, 8, v_initHeartbeats_1253_);
lean_ctor_set(v___x_1262_, 9, v_maxHeartbeats_1254_);
lean_ctor_set(v___x_1262_, 10, v_quotContext_1255_);
lean_ctor_set(v___x_1262_, 11, v_currMacroScope_1256_);
lean_ctor_set(v___x_1262_, 12, v_cancelTk_x3f_1258_);
lean_ctor_set(v___x_1262_, 13, v_inheritedTraceOptions_1260_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*14, v_diag_1257_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*14 + 1, v_suppressElabErrors_1259_);
v___x_1263_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1233_, v___y_1240_, v___y_1241_, v___x_1262_, v___y_1243_);
lean_dec_ref(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1264_, v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v_ref_1264_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1278_, lean_object* v_msg_1279_, lean_object* v_declHint_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1294_; 
v___x_1292_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1279_, v_declHint_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1278_, v_a_1293_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1295_, lean_object* v_msg_1296_, lean_object* v_declHint_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1295_, v_msg_1296_, v_declHint_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v_ref_1295_);
return v_res_1309_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1316_, lean_object* v_constName_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1329_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1330_ = 0;
lean_inc(v_constName_1317_);
v___x_1331_ = l_Lean_MessageData_ofConstName(v_constName_1317_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1316_, v___x_1334_, v_constName_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1336_, lean_object* v_constName_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1336_, v_constName_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v_ref_1336_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_ref_1362_; lean_object* v___x_1363_; 
v_ref_1362_ = lean_ctor_get(v___y_1359_, 5);
v___x_1363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1362_, v_constName_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v___y_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v_env_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; 
v___x_1389_ = lean_st_ref_get(v___y_1387_);
v_env_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc_ref(v_env_1390_);
lean_dec(v___x_1389_);
v___x_1391_ = 0;
lean_inc(v_constName_1377_);
v___x_1392_ = l_Lean_Environment_find_x3f(v_env_1390_, v_constName_1377_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1393_;
}
else
{
lean_object* v_val_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_constName_1377_);
v_val_1394_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1392_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_val_1394_);
lean_dec(v___x_1392_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 0);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_val_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec(v___y_1403_);
return v_res_1414_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1415_; double v___x_1416_; 
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_float_of_nat(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1420_, lean_object* v_msg_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_ref_1427_; lean_object* v___x_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1473_; 
v_ref_1427_ = lean_ctor_get(v___y_1424_, 5);
v___x_1428_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1473_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1473_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v_traceState_1434_; lean_object* v_env_1435_; lean_object* v_nextMacroScope_1436_; lean_object* v_ngen_1437_; lean_object* v_auxDeclNGen_1438_; lean_object* v_cache_1439_; lean_object* v_messages_1440_; lean_object* v_infoState_1441_; lean_object* v_snapshotTasks_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1472_; 
v___x_1433_ = lean_st_ref_take(v___y_1425_);
v_traceState_1434_ = lean_ctor_get(v___x_1433_, 4);
v_env_1435_ = lean_ctor_get(v___x_1433_, 0);
v_nextMacroScope_1436_ = lean_ctor_get(v___x_1433_, 1);
v_ngen_1437_ = lean_ctor_get(v___x_1433_, 2);
v_auxDeclNGen_1438_ = lean_ctor_get(v___x_1433_, 3);
v_cache_1439_ = lean_ctor_get(v___x_1433_, 5);
v_messages_1440_ = lean_ctor_get(v___x_1433_, 6);
v_infoState_1441_ = lean_ctor_get(v___x_1433_, 7);
v_snapshotTasks_1442_ = lean_ctor_get(v___x_1433_, 8);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1444_ = v___x_1433_;
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snapshotTasks_1442_);
lean_inc(v_infoState_1441_);
lean_inc(v_messages_1440_);
lean_inc(v_cache_1439_);
lean_inc(v_traceState_1434_);
lean_inc(v_auxDeclNGen_1438_);
lean_inc(v_ngen_1437_);
lean_inc(v_nextMacroScope_1436_);
lean_inc(v_env_1435_);
lean_dec(v___x_1433_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1472_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
uint64_t v_tid_1446_; lean_object* v_traces_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1471_; 
v_tid_1446_ = lean_ctor_get_uint64(v_traceState_1434_, sizeof(void*)*1);
v_traces_1447_ = lean_ctor_get(v_traceState_1434_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_traceState_1434_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1449_ = v_traceState_1434_;
v_isShared_1450_ = v_isSharedCheck_1471_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_traces_1447_);
lean_dec(v_traceState_1434_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1471_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; double v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1453_ = 0;
v___x_1454_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1455_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1455_, 0, v_cls_1420_);
lean_ctor_set(v___x_1455_, 1, v___x_1451_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
lean_ctor_set_float(v___x_1455_, sizeof(void*)*3, v___x_1452_);
lean_ctor_set_float(v___x_1455_, sizeof(void*)*3 + 8, v___x_1452_);
lean_ctor_set_uint8(v___x_1455_, sizeof(void*)*3 + 16, v___x_1453_);
v___x_1456_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1457_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v_a_1429_);
lean_ctor_set(v___x_1457_, 2, v___x_1456_);
lean_inc(v_ref_1427_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_ref_1427_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_PersistentArray_push___redArg(v_traces_1447_, v___x_1458_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1459_);
v___x_1461_ = v___x_1449_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1459_);
lean_ctor_set_uint64(v_reuseFailAlloc_1470_, sizeof(void*)*1, v_tid_1446_);
v___x_1461_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v___x_1461_);
v___x_1463_ = v___x_1444_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_env_1435_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_nextMacroScope_1436_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_ngen_1437_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_auxDeclNGen_1438_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_cache_1439_);
lean_ctor_set(v_reuseFailAlloc_1469_, 6, v_messages_1440_);
lean_ctor_set(v_reuseFailAlloc_1469_, 7, v_infoState_1441_);
lean_ctor_set(v_reuseFailAlloc_1469_, 8, v_snapshotTasks_1442_);
v___x_1463_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1464_ = lean_st_ref_set(v___y_1425_, v___x_1463_);
v___x_1465_ = lean_box(0);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1465_);
v___x_1467_ = v___x_1431_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1474_, lean_object* v_msg_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1474_, v_msg_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1500_ = l_Lean_Name_append(v___x_1499_, v___x_1498_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
uint8_t v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; uint8_t v___y_1651_; lean_object* v___x_1765_; 
lean_inc_ref(v_e_1513_);
v___x_1765_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1513_, v_a_1521_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1807_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1807_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1807_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = l_Lean_Expr_cleanupAnnotations(v_a_1766_);
v___x_1784_ = l_Lean_Expr_isApp(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_del_object(v___x_1768_);
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
goto v___jp_1770_;
}
else
{
lean_object* v_arg_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_arg_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc_ref(v_arg_1785_);
v___x_1786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1783_);
v___x_1787_ = l_Lean_Expr_isApp(v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1786_);
lean_dec_ref(v_arg_1785_);
lean_del_object(v___x_1768_);
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
goto v___jp_1770_;
}
else
{
lean_object* v_arg_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_arg_1788_ = lean_ctor_get(v___x_1786_, 1);
lean_inc_ref(v_arg_1788_);
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1786_);
v___x_1790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1791_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1793_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1794_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_del_object(v___x_1768_);
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1797_ = l_Lean_Expr_isConstOf(v___x_1795_, v___x_1796_);
lean_dec_ref(v___x_1795_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_del_object(v___x_1768_);
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
goto v___jp_1770_;
}
else
{
uint8_t v___x_1798_; 
lean_inc_ref(v_e_1513_);
v___x_1798_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1513_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_e_1513_);
v___x_1799_ = lean_unsigned_to_nat(2u);
v___x_1800_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1, v___x_1798_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*1 + 1, v___x_1798_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1800_);
v___x_1802_ = v___x_1768_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
else
{
lean_object* v___x_1804_; 
lean_del_object(v___x_1768_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1513_, v_arg_1788_, v_arg_1785_, v_a_1514_, v_a_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1804_;
}
}
}
}
else
{
lean_object* v___x_1805_; 
lean_dec_ref(v___x_1789_);
lean_del_object(v___x_1768_);
v___x_1805_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1513_, v_arg_1788_, v_arg_1785_, v_a_1514_, v_a_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1805_;
}
}
else
{
lean_object* v___x_1806_; 
lean_dec_ref(v___x_1789_);
lean_del_object(v___x_1768_);
v___x_1806_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1513_, v_arg_1788_, v_arg_1785_, v_a_1514_, v_a_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1806_;
}
}
}
v___jp_1770_:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Grind_isIte(v_e_1513_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; 
v___x_1782_ = l_Lean_Meta_Grind_isDIte(v_e_1513_);
v___y_1641_ = v___y_1775_;
v___y_1642_ = v___y_1778_;
v___y_1643_ = v___y_1773_;
v___y_1644_ = v___y_1771_;
v___y_1645_ = v___y_1777_;
v___y_1646_ = v___y_1776_;
v___y_1647_ = v___y_1774_;
v___y_1648_ = v___y_1780_;
v___y_1649_ = v___y_1779_;
v___y_1650_ = v___y_1772_;
v___y_1651_ = v___x_1782_;
goto v___jp_1640_;
}
else
{
v___y_1641_ = v___y_1775_;
v___y_1642_ = v___y_1778_;
v___y_1643_ = v___y_1773_;
v___y_1644_ = v___y_1771_;
v___y_1645_ = v___y_1777_;
v___y_1646_ = v___y_1776_;
v___y_1647_ = v___y_1774_;
v___y_1648_ = v___y_1780_;
v___y_1649_ = v___y_1779_;
v___y_1650_ = v___y_1772_;
v___y_1651_ = v___x_1781_;
goto v___jp_1640_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_e_1513_);
v_a_1808_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1765_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1765_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
v___jp_1531_:
{
uint8_t v___x_1543_; 
v___x_1543_ = l_Lean_Expr_isFVar(v_e_1513_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v_e_1513_);
v___x_1544_ = lean_box(1);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; 
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc_ref(v_e_1513_);
v___x_1546_ = lean_infer_type(v_e_1513_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_Lean_Meta_whnfD(v_a_1547_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_n(v_a_1549_, 2);
lean_dec_ref(v___x_1548_);
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1551_ = l_Lean_MessageData_ofExpr(v_e_1513_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_indentExpr(v_a_1549_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_Expr_getAppFn(v_a_1549_);
lean_dec(v_a_1549_);
if (lean_obj_tag(v___x_1557_) == 4)
{
lean_object* v_declName_1558_; lean_object* v___x_1559_; 
v_declName_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_declName_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1558_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1592_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1592_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1592_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
if (lean_obj_tag(v_a_1560_) == 5)
{
lean_object* v_val_1564_; lean_object* v_ctors_1565_; uint8_t v_isRec_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec_ref(v___x_1556_);
v_val_1564_ = lean_ctor_get(v_a_1560_, 0);
lean_inc_ref(v_val_1564_);
lean_dec_ref(v_a_1560_);
v_ctors_1565_ = lean_ctor_get(v_val_1564_, 4);
lean_inc(v_ctors_1565_);
v_isRec_1566_ = lean_ctor_get_uint8(v_val_1564_, sizeof(void*)*6);
lean_dec_ref(v_val_1564_);
v___x_1567_ = l_List_lengthTR___redArg(v_ctors_1565_);
lean_dec(v_ctors_1565_);
v___x_1568_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*1, v_isRec_1566_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*1 + 1, v___y_1532_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1568_);
v___x_1570_ = v___x_1562_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1562_);
lean_dec(v_a_1560_);
v___x_1572_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1537_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; uint8_t v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
if (v___x_1574_ == 0)
{
lean_dec_ref(v___x_1556_);
goto v___jp_1528_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Sym_reportIssue(v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec_ref(v___x_1575_);
goto v___jp_1528_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___x_1556_);
v_a_1584_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1572_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1572_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v___x_1556_);
v_a_1593_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1559_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1559_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v___x_1601_; 
lean_dec_ref(v___x_1557_);
v___x_1601_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1537_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; uint8_t v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_unbox(v_a_1602_);
lean_dec(v_a_1602_);
if (v___x_1603_ == 0)
{
lean_dec_ref(v___x_1556_);
goto v___jp_1525_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Sym_reportIssue(v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec_ref(v___x_1604_);
goto v___jp_1525_;
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
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
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v___x_1556_);
v_a_1613_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1601_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1601_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_e_1513_);
v_a_1621_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1548_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1548_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_e_1513_);
v_a_1629_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1546_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1546_);
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
}
v___jp_1637_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
v___jp_1640_:
{
if (v___y_1651_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1513_, v___y_1644_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_unbox(v_a_1653_);
lean_dec(v_a_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_inc_ref(v_e_1513_);
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1513_, v___y_1644_, v___y_1650_, v___y_1643_, v___y_1647_, v___y_1641_, v___y_1646_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1715_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1715_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1715_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_unbox(v_a_1656_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v_env_1662_; lean_object* v___x_1663_; 
v___x_1661_ = lean_st_ref_get(v___y_1648_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc_ref(v_env_1662_);
lean_dec(v___x_1661_);
v___x_1663_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1662_, v_e_1513_);
if (lean_obj_tag(v___x_1663_) == 1)
{
lean_object* v_val_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1670_; 
lean_dec_ref(v_e_1513_);
v_val_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1664_);
lean_dec(v_val_1664_);
v___x_1666_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
v___x_1667_ = lean_unbox(v_a_1656_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*1, v___x_1667_);
v___x_1668_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*1 + 1, v___x_1668_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1666_);
v___x_1670_ = v___x_1658_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1666_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
else
{
lean_object* v___x_1672_; 
lean_dec(v___x_1663_);
lean_del_object(v___x_1658_);
v___x_1672_ = l_Lean_Expr_getAppFn(v_e_1513_);
if (lean_obj_tag(v___x_1672_) == 4)
{
lean_object* v_declName_1673_; lean_object* v___x_1674_; 
v_declName_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_declName_1673_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1673_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
if (lean_obj_tag(v_a_1675_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_val_1676_);
lean_dec_ref(v_a_1675_);
lean_inc_ref(v_e_1513_);
v___x_1677_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1513_, v___y_1644_, v___y_1641_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1692_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1692_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_unbox(v_a_1678_);
lean_dec(v_a_1678_);
if (v___x_1682_ == 0)
{
uint8_t v___x_1683_; 
lean_del_object(v___x_1680_);
lean_dec(v_val_1676_);
v___x_1683_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
v___y_1532_ = v___x_1683_;
v___y_1533_ = v___y_1644_;
v___y_1534_ = v___y_1650_;
v___y_1535_ = v___y_1643_;
v___y_1536_ = v___y_1647_;
v___y_1537_ = v___y_1641_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1642_;
v___y_1541_ = v___y_1649_;
v___y_1542_ = v___y_1648_;
goto v___jp_1531_;
}
else
{
lean_object* v_ctors_1684_; uint8_t v_isRec_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1690_; 
lean_dec_ref(v_e_1513_);
v_ctors_1684_ = lean_ctor_get(v_val_1676_, 4);
lean_inc(v_ctors_1684_);
v_isRec_1685_ = lean_ctor_get_uint8(v_val_1676_, sizeof(void*)*6);
lean_dec(v_val_1676_);
v___x_1686_ = l_List_lengthTR___redArg(v_ctors_1684_);
lean_dec(v_ctors_1684_);
v___x_1687_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*1, v_isRec_1685_);
v___x_1688_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*1 + 1, v___x_1688_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1687_);
v___x_1690_ = v___x_1680_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1687_);
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
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_val_1676_);
lean_dec(v_a_1656_);
lean_dec_ref(v_e_1513_);
v_a_1693_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1677_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1677_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
uint8_t v___x_1701_; 
lean_dec(v_a_1675_);
v___x_1701_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
v___y_1532_ = v___x_1701_;
v___y_1533_ = v___y_1644_;
v___y_1534_ = v___y_1650_;
v___y_1535_ = v___y_1643_;
v___y_1536_ = v___y_1647_;
v___y_1537_ = v___y_1641_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1642_;
v___y_1541_ = v___y_1649_;
v___y_1542_ = v___y_1648_;
goto v___jp_1531_;
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1656_);
lean_dec_ref(v_e_1513_);
v_a_1702_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1674_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1674_);
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
uint8_t v___x_1710_; 
lean_dec_ref(v___x_1672_);
v___x_1710_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
v___y_1532_ = v___x_1710_;
v___y_1533_ = v___y_1644_;
v___y_1534_ = v___y_1650_;
v___y_1535_ = v___y_1643_;
v___y_1536_ = v___y_1647_;
v___y_1537_ = v___y_1641_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1642_;
v___y_1541_ = v___y_1649_;
v___y_1542_ = v___y_1648_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec(v_a_1656_);
lean_dec_ref(v_e_1513_);
v___x_1711_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1711_);
v___x_1713_ = v___x_1658_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v_e_1513_);
v_a_1716_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1655_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1655_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_options_1724_; uint8_t v_hasTrace_1725_; 
v_options_1724_ = lean_ctor_get(v___y_1649_, 2);
v_hasTrace_1725_ = lean_ctor_get_uint8(v_options_1724_, sizeof(void*)*1);
if (v_hasTrace_1725_ == 0)
{
lean_dec_ref(v_e_1513_);
goto v___jp_1637_;
}
else
{
lean_object* v_inheritedTraceOptions_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_inheritedTraceOptions_1726_ = lean_ctor_get(v___y_1649_, 13);
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1726_, v_options_1724_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_e_1513_);
goto v___jp_1637_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Meta_Grind_updateLastTag(v___y_1644_, v___y_1650_, v___y_1643_, v___y_1647_, v___y_1641_, v___y_1646_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec_ref(v___x_1730_);
v___x_1731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1732_ = l_Lean_MessageData_ofExpr(v_e_1513_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1727_, v___x_1733_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_dec_ref(v___x_1734_);
goto v___jp_1637_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
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
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_e_1513_);
v_a_1743_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1730_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1730_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v_e_1513_);
v_a_1751_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1652_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1652_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = l_Lean_Expr_getAppNumArgs(v_e_1513_);
v___x_1761_ = lean_nat_sub(v___x_1760_, v___x_1759_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_nat_sub(v___x_1761_, v___x_1759_);
lean_dec(v___x_1761_);
v___x_1763_ = l_Lean_Expr_getRevArg_x21(v_e_1513_, v___x_1762_);
lean_dec_ref(v_e_1513_);
v___x_1764_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1763_, v___y_1644_, v___y_1641_, v___y_1645_, v___y_1642_, v___y_1649_, v___y_1648_);
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec(v_a_1817_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1829_, v_msg_1830_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1843_, v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec(v___y_1845_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1857_, lean_object* v_constName_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_constName_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1871_, v_constName_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1885_, lean_object* v_ref_1886_, lean_object* v_constName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1886_, v_constName_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1900_, lean_object* v_ref_1901_, lean_object* v_constName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1900_, v_ref_1901_, v_constName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec(v_ref_1901_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1915_, lean_object* v_ref_1916_, lean_object* v_msg_1917_, lean_object* v_declHint_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1916_, v_msg_1917_, v_declHint_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v_declHint_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1931_, v_ref_1932_, v_msg_1933_, v_declHint_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v_ref_1932_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1947_, lean_object* v_declHint_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1947_, v_declHint_1948_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1961_, lean_object* v_declHint_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1961_, v_declHint_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1975_, lean_object* v_ref_1976_, lean_object* v_msg_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1976_, v_msg_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_ref_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1990_, v_ref_1991_, v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v_ref_1991_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2005_, lean_object* v_msg_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2006_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2019_, v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2033_, lean_object* v_x_2034_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_box(0);
return v___x_2035_;
}
else
{
lean_object* v_key_2036_; lean_object* v_value_2037_; lean_object* v_tail_2038_; uint8_t v___y_2040_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; lean_object* v_fst_2045_; lean_object* v_snd_2046_; uint8_t v___x_2047_; 
v_key_2036_ = lean_ctor_get(v_x_2034_, 0);
v_value_2037_ = lean_ctor_get(v_x_2034_, 1);
v_tail_2038_ = lean_ctor_get(v_x_2034_, 2);
v_fst_2043_ = lean_ctor_get(v_key_2036_, 0);
v_snd_2044_ = lean_ctor_get(v_key_2036_, 1);
v_fst_2045_ = lean_ctor_get(v_a_2033_, 0);
v_snd_2046_ = lean_ctor_get(v_a_2033_, 1);
v___x_2047_ = lean_expr_eqv(v_fst_2043_, v_fst_2045_);
if (v___x_2047_ == 0)
{
v___y_2040_ = v___x_2047_;
goto v___jp_2039_;
}
else
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_expr_eqv(v_snd_2044_, v_snd_2046_);
v___y_2040_ = v___x_2048_;
goto v___jp_2039_;
}
v___jp_2039_:
{
if (v___y_2040_ == 0)
{
v_x_2034_ = v_tail_2038_;
goto _start;
}
else
{
lean_object* v___x_2042_; 
lean_inc(v_value_2037_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_value_2037_);
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2049_, lean_object* v_x_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2049_, v_x_2050_);
lean_dec(v_x_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_buckets_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v_fold_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; size_t v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_buckets_2054_ = lean_ctor_get(v_m_2052_, 1);
v_fst_2055_ = lean_ctor_get(v_a_2053_, 0);
v_snd_2056_ = lean_ctor_get(v_a_2053_, 1);
v___x_2057_ = lean_array_get_size(v_buckets_2054_);
v___x_2058_ = l_Lean_Expr_hash(v_fst_2055_);
v___x_2059_ = l_Lean_Expr_hash(v_snd_2056_);
v___x_2060_ = lean_uint64_mix_hash(v___x_2058_, v___x_2059_);
v___x_2061_ = 32ULL;
v___x_2062_ = lean_uint64_shift_right(v___x_2060_, v___x_2061_);
v_fold_2063_ = lean_uint64_xor(v___x_2060_, v___x_2062_);
v___x_2064_ = 16ULL;
v___x_2065_ = lean_uint64_shift_right(v_fold_2063_, v___x_2064_);
v___x_2066_ = lean_uint64_xor(v_fold_2063_, v___x_2065_);
v___x_2067_ = lean_uint64_to_usize(v___x_2066_);
v___x_2068_ = lean_usize_of_nat(v___x_2057_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_sub(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_usize_land(v___x_2067_, v___x_2070_);
v___x_2072_ = lean_array_uget_borrowed(v_buckets_2054_, v___x_2071_);
v___x_2073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2053_, v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2074_, v_a_2075_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_m_2074_);
return v_res_2076_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___f_2078_; 
v___x_2077_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2078_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2078_, 0, v___x_2077_);
return v___f_2078_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1));
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2084_ = l_Lean_Name_append(v___x_2083_, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__3));
v___x_2087_ = l_Lean_stringToMessageData(v___x_2086_);
return v___x_2087_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__5));
v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__7));
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__9));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__11));
v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
return v___x_2099_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__13));
v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* v___y_2103_, lean_object* v_eq_2104_, lean_object* v_a_2105_, lean_object* v_b_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_snd_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2251_; 
v_snd_2119_ = lean_ctor_get(v_b_2107_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_b_2107_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; 
v_unused_2252_ = lean_ctor_get(v_b_2107_, 0);
lean_dec(v_unused_2252_);
v___x_2121_ = v_b_2107_;
v_isShared_2122_ = v_isSharedCheck_2251_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_snd_2119_);
lean_dec(v_b_2107_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2251_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_snd_2123_; lean_object* v_fst_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2250_; 
v_snd_2123_ = lean_ctor_get(v_snd_2119_, 1);
v_fst_2124_ = lean_ctor_get(v_snd_2119_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_snd_2119_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2126_ = v_snd_2119_;
v_isShared_2127_ = v_isSharedCheck_2250_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_snd_2123_);
lean_inc(v_fst_2124_);
lean_dec(v_snd_2119_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2250_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; lean_object* v_snd_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2249_; 
v_fst_2128_ = lean_ctor_get(v_snd_2123_, 0);
v_snd_2129_ = lean_ctor_get(v_snd_2123_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_snd_2123_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2131_ = v_snd_2123_;
v_isShared_2132_ = v_isSharedCheck_2249_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snd_2129_);
lean_inc(v_fst_2128_);
lean_dec(v_snd_2123_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2249_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___y_2135_; uint8_t v___x_2148_; uint8_t v___y_2150_; lean_object* v___y_2151_; uint8_t v___y_2160_; uint8_t v___x_2247_; 
v___x_2133_ = lean_box(0);
v___x_2148_ = 1;
v___x_2247_ = l_Lean_Expr_isApp(v_fst_2128_);
if (v___x_2247_ == 0)
{
v___y_2160_ = v___x_2247_;
goto v___jp_2159_;
}
else
{
uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_Expr_isApp(v_snd_2129_);
v___y_2160_ = v___x_2248_;
goto v___jp_2159_;
}
v___jp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2136_ = l_Lean_Expr_appFn_x21(v_fst_2128_);
lean_dec(v_fst_2128_);
v___x_2137_ = l_Lean_Expr_appFn_x21(v_snd_2129_);
lean_dec(v_snd_2129_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v___x_2137_);
lean_ctor_set(v___x_2131_, 0, v___x_2136_);
v___x_2139_ = v___x_2131_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v___x_2139_);
lean_ctor_set(v___x_2126_, 0, v___y_2135_);
v___x_2141_ = v___x_2126_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___y_2135_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2141_);
lean_ctor_set(v___x_2121_, 0, v___x_2133_);
v___x_2143_ = v___x_2121_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
v_b_2107_ = v___x_2143_;
goto _start;
}
}
}
}
v___jp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = lean_unsigned_to_nat(2u);
v___x_2153_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1, v___y_2150_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1 + 1, v___x_2148_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_fst_2128_);
lean_ctor_set(v___x_2155_, 1, v_snd_2129_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2151_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
v___jp_2159_:
{
if (v___y_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2126_);
lean_del_object(v___x_2121_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
lean_dec(v___y_2103_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v___x_2162_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___y_2160_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1 + 1, v___y_2160_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_fst_2128_);
lean_ctor_set(v___x_2164_, 1, v_snd_2129_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_fst_2124_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2163_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; uint8_t v___x_2171_; 
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_sub(v_fst_2124_, v___x_2168_);
lean_dec(v_fst_2124_);
v___f_2170_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__0);
lean_inc(v___y_2103_);
lean_inc(v___x_2169_);
v___x_2171_ = l_List_elem___redArg(v___f_2170_, v___x_2169_, v___y_2103_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = l_Lean_Expr_appArg_x21(v_fst_2128_);
v___x_2173_ = l_Lean_Expr_appArg_x21(v_snd_2129_);
v___x_2174_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2172_, v___x_2173_, v___y_2108_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; uint8_t v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = lean_unbox(v_a_2175_);
if (v___x_2176_ == 0)
{
lean_object* v_options_2177_; uint8_t v_hasTrace_2178_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2126_);
lean_del_object(v___x_2121_);
lean_dec(v___y_2103_);
v_options_2177_ = lean_ctor_get(v___y_2116_, 2);
v_hasTrace_2178_ = lean_ctor_get_uint8(v_options_2177_, sizeof(void*)*1);
if (v_hasTrace_2178_ == 0)
{
uint8_t v___x_2179_; 
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
v___x_2179_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
v___y_2150_ = v___x_2179_;
v___y_2151_ = v___x_2169_;
goto v___jp_2149_;
}
else
{
lean_object* v_inheritedTraceOptions_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_inheritedTraceOptions_2180_ = lean_ctor_get(v___y_2116_, 13);
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1));
v___x_2182_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2);
v___x_2183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2180_, v_options_2177_, v___x_2182_);
if (v___x_2183_ == 0)
{
uint8_t v___x_2184_; 
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
v___x_2184_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
v___y_2150_ = v___x_2184_;
v___y_2151_ = v___x_2169_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Meta_Grind_updateLastTag(v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v___x_2186_; 
lean_dec_ref(v___x_2185_);
v___x_2186_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2104_, v___y_2108_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
v___x_2188_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__4);
v___x_2189_ = l_Lean_MessageData_ofExpr(v_a_2105_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__6);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_MessageData_ofExpr(v_b_2106_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__8);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_MessageData_ofExpr(v_eq_2104_);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__10);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_Lean_MessageData_ofExpr(v___x_2172_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__12);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_ofExpr(v___x_2173_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__14);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Nat_reprFast(v_a_2187_);
v___x_2210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = l_Lean_MessageData_ofFormat(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2208_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2181_, v___x_2212_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2213_) == 0)
{
uint8_t v___x_2214_; 
lean_dec_ref(v___x_2213_);
v___x_2214_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
v___y_2150_ = v___x_2214_;
v___y_2151_ = v___x_2169_;
goto v___jp_2149_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2175_);
lean_dec(v___x_2169_);
lean_dec(v_snd_2129_);
lean_dec(v_fst_2128_);
v_a_2215_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2213_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2213_);
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
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2175_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec(v___x_2169_);
lean_dec(v_snd_2129_);
lean_dec(v_fst_2128_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
v_a_2223_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2186_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2186_);
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
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2175_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec(v___x_2169_);
lean_dec(v_snd_2129_);
lean_dec(v_fst_2128_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
v_a_2231_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2185_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2185_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2175_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
v___y_2135_ = v___x_2169_;
goto v___jp_2134_;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec(v___x_2169_);
lean_del_object(v___x_2131_);
lean_dec(v_snd_2129_);
lean_dec(v_fst_2128_);
lean_del_object(v___x_2126_);
lean_del_object(v___x_2121_);
lean_dec_ref(v_b_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_eq_2104_);
lean_dec(v___y_2103_);
v_a_2239_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2174_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2174_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
v___y_2135_ = v___x_2169_;
goto v___jp_2134_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object* v___y_2253_, lean_object* v_eq_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_, lean_object* v_b_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2253_, v_eq_2254_, v_a_2255_, v_b_2256_, v_b_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2270_, lean_object* v_b_2271_, lean_object* v_eq_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
uint8_t v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2317_; lean_object* v___x_2353_; 
lean_inc_ref(v_eq_2272_);
v___x_2353_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2272_, v_a_2273_, v_a_2277_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; uint8_t v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
v___x_2355_ = lean_unbox(v_a_2354_);
lean_dec(v_a_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec_ref(v___x_2353_);
lean_inc_ref(v_eq_2272_);
v___x_2356_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2272_, v_a_2273_, v_a_2277_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
v___y_2317_ = v___x_2356_;
goto v___jp_2316_;
}
else
{
v___y_2317_ = v___x_2353_;
goto v___jp_2316_;
}
}
else
{
v___y_2317_ = v___x_2353_;
goto v___jp_2316_;
}
v___jp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2287_ = l_Lean_Expr_getAppNumArgs(v_a_2270_);
v___x_2288_ = lean_box(0);
lean_inc_ref(v_b_2271_);
lean_inc_ref(v_a_2270_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_a_2270_);
lean_ctor_set(v___x_2289_, 1, v_b_2271_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2287_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2286_, v_eq_2272_, v_a_2270_, v_b_2271_, v___x_2291_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2307_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2307_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_a_2293_);
if (lean_obj_tag(v_fst_2297_) == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2298_ = lean_unsigned_to_nat(2u);
v___x_2299_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*1, v___y_2285_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*1 + 1, v___y_2285_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2299_);
v___x_2301_ = v___x_2295_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
else
{
lean_object* v_val_2303_; lean_object* v___x_2305_; 
v_val_2303_ = lean_ctor_get(v_fst_2297_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v_fst_2297_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_val_2303_);
v___x_2305_ = v___x_2295_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_val_2303_);
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
v_a_2308_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2292_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2292_);
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
v___jp_2316_:
{
if (lean_obj_tag(v___y_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2344_; 
v_a_2318_ = lean_ctor_get(v___y_2317_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___y_2317_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2320_ = v___y_2317_;
v_isShared_2321_ = v_isSharedCheck_2344_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___y_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2344_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
uint8_t v___x_2322_; 
v___x_2322_ = lean_unbox(v_a_2318_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v_toGoalState_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2338_; 
lean_del_object(v___x_2320_);
v___x_2323_ = lean_st_ref_get(v_a_2273_);
v_toGoalState_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2323_, 1);
lean_dec(v_unused_2339_);
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_toGoalState_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2338_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_split_2328_; lean_object* v_argPosMap_2329_; lean_object* v___x_2331_; 
v_split_2328_ = lean_ctor_get(v_toGoalState_2324_, 14);
lean_inc_ref(v_split_2328_);
lean_dec_ref(v_toGoalState_2324_);
v_argPosMap_2329_ = lean_ctor_get(v_split_2328_, 6);
lean_inc_ref(v_argPosMap_2329_);
lean_dec_ref(v_split_2328_);
lean_inc_ref(v_b_2271_);
lean_inc_ref(v_a_2270_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 1, v_b_2271_);
lean_ctor_set(v___x_2326_, 0, v_a_2270_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2270_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_b_2271_);
v___x_2331_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2329_, v___x_2331_);
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_argPosMap_2329_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
v___y_2285_ = v___x_2334_;
v___y_2286_ = v___x_2333_;
goto v___jp_2284_;
}
else
{
lean_object* v_val_2335_; uint8_t v___x_2336_; 
v_val_2335_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_val_2335_);
lean_dec_ref(v___x_2332_);
v___x_2336_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
v___y_2285_ = v___x_2336_;
v___y_2286_ = v_val_2335_;
goto v___jp_2284_;
}
}
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
lean_dec(v_a_2318_);
lean_dec_ref(v_eq_2272_);
lean_dec_ref(v_b_2271_);
lean_dec_ref(v_a_2270_);
v___x_2340_ = lean_box(0);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2340_);
v___x_2342_ = v___x_2320_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_eq_2272_);
lean_dec_ref(v_b_2271_);
lean_dec_ref(v_a_2270_);
v_a_2345_ = lean_ctor_get(v___y_2317_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___y_2317_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___y_2317_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___y_2317_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2357_, lean_object* v_b_2358_, lean_object* v_eq_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2357_, v_b_2358_, v_eq_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec(v_a_2360_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2372_, lean_object* v_m_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2373_, v_a_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2376_, lean_object* v_m_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2376_, v_m_2377_, v_a_2378_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_m_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2380_, lean_object* v_a_2381_, lean_object* v_x_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2381_, v_x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_a_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2384_, v_a_2385_, v_x_2386_);
lean_dec(v_x_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
uint8_t v___y_2397_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___x_2422_; 
lean_inc_ref(v_imp_2388_);
v___x_2422_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; uint8_t v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = lean_unbox(v_a_2423_);
lean_dec(v_a_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2439_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2439_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2439_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_unbox(v_a_2426_);
lean_dec(v_a_2426_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_box(1);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = lean_box(0);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2435_);
v___x_2437_ = v___x_2428_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
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
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2425_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2425_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_binderType_2448_; lean_object* v_body_2449_; lean_object* v___y_2451_; lean_object* v___x_2479_; 
v_binderType_2448_ = lean_ctor_get(v_imp_2388_, 1);
lean_inc_ref_n(v_binderType_2448_, 2);
v_body_2449_ = lean_ctor_get(v_imp_2388_, 2);
lean_inc_ref(v_body_2449_);
lean_dec_ref(v_imp_2388_);
v___x_2479_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2448_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; uint8_t v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
v___x_2481_ = lean_unbox(v_a_2480_);
lean_dec(v_a_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_dec_ref(v___x_2479_);
v___x_2482_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2448_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
v___y_2451_ = v___x_2482_;
goto v___jp_2450_;
}
else
{
lean_dec_ref(v_binderType_2448_);
v___y_2451_ = v___x_2479_;
goto v___jp_2450_;
}
}
else
{
lean_dec_ref(v_binderType_2448_);
v___y_2451_ = v___x_2479_;
goto v___jp_2450_;
}
v___jp_2450_:
{
if (lean_obj_tag(v___y_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2470_; 
v_a_2452_ = lean_ctor_get(v___y_2451_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___y_2451_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2454_ = v___y_2451_;
v_isShared_2455_ = v_isSharedCheck_2470_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___y_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2470_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_unbox(v_a_2452_);
if (v___x_2456_ == 0)
{
uint8_t v___x_2457_; 
lean_del_object(v___x_2454_);
v___x_2457_ = l_Lean_Expr_hasLooseBVars(v_body_2449_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_inc_ref(v_body_2449_);
v___x_2458_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2449_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; uint8_t v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
v___x_2460_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
lean_dec_ref(v___x_2458_);
v___x_2461_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2449_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
v___x_2462_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
v___y_2402_ = v___x_2462_;
v___y_2403_ = v___x_2461_;
goto v___jp_2401_;
}
else
{
uint8_t v___x_2463_; 
lean_dec_ref(v_body_2449_);
v___x_2463_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
v___y_2402_ = v___x_2463_;
v___y_2403_ = v___x_2458_;
goto v___jp_2401_;
}
}
else
{
uint8_t v___x_2464_; 
lean_dec_ref(v_body_2449_);
v___x_2464_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
v___y_2402_ = v___x_2464_;
v___y_2403_ = v___x_2458_;
goto v___jp_2401_;
}
}
else
{
uint8_t v___x_2465_; 
lean_dec_ref(v_body_2449_);
v___x_2465_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
v___y_2397_ = v___x_2465_;
goto v___jp_2396_;
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v_a_2452_);
lean_dec_ref(v_body_2449_);
v___x_2466_ = lean_box(0);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2466_);
v___x_2468_ = v___x_2454_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v_body_2449_);
v_a_2471_ = lean_ctor_get(v___y_2451_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___y_2451_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___y_2451_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___y_2451_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v_imp_2388_);
v_a_2483_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2422_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2422_);
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
v___jp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1, v___y_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*1 + 1, v___y_2397_);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
v___jp_2401_:
{
if (lean_obj_tag(v___y_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2413_; 
v_a_2404_ = lean_ctor_get(v___y_2403_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___y_2403_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2406_ = v___y_2403_;
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___y_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_unbox(v_a_2404_);
lean_dec(v_a_2404_);
if (v___x_2408_ == 0)
{
lean_del_object(v___x_2406_);
v___y_2397_ = v___y_2402_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_box(0);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2409_);
v___x_2411_ = v___x_2406_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_a_2414_ = lean_ctor_get(v___y_2403_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___y_2403_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___y_2403_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___y_2403_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2500_, lean_object* v_h_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2500_, v_a_2502_, v_a_2506_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2514_, lean_object* v_h_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2514_, v_h_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_a_2516_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
switch(lean_obj_tag(v_s_2528_))
{
case 0:
{
lean_object* v_e_2540_; lean_object* v___x_2541_; 
v_e_2540_ = lean_ctor_get(v_s_2528_, 0);
lean_inc_ref(v_e_2540_);
lean_dec_ref(v_s_2528_);
v___x_2541_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2540_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2541_;
}
case 1:
{
lean_object* v_e_2542_; lean_object* v___x_2543_; 
v_e_2542_ = lean_ctor_get(v_s_2528_, 0);
lean_inc_ref(v_e_2542_);
lean_dec_ref(v_s_2528_);
v___x_2543_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2542_, v_a_2529_, v_a_2533_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2543_;
}
default: 
{
lean_object* v_a_2544_; lean_object* v_b_2545_; lean_object* v_eq_2546_; lean_object* v___x_2547_; 
v_a_2544_ = lean_ctor_get(v_s_2528_, 0);
lean_inc_ref(v_a_2544_);
v_b_2545_ = lean_ctor_get(v_s_2528_, 1);
lean_inc_ref(v_b_2545_);
v_eq_2546_ = lean_ctor_get(v_s_2528_, 3);
lean_inc_ref(v_eq_2546_);
lean_dec_ref(v_s_2528_);
v___x_2547_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2544_, v_b_2545_, v_eq_2546_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
return v___x_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec(v_a_2549_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2561_){
_start:
{
if (lean_obj_tag(v_x_2561_) == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_unsigned_to_nat(0u);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_unsigned_to_nat(1u);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2564_);
lean_dec(v_x_2564_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2566_, lean_object* v_k_2567_){
_start:
{
if (lean_obj_tag(v_t_2566_) == 0)
{
return v_k_2567_;
}
else
{
lean_object* v_c_2568_; lean_object* v_numCases_2569_; uint8_t v_isRec_2570_; uint8_t v_tryPostpone_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_c_2568_ = lean_ctor_get(v_t_2566_, 0);
lean_inc_ref(v_c_2568_);
v_numCases_2569_ = lean_ctor_get(v_t_2566_, 1);
lean_inc(v_numCases_2569_);
v_isRec_2570_ = lean_ctor_get_uint8(v_t_2566_, sizeof(void*)*2);
v_tryPostpone_2571_ = lean_ctor_get_uint8(v_t_2566_, sizeof(void*)*2 + 1);
lean_dec_ref(v_t_2566_);
v___x_2572_ = lean_box(v_isRec_2570_);
v___x_2573_ = lean_box(v_tryPostpone_2571_);
v___x_2574_ = lean_apply_4(v_k_2567_, v_c_2568_, v_numCases_2569_, v___x_2572_, v___x_2573_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2575_, lean_object* v_ctorIdx_2576_, lean_object* v_t_2577_, lean_object* v_h_2578_, lean_object* v_k_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2577_, v_k_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2581_, lean_object* v_ctorIdx_2582_, lean_object* v_t_2583_, lean_object* v_h_2584_, lean_object* v_k_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2581_, v_ctorIdx_2582_, v_t_2583_, v_h_2584_, v_k_2585_);
lean_dec(v_ctorIdx_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2587_, lean_object* v_none_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2587_, v_none_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2590_, lean_object* v_t_2591_, lean_object* v_h_2592_, lean_object* v_none_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2591_, v_none_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2595_, lean_object* v_some_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2595_, v_some_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2598_, lean_object* v_t_2599_, lean_object* v_h_2600_, lean_object* v_some_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2599_, v_some_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2603_, lean_object* v_as_2604_, size_t v_i_2605_, size_t v_stop_2606_){
_start:
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_usize_dec_eq(v_i_2605_, v_stop_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_array_uget_borrowed(v_as_2604_, v_i_2605_);
v___x_2609_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2608_, v_a_2603_);
if (v___x_2609_ == 0)
{
size_t v___x_2610_; size_t v___x_2611_; 
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_add(v_i_2605_, v___x_2610_);
v_i_2605_ = v___x_2611_;
goto _start;
}
else
{
return v___x_2609_;
}
}
else
{
uint8_t v___x_2613_; 
v___x_2613_ = 0;
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2614_, lean_object* v_as_2615_, lean_object* v_i_2616_, lean_object* v_stop_2617_){
_start:
{
uint64_t v_a_2749__boxed_2618_; size_t v_i_boxed_2619_; size_t v_stop_boxed_2620_; uint8_t v_res_2621_; lean_object* v_r_2622_; 
v_a_2749__boxed_2618_ = lean_unbox_uint64(v_a_2614_);
lean_dec_ref(v_a_2614_);
v_i_boxed_2619_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_stop_boxed_2620_ = lean_unbox_usize(v_stop_2617_);
lean_dec(v_stop_2617_);
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2749__boxed_2618_, v_as_2615_, v_i_boxed_2619_, v_stop_boxed_2620_);
lean_dec_ref(v_as_2615_);
v_r_2622_ = lean_box(v_res_2621_);
return v_r_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2625_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2678_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2678_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2678_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
if (lean_obj_tag(v_a_2635_) == 1)
{
lean_object* v_val_2639_; lean_object* v___x_2640_; 
lean_del_object(v___x_2637_);
v_val_2639_ = lean_ctor_get(v_a_2635_, 0);
lean_inc(v_val_2639_);
lean_dec_ref(v_a_2635_);
v___x_2640_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2664_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2664_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2664_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_array_get_size(v_val_2639_);
v___x_2647_ = lean_nat_dec_lt(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_dec(v_a_2641_);
lean_dec(v_val_2639_);
v___x_2648_ = lean_box(v___x_2647_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2648_);
v___x_2650_ = v___x_2643_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
else
{
if (v___x_2647_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v_a_2641_);
lean_dec(v_val_2639_);
v___x_2652_ = lean_box(v___x_2647_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2652_);
v___x_2654_ = v___x_2643_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; uint64_t v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2646_);
v___x_2658_ = lean_unbox_uint64(v_a_2641_);
lean_dec(v_a_2641_);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2658_, v_val_2639_, v___x_2656_, v___x_2657_);
lean_dec(v_val_2639_);
v___x_2660_ = lean_box(v___x_2659_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2660_);
v___x_2662_ = v___x_2643_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_val_2639_);
v_a_2665_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2640_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2640_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec(v_a_2635_);
v___x_2673_ = 1;
v___x_2674_ = lean_box(v___x_2673_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2674_);
v___x_2676_ = v___x_2637_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2634_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2634_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_c_2687_);
return v_res_2698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2701_ = l_Lean_stringToMessageData(v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2702_, lean_object* v_c_x3f_2703_, lean_object* v_cs_x27_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
if (lean_obj_tag(v_cs_2702_) == 0)
{
lean_object* v___x_2716_; lean_object* v_toGoalState_2717_; lean_object* v_split_2718_; lean_object* v_mvarId_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2827_; 
v___x_2716_ = lean_st_ref_take(v_a_2705_);
v_toGoalState_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc_ref(v_toGoalState_2717_);
v_split_2718_ = lean_ctor_get(v_toGoalState_2717_, 14);
lean_inc_ref(v_split_2718_);
v_mvarId_2719_ = lean_ctor_get(v___x_2716_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; 
v_unused_2828_ = lean_ctor_get(v___x_2716_, 0);
lean_dec(v_unused_2828_);
v___x_2721_ = v___x_2716_;
v_isShared_2722_ = v_isSharedCheck_2827_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_mvarId_2719_);
lean_dec(v___x_2716_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2827_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_nextDeclIdx_2723_; lean_object* v_enodeMap_2724_; lean_object* v_exprs_2725_; lean_object* v_parents_2726_; lean_object* v_congrTable_2727_; lean_object* v_appMap_2728_; lean_object* v_indicesFound_2729_; lean_object* v_newFacts_2730_; uint8_t v_inconsistent_2731_; lean_object* v_nextIdx_2732_; lean_object* v_newRawFacts_2733_; lean_object* v_facts_2734_; lean_object* v_extThms_2735_; lean_object* v_ematch_2736_; lean_object* v_inj_2737_; lean_object* v_clean_2738_; lean_object* v_sstates_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2825_; 
v_nextDeclIdx_2723_ = lean_ctor_get(v_toGoalState_2717_, 0);
v_enodeMap_2724_ = lean_ctor_get(v_toGoalState_2717_, 1);
v_exprs_2725_ = lean_ctor_get(v_toGoalState_2717_, 2);
v_parents_2726_ = lean_ctor_get(v_toGoalState_2717_, 3);
v_congrTable_2727_ = lean_ctor_get(v_toGoalState_2717_, 4);
v_appMap_2728_ = lean_ctor_get(v_toGoalState_2717_, 5);
v_indicesFound_2729_ = lean_ctor_get(v_toGoalState_2717_, 6);
v_newFacts_2730_ = lean_ctor_get(v_toGoalState_2717_, 7);
v_inconsistent_2731_ = lean_ctor_get_uint8(v_toGoalState_2717_, sizeof(void*)*17);
v_nextIdx_2732_ = lean_ctor_get(v_toGoalState_2717_, 8);
v_newRawFacts_2733_ = lean_ctor_get(v_toGoalState_2717_, 9);
v_facts_2734_ = lean_ctor_get(v_toGoalState_2717_, 10);
v_extThms_2735_ = lean_ctor_get(v_toGoalState_2717_, 11);
v_ematch_2736_ = lean_ctor_get(v_toGoalState_2717_, 12);
v_inj_2737_ = lean_ctor_get(v_toGoalState_2717_, 13);
v_clean_2738_ = lean_ctor_get(v_toGoalState_2717_, 15);
v_sstates_2739_ = lean_ctor_get(v_toGoalState_2717_, 16);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_toGoalState_2717_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_toGoalState_2717_, 14);
lean_dec(v_unused_2826_);
v___x_2741_ = v_toGoalState_2717_;
v_isShared_2742_ = v_isSharedCheck_2825_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_sstates_2739_);
lean_inc(v_clean_2738_);
lean_inc(v_inj_2737_);
lean_inc(v_ematch_2736_);
lean_inc(v_extThms_2735_);
lean_inc(v_facts_2734_);
lean_inc(v_newRawFacts_2733_);
lean_inc(v_nextIdx_2732_);
lean_inc(v_newFacts_2730_);
lean_inc(v_indicesFound_2729_);
lean_inc(v_appMap_2728_);
lean_inc(v_congrTable_2727_);
lean_inc(v_parents_2726_);
lean_inc(v_exprs_2725_);
lean_inc(v_enodeMap_2724_);
lean_inc(v_nextDeclIdx_2723_);
lean_dec(v_toGoalState_2717_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2825_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_num_2743_; lean_object* v_added_2744_; lean_object* v_resolved_2745_; lean_object* v_trace_2746_; lean_object* v_lookaheads_2747_; lean_object* v_argPosMap_2748_; lean_object* v_argsAt_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2823_; 
v_num_2743_ = lean_ctor_get(v_split_2718_, 0);
v_added_2744_ = lean_ctor_get(v_split_2718_, 2);
v_resolved_2745_ = lean_ctor_get(v_split_2718_, 3);
v_trace_2746_ = lean_ctor_get(v_split_2718_, 4);
v_lookaheads_2747_ = lean_ctor_get(v_split_2718_, 5);
v_argPosMap_2748_ = lean_ctor_get(v_split_2718_, 6);
v_argsAt_2749_ = lean_ctor_get(v_split_2718_, 7);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_split_2718_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_split_2718_, 1);
lean_dec(v_unused_2824_);
v___x_2751_ = v_split_2718_;
v_isShared_2752_ = v_isSharedCheck_2823_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_argsAt_2749_);
lean_inc(v_argPosMap_2748_);
lean_inc(v_lookaheads_2747_);
lean_inc(v_trace_2746_);
lean_inc(v_resolved_2745_);
lean_inc(v_added_2744_);
lean_inc(v_num_2743_);
lean_dec(v_split_2718_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2823_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = l_List_reverse___redArg(v_cs_x27_2704_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2753_);
v___x_2755_ = v___x_2751_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_num_2743_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_added_2744_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_resolved_2745_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_trace_2746_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_lookaheads_2747_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_argPosMap_2748_);
lean_ctor_set(v_reuseFailAlloc_2822_, 7, v_argsAt_2749_);
v___x_2755_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2757_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 14, v___x_2755_);
v___x_2757_ = v___x_2741_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_nextDeclIdx_2723_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_enodeMap_2724_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_exprs_2725_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_parents_2726_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_congrTable_2727_);
lean_ctor_set(v_reuseFailAlloc_2821_, 5, v_appMap_2728_);
lean_ctor_set(v_reuseFailAlloc_2821_, 6, v_indicesFound_2729_);
lean_ctor_set(v_reuseFailAlloc_2821_, 7, v_newFacts_2730_);
lean_ctor_set(v_reuseFailAlloc_2821_, 8, v_nextIdx_2732_);
lean_ctor_set(v_reuseFailAlloc_2821_, 9, v_newRawFacts_2733_);
lean_ctor_set(v_reuseFailAlloc_2821_, 10, v_facts_2734_);
lean_ctor_set(v_reuseFailAlloc_2821_, 11, v_extThms_2735_);
lean_ctor_set(v_reuseFailAlloc_2821_, 12, v_ematch_2736_);
lean_ctor_set(v_reuseFailAlloc_2821_, 13, v_inj_2737_);
lean_ctor_set(v_reuseFailAlloc_2821_, 14, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2821_, 15, v_clean_2738_);
lean_ctor_set(v_reuseFailAlloc_2821_, 16, v_sstates_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*17, v_inconsistent_2731_);
v___x_2757_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2757_);
v___x_2759_ = v___x_2721_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_mvarId_2719_);
v___x_2759_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_st_ref_set(v_a_2705_, v___x_2759_);
if (lean_obj_tag(v_c_x3f_2703_) == 1)
{
lean_object* v___x_2761_; lean_object* v_toGoalState_2762_; lean_object* v_ematch_2763_; lean_object* v_mvarId_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2817_; 
v___x_2761_ = lean_st_ref_take(v_a_2705_);
v_toGoalState_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc_ref(v_toGoalState_2762_);
v_ematch_2763_ = lean_ctor_get(v_toGoalState_2762_, 12);
lean_inc_ref(v_ematch_2763_);
v_mvarId_2764_ = lean_ctor_get(v___x_2761_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2818_);
v___x_2766_ = v___x_2761_;
v_isShared_2767_ = v_isSharedCheck_2817_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_mvarId_2764_);
lean_dec(v___x_2761_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2817_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_nextDeclIdx_2768_; lean_object* v_enodeMap_2769_; lean_object* v_exprs_2770_; lean_object* v_parents_2771_; lean_object* v_congrTable_2772_; lean_object* v_appMap_2773_; lean_object* v_indicesFound_2774_; lean_object* v_newFacts_2775_; uint8_t v_inconsistent_2776_; lean_object* v_nextIdx_2777_; lean_object* v_newRawFacts_2778_; lean_object* v_facts_2779_; lean_object* v_extThms_2780_; lean_object* v_inj_2781_; lean_object* v_split_2782_; lean_object* v_clean_2783_; lean_object* v_sstates_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2815_; 
v_nextDeclIdx_2768_ = lean_ctor_get(v_toGoalState_2762_, 0);
v_enodeMap_2769_ = lean_ctor_get(v_toGoalState_2762_, 1);
v_exprs_2770_ = lean_ctor_get(v_toGoalState_2762_, 2);
v_parents_2771_ = lean_ctor_get(v_toGoalState_2762_, 3);
v_congrTable_2772_ = lean_ctor_get(v_toGoalState_2762_, 4);
v_appMap_2773_ = lean_ctor_get(v_toGoalState_2762_, 5);
v_indicesFound_2774_ = lean_ctor_get(v_toGoalState_2762_, 6);
v_newFacts_2775_ = lean_ctor_get(v_toGoalState_2762_, 7);
v_inconsistent_2776_ = lean_ctor_get_uint8(v_toGoalState_2762_, sizeof(void*)*17);
v_nextIdx_2777_ = lean_ctor_get(v_toGoalState_2762_, 8);
v_newRawFacts_2778_ = lean_ctor_get(v_toGoalState_2762_, 9);
v_facts_2779_ = lean_ctor_get(v_toGoalState_2762_, 10);
v_extThms_2780_ = lean_ctor_get(v_toGoalState_2762_, 11);
v_inj_2781_ = lean_ctor_get(v_toGoalState_2762_, 13);
v_split_2782_ = lean_ctor_get(v_toGoalState_2762_, 14);
v_clean_2783_ = lean_ctor_get(v_toGoalState_2762_, 15);
v_sstates_2784_ = lean_ctor_get(v_toGoalState_2762_, 16);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_toGoalState_2762_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_toGoalState_2762_, 12);
lean_dec(v_unused_2816_);
v___x_2786_ = v_toGoalState_2762_;
v_isShared_2787_ = v_isSharedCheck_2815_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_sstates_2784_);
lean_inc(v_clean_2783_);
lean_inc(v_split_2782_);
lean_inc(v_inj_2781_);
lean_inc(v_extThms_2780_);
lean_inc(v_facts_2779_);
lean_inc(v_newRawFacts_2778_);
lean_inc(v_nextIdx_2777_);
lean_inc(v_newFacts_2775_);
lean_inc(v_indicesFound_2774_);
lean_inc(v_appMap_2773_);
lean_inc(v_congrTable_2772_);
lean_inc(v_parents_2771_);
lean_inc(v_exprs_2770_);
lean_inc(v_enodeMap_2769_);
lean_inc(v_nextDeclIdx_2768_);
lean_dec(v_toGoalState_2762_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2815_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v_thmMap_2788_; lean_object* v_gmt_2789_; lean_object* v_thms_2790_; lean_object* v_newThms_2791_; lean_object* v_numInstances_2792_; lean_object* v_numDelayedInstances_2793_; lean_object* v_preInstances_2794_; lean_object* v_nextThmIdx_2795_; lean_object* v_matchEqNames_2796_; lean_object* v_delayedThmInsts_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2813_; 
v_thmMap_2788_ = lean_ctor_get(v_ematch_2763_, 0);
v_gmt_2789_ = lean_ctor_get(v_ematch_2763_, 1);
v_thms_2790_ = lean_ctor_get(v_ematch_2763_, 2);
v_newThms_2791_ = lean_ctor_get(v_ematch_2763_, 3);
v_numInstances_2792_ = lean_ctor_get(v_ematch_2763_, 4);
v_numDelayedInstances_2793_ = lean_ctor_get(v_ematch_2763_, 5);
v_preInstances_2794_ = lean_ctor_get(v_ematch_2763_, 7);
v_nextThmIdx_2795_ = lean_ctor_get(v_ematch_2763_, 8);
v_matchEqNames_2796_ = lean_ctor_get(v_ematch_2763_, 9);
v_delayedThmInsts_2797_ = lean_ctor_get(v_ematch_2763_, 10);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_ematch_2763_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_ematch_2763_, 6);
lean_dec(v_unused_2814_);
v___x_2799_ = v_ematch_2763_;
v_isShared_2800_ = v_isSharedCheck_2813_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_delayedThmInsts_2797_);
lean_inc(v_matchEqNames_2796_);
lean_inc(v_nextThmIdx_2795_);
lean_inc(v_preInstances_2794_);
lean_inc(v_numDelayedInstances_2793_);
lean_inc(v_numInstances_2792_);
lean_inc(v_newThms_2791_);
lean_inc(v_thms_2790_);
lean_inc(v_gmt_2789_);
lean_inc(v_thmMap_2788_);
lean_dec(v_ematch_2763_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2813_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 6, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_thmMap_2788_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_gmt_2789_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_thms_2790_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_newThms_2791_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_numInstances_2792_);
lean_ctor_set(v_reuseFailAlloc_2812_, 5, v_numDelayedInstances_2793_);
lean_ctor_set(v_reuseFailAlloc_2812_, 6, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2812_, 7, v_preInstances_2794_);
lean_ctor_set(v_reuseFailAlloc_2812_, 8, v_nextThmIdx_2795_);
lean_ctor_set(v_reuseFailAlloc_2812_, 9, v_matchEqNames_2796_);
lean_ctor_set(v_reuseFailAlloc_2812_, 10, v_delayedThmInsts_2797_);
v___x_2803_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2805_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 12, v___x_2803_);
v___x_2805_ = v___x_2786_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_nextDeclIdx_2768_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_enodeMap_2769_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v_exprs_2770_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v_parents_2771_);
lean_ctor_set(v_reuseFailAlloc_2811_, 4, v_congrTable_2772_);
lean_ctor_set(v_reuseFailAlloc_2811_, 5, v_appMap_2773_);
lean_ctor_set(v_reuseFailAlloc_2811_, 6, v_indicesFound_2774_);
lean_ctor_set(v_reuseFailAlloc_2811_, 7, v_newFacts_2775_);
lean_ctor_set(v_reuseFailAlloc_2811_, 8, v_nextIdx_2777_);
lean_ctor_set(v_reuseFailAlloc_2811_, 9, v_newRawFacts_2778_);
lean_ctor_set(v_reuseFailAlloc_2811_, 10, v_facts_2779_);
lean_ctor_set(v_reuseFailAlloc_2811_, 11, v_extThms_2780_);
lean_ctor_set(v_reuseFailAlloc_2811_, 12, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2811_, 13, v_inj_2781_);
lean_ctor_set(v_reuseFailAlloc_2811_, 14, v_split_2782_);
lean_ctor_set(v_reuseFailAlloc_2811_, 15, v_clean_2783_);
lean_ctor_set(v_reuseFailAlloc_2811_, 16, v_sstates_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2811_, sizeof(void*)*17, v_inconsistent_2776_);
v___x_2805_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2807_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2805_);
v___x_2807_ = v___x_2766_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2805_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_mvarId_2764_);
v___x_2807_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_st_ref_set(v_a_2705_, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_c_x3f_2703_);
return v___x_2809_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_c_x3f_2703_);
return v___x_2819_;
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
lean_object* v_head_2829_; lean_object* v_tail_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_3050_; 
v_head_2829_ = lean_ctor_get(v_cs_2702_, 0);
v_tail_2830_ = lean_ctor_get(v_cs_2702_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_cs_2702_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_2832_ = v_cs_2702_;
v_isShared_2833_ = v_isSharedCheck_3050_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_tail_2830_);
lean_inc(v_head_2829_);
lean_dec(v_cs_2702_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_3050_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2850_; lean_object* v___y_2851_; uint8_t v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2868_; lean_object* v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2906_; lean_object* v___y_2907_; uint8_t v___y_2908_; lean_object* v___y_2909_; uint8_t v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2940_; lean_object* v___y_2944_; lean_object* v___y_2945_; uint8_t v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; uint8_t v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; uint8_t v___y_2957_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_3010_; 
v___x_3010_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2829_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
lean_del_object(v___x_2832_);
lean_dec(v_head_2829_);
v_cs_2702_ = v_tail_2830_;
goto _start;
}
else
{
lean_object* v_options_3014_; uint8_t v_hasTrace_3015_; 
v_options_3014_ = lean_ctor_get(v_a_2713_, 2);
v_hasTrace_3015_ = lean_ctor_get_uint8(v_options_3014_, sizeof(void*)*1);
if (v_hasTrace_3015_ == 0)
{
v___y_2968_ = v_a_2705_;
v___y_2969_ = v_a_2706_;
v___y_2970_ = v_a_2707_;
v___y_2971_ = v_a_2708_;
v___y_2972_ = v_a_2709_;
v___y_2973_ = v_a_2710_;
v___y_2974_ = v_a_2711_;
v___y_2975_ = v_a_2712_;
v___y_2976_ = v_a_2713_;
v___y_2977_ = v_a_2714_;
goto v___jp_2967_;
}
else
{
lean_object* v_inheritedTraceOptions_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_inheritedTraceOptions_3016_ = lean_ctor_get(v_a_2713_, 13);
v___x_3017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3016_, v_options_3014_, v___x_3018_);
if (v___x_3019_ == 0)
{
v___y_2968_ = v_a_2705_;
v___y_2969_ = v_a_2706_;
v___y_2970_ = v_a_2707_;
v___y_2971_ = v_a_2708_;
v___y_2972_ = v_a_2709_;
v___y_2973_ = v_a_2710_;
v___y_2974_ = v_a_2711_;
v___y_2975_ = v_a_2712_;
v___y_2976_ = v_a_2713_;
v___y_2977_ = v_a_2714_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Meta_Grind_updateLastTag(v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_dec_ref(v___x_3020_);
v___x_3021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3022_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2829_);
v___x_3023_ = l_Lean_MessageData_ofExpr(v___x_3022_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3021_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3017_, v___x_3024_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_dec_ref(v___x_3025_);
v___y_2968_ = v_a_2705_;
v___y_2969_ = v_a_2706_;
v___y_2970_ = v_a_2707_;
v___y_2971_ = v_a_2708_;
v___y_2972_ = v_a_2709_;
v___y_2973_ = v_a_2710_;
v___y_2974_ = v_a_2711_;
v___y_2975_ = v_a_2712_;
v___y_2976_ = v_a_2713_;
v___y_2977_ = v_a_2714_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_3034_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3020_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3020_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_3042_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3010_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3010_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
v___jp_2834_:
{
lean_object* v___x_2846_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 1, v_cs_x27_2704_);
v___x_2846_ = v___x_2832_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_head_2829_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_cs_x27_2704_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v_cs_2702_ = v_tail_2830_;
v_cs_x27_2704_ = v___x_2846_;
v_a_2705_ = v___y_2842_;
v_a_2706_ = v___y_2841_;
v_a_2707_ = v___y_2844_;
v_a_2708_ = v___y_2838_;
v_a_2709_ = v___y_2839_;
v_a_2710_ = v___y_2835_;
v_a_2711_ = v___y_2836_;
v_a_2712_ = v___y_2840_;
v_a_2713_ = v___y_2843_;
v_a_2714_ = v___y_2837_;
goto _start;
}
}
v___jp_2849_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2864_, 0, v_head_2829_);
lean_ctor_set(v___x_2864_, 1, v___y_2854_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*2, v___y_2852_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*2 + 1, v___y_2855_);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___y_2859_);
lean_ctor_set(v___x_2865_, 1, v_cs_x27_2704_);
v_cs_2702_ = v_tail_2830_;
v_c_x3f_2703_ = v___x_2864_;
v_cs_x27_2704_ = v___x_2865_;
v_a_2705_ = v___y_2856_;
v_a_2706_ = v___y_2853_;
v_a_2707_ = v___y_2857_;
v_a_2708_ = v___y_2850_;
v_a_2709_ = v___y_2851_;
v_a_2710_ = v___y_2860_;
v_a_2711_ = v___y_2861_;
v_a_2712_ = v___y_2863_;
v_a_2713_ = v___y_2858_;
v_a_2714_ = v___y_2862_;
goto _start;
}
v___jp_2867_:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2829_, v___y_2873_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_2877_, v___y_2873_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; uint8_t v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = lean_nat_dec_lt(v_a_2884_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec(v_a_2884_);
if (v___x_2887_ == 0)
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_nat_dec_lt(v___y_2874_, v___y_2880_);
lean_dec(v___y_2880_);
if (v___x_2888_ == 0)
{
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2874_);
v___y_2835_ = v___y_2878_;
v___y_2836_ = v___y_2879_;
v___y_2837_ = v___y_2881_;
v___y_2838_ = v___y_2868_;
v___y_2839_ = v___y_2869_;
v___y_2840_ = v___y_2882_;
v___y_2841_ = v___y_2871_;
v___y_2842_ = v___y_2873_;
v___y_2843_ = v___y_2876_;
v___y_2844_ = v___y_2875_;
goto v___jp_2834_;
}
else
{
lean_del_object(v___x_2832_);
lean_dec(v_c_x3f_2703_);
v___y_2850_ = v___y_2868_;
v___y_2851_ = v___y_2869_;
v___y_2852_ = v___y_2870_;
v___y_2853_ = v___y_2871_;
v___y_2854_ = v___y_2874_;
v___y_2855_ = v___y_2872_;
v___y_2856_ = v___y_2873_;
v___y_2857_ = v___y_2875_;
v___y_2858_ = v___y_2876_;
v___y_2859_ = v___y_2877_;
v___y_2860_ = v___y_2878_;
v___y_2861_ = v___y_2879_;
v___y_2862_ = v___y_2881_;
v___y_2863_ = v___y_2882_;
goto v___jp_2849_;
}
}
else
{
lean_dec(v___y_2880_);
lean_del_object(v___x_2832_);
lean_dec(v_c_x3f_2703_);
v___y_2850_ = v___y_2868_;
v___y_2851_ = v___y_2869_;
v___y_2852_ = v___y_2870_;
v___y_2853_ = v___y_2871_;
v___y_2854_ = v___y_2874_;
v___y_2855_ = v___y_2872_;
v___y_2856_ = v___y_2873_;
v___y_2857_ = v___y_2875_;
v___y_2858_ = v___y_2876_;
v___y_2859_ = v___y_2877_;
v___y_2860_ = v___y_2878_;
v___y_2861_ = v___y_2879_;
v___y_2862_ = v___y_2881_;
v___y_2863_ = v___y_2882_;
goto v___jp_2849_;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_a_2884_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2874_);
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_2889_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2885_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2885_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2874_);
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_2897_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2883_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2883_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
v___jp_2905_:
{
if (v___y_2921_ == 0)
{
v___y_2868_ = v___y_2906_;
v___y_2869_ = v___y_2907_;
v___y_2870_ = v___y_2908_;
v___y_2871_ = v___y_2909_;
v___y_2872_ = v___y_2910_;
v___y_2873_ = v___y_2911_;
v___y_2874_ = v___y_2912_;
v___y_2875_ = v___y_2913_;
v___y_2876_ = v___y_2914_;
v___y_2877_ = v___y_2915_;
v___y_2878_ = v___y_2916_;
v___y_2879_ = v___y_2917_;
v___y_2880_ = v___y_2918_;
v___y_2881_ = v___y_2919_;
v___y_2882_ = v___y_2920_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_dec_lt(v___x_2922_, v___y_2918_);
if (v___x_2923_ == 0)
{
v___y_2868_ = v___y_2906_;
v___y_2869_ = v___y_2907_;
v___y_2870_ = v___y_2908_;
v___y_2871_ = v___y_2909_;
v___y_2872_ = v___y_2910_;
v___y_2873_ = v___y_2911_;
v___y_2874_ = v___y_2912_;
v___y_2875_ = v___y_2913_;
v___y_2876_ = v___y_2914_;
v___y_2877_ = v___y_2915_;
v___y_2878_ = v___y_2916_;
v___y_2879_ = v___y_2917_;
v___y_2880_ = v___y_2918_;
v___y_2881_ = v___y_2919_;
v___y_2882_ = v___y_2920_;
goto v___jp_2867_;
}
else
{
lean_dec(v___y_2918_);
lean_del_object(v___x_2832_);
lean_dec(v_c_x3f_2703_);
v___y_2850_ = v___y_2906_;
v___y_2851_ = v___y_2907_;
v___y_2852_ = v___y_2908_;
v___y_2853_ = v___y_2909_;
v___y_2854_ = v___y_2912_;
v___y_2855_ = v___y_2910_;
v___y_2856_ = v___y_2911_;
v___y_2857_ = v___y_2913_;
v___y_2858_ = v___y_2914_;
v___y_2859_ = v___y_2915_;
v___y_2860_ = v___y_2916_;
v___y_2861_ = v___y_2917_;
v___y_2862_ = v___y_2919_;
v___y_2863_ = v___y_2920_;
goto v___jp_2849_;
}
}
}
v___jp_2924_:
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_dec_eq(v___y_2929_, v___x_2941_);
if (v___x_2942_ == 0)
{
v___y_2906_ = v___y_2925_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___y_2927_;
v___y_2909_ = v___y_2928_;
v___y_2910_ = v___y_2930_;
v___y_2911_ = v___y_2931_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2932_;
v___y_2914_ = v___y_2933_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
v___y_2919_ = v___y_2938_;
v___y_2920_ = v___y_2939_;
v___y_2921_ = v___x_2942_;
goto v___jp_2905_;
}
else
{
if (v___y_2927_ == 0)
{
v___y_2906_ = v___y_2925_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___y_2927_;
v___y_2909_ = v___y_2928_;
v___y_2910_ = v___y_2930_;
v___y_2911_ = v___y_2931_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2932_;
v___y_2914_ = v___y_2933_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
v___y_2919_ = v___y_2938_;
v___y_2920_ = v___y_2939_;
v___y_2921_ = v___x_2942_;
goto v___jp_2905_;
}
else
{
v___y_2906_ = v___y_2925_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___y_2927_;
v___y_2909_ = v___y_2928_;
v___y_2910_ = v___y_2930_;
v___y_2911_ = v___y_2931_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2932_;
v___y_2914_ = v___y_2933_;
v___y_2915_ = v___y_2934_;
v___y_2916_ = v___y_2935_;
v___y_2917_ = v___y_2936_;
v___y_2918_ = v___y_2937_;
v___y_2919_ = v___y_2938_;
v___y_2920_ = v___y_2939_;
v___y_2921_ = v___y_2940_;
goto v___jp_2905_;
}
}
}
v___jp_2943_:
{
if (lean_obj_tag(v_c_x3f_2703_) == 0)
{
lean_object* v___x_2958_; 
lean_del_object(v___x_2832_);
v___x_2958_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2958_, 0, v_head_2829_);
lean_ctor_set(v___x_2958_, 1, v___y_2948_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*2, v___y_2946_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*2 + 1, v___y_2949_);
v_cs_2702_ = v_tail_2830_;
v_c_x3f_2703_ = v___x_2958_;
v_a_2705_ = v___y_2950_;
v_a_2706_ = v___y_2947_;
v_a_2707_ = v___y_2951_;
v_a_2708_ = v___y_2944_;
v_a_2709_ = v___y_2945_;
v_a_2710_ = v___y_2953_;
v_a_2711_ = v___y_2954_;
v_a_2712_ = v___y_2956_;
v_a_2713_ = v___y_2952_;
v_a_2714_ = v___y_2955_;
goto _start;
}
else
{
uint8_t v_tryPostpone_2960_; 
v_tryPostpone_2960_ = lean_ctor_get_uint8(v_c_x3f_2703_, sizeof(void*)*2 + 1);
if (v_tryPostpone_2960_ == 0)
{
if (v___y_2949_ == 0)
{
lean_object* v_c_2961_; lean_object* v_numCases_2962_; 
v_c_2961_ = lean_ctor_get(v_c_x3f_2703_, 0);
v_numCases_2962_ = lean_ctor_get(v_c_x3f_2703_, 1);
lean_inc(v_numCases_2962_);
lean_inc_ref(v_c_2961_);
v___y_2925_ = v___y_2944_;
v___y_2926_ = v___y_2945_;
v___y_2927_ = v___y_2946_;
v___y_2928_ = v___y_2947_;
v___y_2929_ = v___y_2948_;
v___y_2930_ = v___y_2949_;
v___y_2931_ = v___y_2950_;
v___y_2932_ = v___y_2951_;
v___y_2933_ = v___y_2952_;
v___y_2934_ = v_c_2961_;
v___y_2935_ = v___y_2953_;
v___y_2936_ = v___y_2954_;
v___y_2937_ = v_numCases_2962_;
v___y_2938_ = v___y_2955_;
v___y_2939_ = v___y_2956_;
v___y_2940_ = v___y_2949_;
goto v___jp_2924_;
}
else
{
lean_dec(v___y_2948_);
v___y_2835_ = v___y_2953_;
v___y_2836_ = v___y_2954_;
v___y_2837_ = v___y_2955_;
v___y_2838_ = v___y_2944_;
v___y_2839_ = v___y_2945_;
v___y_2840_ = v___y_2956_;
v___y_2841_ = v___y_2947_;
v___y_2842_ = v___y_2950_;
v___y_2843_ = v___y_2952_;
v___y_2844_ = v___y_2951_;
goto v___jp_2834_;
}
}
else
{
if (v___y_2949_ == 0)
{
lean_object* v_c_2963_; 
lean_del_object(v___x_2832_);
v_c_2963_ = lean_ctor_get(v_c_x3f_2703_, 0);
lean_inc_ref(v_c_2963_);
lean_dec_ref(v_c_x3f_2703_);
v___y_2850_ = v___y_2944_;
v___y_2851_ = v___y_2945_;
v___y_2852_ = v___y_2946_;
v___y_2853_ = v___y_2947_;
v___y_2854_ = v___y_2948_;
v___y_2855_ = v___y_2949_;
v___y_2856_ = v___y_2950_;
v___y_2857_ = v___y_2951_;
v___y_2858_ = v___y_2952_;
v___y_2859_ = v_c_2963_;
v___y_2860_ = v___y_2953_;
v___y_2861_ = v___y_2954_;
v___y_2862_ = v___y_2955_;
v___y_2863_ = v___y_2956_;
goto v___jp_2849_;
}
else
{
if (v___y_2957_ == 0)
{
lean_object* v_c_2964_; lean_object* v_numCases_2965_; 
v_c_2964_ = lean_ctor_get(v_c_x3f_2703_, 0);
v_numCases_2965_ = lean_ctor_get(v_c_x3f_2703_, 1);
lean_inc(v_numCases_2965_);
lean_inc_ref(v_c_2964_);
v___y_2925_ = v___y_2944_;
v___y_2926_ = v___y_2945_;
v___y_2927_ = v___y_2946_;
v___y_2928_ = v___y_2947_;
v___y_2929_ = v___y_2948_;
v___y_2930_ = v___y_2949_;
v___y_2931_ = v___y_2950_;
v___y_2932_ = v___y_2951_;
v___y_2933_ = v___y_2952_;
v___y_2934_ = v_c_2964_;
v___y_2935_ = v___y_2953_;
v___y_2936_ = v___y_2954_;
v___y_2937_ = v_numCases_2965_;
v___y_2938_ = v___y_2955_;
v___y_2939_ = v___y_2956_;
v___y_2940_ = v___y_2957_;
goto v___jp_2924_;
}
else
{
lean_object* v_c_2966_; 
lean_del_object(v___x_2832_);
v_c_2966_ = lean_ctor_get(v_c_x3f_2703_, 0);
lean_inc_ref(v_c_2966_);
lean_dec_ref(v_c_x3f_2703_);
v___y_2850_ = v___y_2944_;
v___y_2851_ = v___y_2945_;
v___y_2852_ = v___y_2946_;
v___y_2853_ = v___y_2947_;
v___y_2854_ = v___y_2948_;
v___y_2855_ = v___y_2949_;
v___y_2856_ = v___y_2950_;
v___y_2857_ = v___y_2951_;
v___y_2858_ = v___y_2952_;
v___y_2859_ = v_c_2966_;
v___y_2860_ = v___y_2953_;
v___y_2861_ = v___y_2954_;
v___y_2862_ = v___y_2955_;
v___y_2863_ = v___y_2956_;
goto v___jp_2849_;
}
}
}
}
}
v___jp_2967_:
{
lean_object* v___x_2978_; 
lean_inc(v_head_2829_);
v___x_2978_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2829_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref(v___x_2978_);
switch(lean_obj_tag(v_a_2979_))
{
case 0:
{
lean_del_object(v___x_2832_);
lean_dec(v_head_2829_);
v_cs_2702_ = v_tail_2830_;
v_a_2705_ = v___y_2968_;
v_a_2706_ = v___y_2969_;
v_a_2707_ = v___y_2970_;
v_a_2708_ = v___y_2971_;
v_a_2709_ = v___y_2972_;
v_a_2710_ = v___y_2973_;
v_a_2711_ = v___y_2974_;
v_a_2712_ = v___y_2975_;
v_a_2713_ = v___y_2976_;
v_a_2714_ = v___y_2977_;
goto _start;
}
case 1:
{
lean_object* v___x_2981_; 
lean_del_object(v___x_2832_);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_head_2829_);
lean_ctor_set(v___x_2981_, 1, v_cs_x27_2704_);
v_cs_2702_ = v_tail_2830_;
v_cs_x27_2704_ = v___x_2981_;
v_a_2705_ = v___y_2968_;
v_a_2706_ = v___y_2969_;
v_a_2707_ = v___y_2970_;
v_a_2708_ = v___y_2971_;
v_a_2709_ = v___y_2972_;
v_a_2710_ = v___y_2973_;
v_a_2711_ = v___y_2974_;
v_a_2712_ = v___y_2975_;
v_a_2713_ = v___y_2976_;
v_a_2714_ = v___y_2977_;
goto _start;
}
default: 
{
lean_object* v_numCases_2983_; uint8_t v_isRec_2984_; uint8_t v_tryPostpone_2985_; lean_object* v___x_2986_; 
v_numCases_2983_ = lean_ctor_get(v_a_2979_, 0);
lean_inc(v_numCases_2983_);
v_isRec_2984_ = lean_ctor_get_uint8(v_a_2979_, sizeof(void*)*1);
v_tryPostpone_2985_ = lean_ctor_get_uint8(v_a_2979_, sizeof(void*)*1 + 1);
lean_dec_ref(v_a_2979_);
v___x_2986_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_2970_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; uint8_t v___x_2988_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref(v___x_2986_);
v___x_2988_ = lean_unbox(v_a_2987_);
if (v___x_2988_ == 0)
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_unbox(v_a_2987_);
lean_dec(v_a_2987_);
v___y_2944_ = v___y_2971_;
v___y_2945_ = v___y_2972_;
v___y_2946_ = v_isRec_2984_;
v___y_2947_ = v___y_2969_;
v___y_2948_ = v_numCases_2983_;
v___y_2949_ = v_tryPostpone_2985_;
v___y_2950_ = v___y_2968_;
v___y_2951_ = v___y_2970_;
v___y_2952_ = v___y_2976_;
v___y_2953_ = v___y_2973_;
v___y_2954_ = v___y_2974_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2975_;
v___y_2957_ = v___x_2989_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
lean_dec(v_a_2987_);
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_nat_dec_lt(v___x_2990_, v_numCases_2983_);
if (v___x_2991_ == 0)
{
v___y_2944_ = v___y_2971_;
v___y_2945_ = v___y_2972_;
v___y_2946_ = v_isRec_2984_;
v___y_2947_ = v___y_2969_;
v___y_2948_ = v_numCases_2983_;
v___y_2949_ = v_tryPostpone_2985_;
v___y_2950_ = v___y_2968_;
v___y_2951_ = v___y_2970_;
v___y_2952_ = v___y_2976_;
v___y_2953_ = v___y_2973_;
v___y_2954_ = v___y_2974_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2975_;
v___y_2957_ = v___x_2991_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_2992_; 
lean_dec(v_numCases_2983_);
lean_del_object(v___x_2832_);
v___x_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2992_, 0, v_head_2829_);
lean_ctor_set(v___x_2992_, 1, v_cs_x27_2704_);
v_cs_2702_ = v_tail_2830_;
v_cs_x27_2704_ = v___x_2992_;
v_a_2705_ = v___y_2968_;
v_a_2706_ = v___y_2969_;
v_a_2707_ = v___y_2970_;
v_a_2708_ = v___y_2971_;
v_a_2709_ = v___y_2972_;
v_a_2710_ = v___y_2973_;
v_a_2711_ = v___y_2974_;
v_a_2712_ = v___y_2975_;
v_a_2713_ = v___y_2976_;
v_a_2714_ = v___y_2977_;
goto _start;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_numCases_2983_);
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_2994_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2986_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2986_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2832_);
lean_dec(v_tail_2830_);
lean_dec(v_head_2829_);
lean_dec(v_cs_x27_2704_);
lean_dec(v_c_x3f_2703_);
v_a_3002_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2978_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2978_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3051_, lean_object* v_c_x3f_3052_, lean_object* v_cs_x27_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3051_, v_c_x3f_3052_, v_cs_x27_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec(v_a_3054_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3066_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3113_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3113_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3113_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_unbox(v_a_3078_);
lean_dec(v_a_3078_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_del_object(v___x_3080_);
v___x_3083_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3066_, v_a_3068_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3100_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3100_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3100_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_unbox(v_a_3084_);
lean_dec(v_a_3084_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v_toGoalState_3090_; lean_object* v_split_3091_; lean_object* v_candidates_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_del_object(v___x_3086_);
v___x_3089_ = lean_st_ref_get(v_a_3066_);
v_toGoalState_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc_ref(v_toGoalState_3090_);
lean_dec(v___x_3089_);
v_split_3091_ = lean_ctor_get(v_toGoalState_3090_, 14);
lean_inc_ref(v_split_3091_);
lean_dec_ref(v_toGoalState_3090_);
v_candidates_3092_ = lean_ctor_get(v_split_3091_, 1);
lean_inc(v_candidates_3092_);
lean_dec_ref(v_split_3091_);
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_box(0);
v___x_3095_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3092_, v___x_3093_, v___x_3094_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = lean_box(0);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3096_);
v___x_3098_ = v___x_3086_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3083_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3083_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3109_);
v___x_3111_ = v___x_3080_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_a_3114_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3077_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3077_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec(v_a_3122_);
return v_res_3133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_box(0);
v___x_3142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3143_ = l_Lean_mkConst(v___x_3142_, v___x_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3146_ = l_Lean_Expr_app___override(v___x_3145_, v_c_3144_);
return v___x_3146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_box(0);
v___x_3156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3157_ = l_Lean_mkConst(v___x_3156_, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = lean_box(0);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3165_ = l_Lean_mkConst(v___x_3164_, v___x_3163_);
return v___x_3165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3173_ = l_Lean_mkConst(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___x_3233_; 
lean_inc_ref(v_c_3174_);
v___x_3233_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3174_, v_a_3182_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3319_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3319_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3319_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = l_Lean_Expr_cleanupAnnotations(v_a_3234_);
v___x_3252_ = l_Lean_Expr_isApp(v___x_3251_);
if (v___x_3252_ == 0)
{
lean_dec_ref(v___x_3251_);
lean_del_object(v___x_3236_);
v___y_3239_ = v_a_3175_;
v___y_3240_ = v_a_3176_;
v___y_3241_ = v_a_3177_;
v___y_3242_ = v_a_3178_;
v___y_3243_ = v_a_3179_;
v___y_3244_ = v_a_3180_;
v___y_3245_ = v_a_3181_;
v___y_3246_ = v_a_3182_;
v___y_3247_ = v_a_3183_;
v___y_3248_ = v_a_3184_;
goto v___jp_3238_;
}
else
{
lean_object* v_arg_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_arg_3253_ = lean_ctor_get(v___x_3251_, 1);
lean_inc_ref(v_arg_3253_);
v___x_3254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3251_);
v___x_3255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3256_ = l_Lean_Expr_isConstOf(v___x_3254_, v___x_3255_);
if (v___x_3256_ == 0)
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_Expr_isApp(v___x_3254_);
if (v___x_3257_ == 0)
{
lean_dec_ref(v___x_3254_);
lean_dec_ref(v_arg_3253_);
lean_del_object(v___x_3236_);
v___y_3239_ = v_a_3175_;
v___y_3240_ = v_a_3176_;
v___y_3241_ = v_a_3177_;
v___y_3242_ = v_a_3178_;
v___y_3243_ = v_a_3179_;
v___y_3244_ = v_a_3180_;
v___y_3245_ = v_a_3181_;
v___y_3246_ = v_a_3182_;
v___y_3247_ = v_a_3183_;
v___y_3248_ = v_a_3184_;
goto v___jp_3238_;
}
else
{
lean_object* v_arg_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v_arg_3258_ = lean_ctor_get(v___x_3254_, 1);
lean_inc_ref(v_arg_3258_);
v___x_3259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3254_);
v___x_3260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3261_ = l_Lean_Expr_isConstOf(v___x_3259_, v___x_3260_);
if (v___x_3261_ == 0)
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Lean_Expr_isApp(v___x_3259_);
if (v___x_3262_ == 0)
{
lean_dec_ref(v___x_3259_);
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
lean_del_object(v___x_3236_);
v___y_3239_ = v_a_3175_;
v___y_3240_ = v_a_3176_;
v___y_3241_ = v_a_3177_;
v___y_3242_ = v_a_3178_;
v___y_3243_ = v_a_3179_;
v___y_3244_ = v_a_3180_;
v___y_3245_ = v_a_3181_;
v___y_3246_ = v_a_3182_;
v___y_3247_ = v_a_3183_;
v___y_3248_ = v_a_3184_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3259_);
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3265_ = l_Lean_Expr_isConstOf(v___x_3263_, v___x_3264_);
lean_dec_ref(v___x_3263_);
if (v___x_3265_ == 0)
{
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
lean_del_object(v___x_3236_);
v___y_3239_ = v_a_3175_;
v___y_3240_ = v_a_3176_;
v___y_3241_ = v_a_3177_;
v___y_3242_ = v_a_3178_;
v___y_3243_ = v_a_3179_;
v___y_3244_ = v_a_3180_;
v___y_3245_ = v_a_3181_;
v___y_3246_ = v_a_3182_;
v___y_3247_ = v_a_3183_;
v___y_3248_ = v_a_3184_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3266_; 
lean_inc_ref(v_c_3174_);
v___x_3266_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3174_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
v___x_3267_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3174_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3267_);
v___x_3269_ = v___x_3236_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
else
{
lean_object* v___x_3271_; 
lean_del_object(v___x_3236_);
lean_inc_ref(v_c_3174_);
v___x_3271_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3174_, v_a_3175_, v_a_3179_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; uint8_t v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = lean_unbox(v_a_3272_);
lean_dec(v_a_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3284_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3280_ = l_Lean_mkApp3(v___x_3279_, v_arg_3258_, v_arg_3253_, v_a_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3280_);
v___x_3282_ = v___x_3277_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
return v___x_3274_;
}
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3295_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3295_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3295_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3291_ = l_Lean_mkApp3(v___x_3290_, v_arg_3258_, v_arg_3253_, v_a_3286_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3291_);
v___x_3293_ = v___x_3288_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
lean_dec_ref(v_c_3174_);
v_a_3296_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3271_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3271_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v___x_3259_);
lean_del_object(v___x_3236_);
v___x_3304_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3314_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3314_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3314_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3310_ = l_Lean_mkApp3(v___x_3309_, v_arg_3258_, v_arg_3253_, v_a_3305_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3310_);
v___x_3312_ = v___x_3307_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
lean_dec_ref(v_arg_3258_);
lean_dec_ref(v_arg_3253_);
return v___x_3304_;
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_dec_ref(v___x_3254_);
lean_dec_ref(v_c_3174_);
v___x_3315_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3253_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3315_);
v___x_3317_ = v___x_3236_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
v___jp_3238_:
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_Meta_Grind_isIte(v_c_3174_);
if (v___x_3249_ == 0)
{
uint8_t v___x_3250_; 
v___x_3250_ = l_Lean_Meta_Grind_isDIte(v_c_3174_);
v___y_3187_ = v___y_3246_;
v___y_3188_ = v___y_3239_;
v___y_3189_ = v___y_3245_;
v___y_3190_ = v___y_3241_;
v___y_3191_ = v___y_3244_;
v___y_3192_ = v___y_3240_;
v___y_3193_ = v___y_3247_;
v___y_3194_ = v___y_3243_;
v___y_3195_ = v___y_3248_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___x_3250_;
goto v___jp_3186_;
}
else
{
v___y_3187_ = v___y_3246_;
v___y_3188_ = v___y_3239_;
v___y_3189_ = v___y_3245_;
v___y_3190_ = v___y_3241_;
v___y_3191_ = v___y_3244_;
v___y_3192_ = v___y_3240_;
v___y_3193_ = v___y_3247_;
v___y_3194_ = v___y_3243_;
v___y_3195_ = v___y_3248_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___x_3249_;
goto v___jp_3186_;
}
}
}
}
else
{
lean_dec_ref(v_c_3174_);
return v___x_3233_;
}
v___jp_3186_:
{
if (v___y_3197_ == 0)
{
lean_object* v___x_3198_; 
lean_inc_ref(v_c_3174_);
v___x_3198_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3174_, v___y_3188_, v___y_3194_, v___y_3189_, v___y_3187_, v___y_3193_, v___y_3195_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3217_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3217_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3217_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_unbox(v_a_3199_);
lean_dec(v_a_3199_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3205_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_c_3174_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_c_3174_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
else
{
lean_object* v___x_3207_; 
lean_del_object(v___x_3201_);
lean_inc_ref(v_c_3174_);
v___x_3207_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3174_, v___y_3188_, v___y_3192_, v___y_3190_, v___y_3196_, v___y_3194_, v___y_3191_, v___y_3189_, v___y_3187_, v___y_3193_, v___y_3195_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3174_, v_a_3208_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
else
{
lean_dec_ref(v_c_3174_);
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v_c_3174_);
v_a_3218_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3198_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3198_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
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
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3226_ = lean_unsigned_to_nat(1u);
v___x_3227_ = l_Lean_Expr_getAppNumArgs(v_c_3174_);
v___x_3228_ = lean_nat_sub(v___x_3227_, v___x_3226_);
lean_dec(v___x_3227_);
v___x_3229_ = lean_nat_sub(v___x_3228_, v___x_3226_);
lean_dec(v___x_3228_);
v___x_3230_ = l_Lean_Expr_getRevArg_x21(v_c_3174_, v___x_3229_);
lean_dec_ref(v_c_3174_);
v___x_3231_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec(v_a_3321_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3333_, lean_object* v_major_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3335_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; uint8_t v_trace_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref(v___x_3342_);
v_trace_3344_ = lean_ctor_get_uint8(v_a_3343_, sizeof(void*)*11);
lean_dec(v_a_3343_);
if (v_trace_3344_ == 0)
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Meta_Grind_cases(v_mvarId_3333_, v_major_3334_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; 
lean_inc(v_a_3340_);
lean_inc_ref(v_a_3339_);
lean_inc(v_a_3338_);
lean_inc_ref(v_a_3337_);
lean_inc_ref(v_major_3334_);
v___x_3346_ = lean_infer_type(v_major_3334_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = l_Lean_Meta_whnfD(v_a_3347_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Lean_Expr_getAppFn(v_a_3349_);
lean_dec(v_a_3349_);
if (lean_obj_tag(v___x_3350_) == 4)
{
lean_object* v_declName_3351_; lean_object* v___x_3352_; 
v_declName_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_declName_3351_);
lean_dec_ref(v___x_3350_);
v___x_3352_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3351_, v_a_3336_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref(v___x_3352_);
v___x_3353_ = l_Lean_Meta_Grind_cases(v_mvarId_3333_, v_major_3334_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
return v___x_3353_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v_major_3334_);
lean_dec(v_mvarId_3333_);
v_a_3354_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3352_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3352_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v___x_3362_; 
lean_dec_ref(v___x_3350_);
v___x_3362_ = l_Lean_Meta_Grind_cases(v_mvarId_3333_, v_major_3334_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
return v___x_3362_;
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v_major_3334_);
lean_dec(v_mvarId_3333_);
v_a_3363_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3348_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3348_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_major_3334_);
lean_dec(v_mvarId_3333_);
v_a_3371_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3346_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3346_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec_ref(v_major_3334_);
lean_dec(v_mvarId_3333_);
v_a_3379_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3342_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3342_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3387_, lean_object* v_major_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3387_, v_major_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3397_, lean_object* v_major_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3397_, v_major_3398_, v_a_3401_, v_a_3402_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3411_, lean_object* v_major_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3411_, v_major_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec(v_a_3413_);
return v_res_3424_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3425_){
_start:
{
uint64_t v_anchor_3426_; 
v_anchor_3426_ = lean_ctor_get_uint64(v_e_3425_, sizeof(void*)*3);
return v_anchor_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3427_){
_start:
{
uint64_t v_res_3428_; lean_object* v_r_3429_; 
v_res_3428_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3427_);
lean_dec_ref(v_e_3427_);
v_r_3429_ = lean_box_uint64(v_res_3428_);
return v_r_3429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3432_, lean_object* v_x_3433_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 0)
{
uint8_t v___x_3434_; 
v___x_3434_ = 0;
return v___x_3434_;
}
else
{
lean_object* v_key_3435_; lean_object* v_tail_3436_; uint64_t v___x_3437_; uint8_t v___x_3438_; 
v_key_3435_ = lean_ctor_get(v_x_3433_, 0);
v_tail_3436_ = lean_ctor_get(v_x_3433_, 2);
v___x_3437_ = lean_unbox_uint64(v_key_3435_);
v___x_3438_ = lean_uint64_dec_eq(v___x_3437_, v_a_3432_);
if (v___x_3438_ == 0)
{
v_x_3433_ = v_tail_3436_;
goto _start;
}
else
{
return v___x_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3440_, lean_object* v_x_3441_){
_start:
{
uint64_t v_a_boxed_3442_; uint8_t v_res_3443_; lean_object* v_r_3444_; 
v_a_boxed_3442_ = lean_unbox_uint64(v_a_3440_);
lean_dec_ref(v_a_3440_);
v_res_3443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3442_, v_x_3441_);
lean_dec(v_x_3441_);
v_r_3444_ = lean_box(v_res_3443_);
return v_r_3444_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3445_, uint64_t v_a_3446_){
_start:
{
lean_object* v_buckets_3447_; lean_object* v___x_3448_; uint64_t v___x_3449_; uint64_t v___x_3450_; uint64_t v_fold_3451_; uint64_t v___x_3452_; uint64_t v___x_3453_; uint64_t v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; size_t v___x_3457_; size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v_buckets_3447_ = lean_ctor_get(v_m_3445_, 1);
v___x_3448_ = lean_array_get_size(v_buckets_3447_);
v___x_3449_ = 32ULL;
v___x_3450_ = lean_uint64_shift_right(v_a_3446_, v___x_3449_);
v_fold_3451_ = lean_uint64_xor(v_a_3446_, v___x_3450_);
v___x_3452_ = 16ULL;
v___x_3453_ = lean_uint64_shift_right(v_fold_3451_, v___x_3452_);
v___x_3454_ = lean_uint64_xor(v_fold_3451_, v___x_3453_);
v___x_3455_ = lean_uint64_to_usize(v___x_3454_);
v___x_3456_ = lean_usize_of_nat(v___x_3448_);
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_sub(v___x_3456_, v___x_3457_);
v___x_3459_ = lean_usize_land(v___x_3455_, v___x_3458_);
v___x_3460_ = lean_array_uget_borrowed(v_buckets_3447_, v___x_3459_);
v___x_3461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3446_, v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3462_, lean_object* v_a_3463_){
_start:
{
uint64_t v_a_boxed_3464_; uint8_t v_res_3465_; lean_object* v_r_3466_; 
v_a_boxed_3464_ = lean_unbox_uint64(v_a_3463_);
lean_dec_ref(v_a_3463_);
v_res_3465_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3462_, v_a_boxed_3464_);
lean_dec_ref(v_m_3462_);
v_r_3466_ = lean_box(v_res_3465_);
return v_r_3466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_x_3467_, lean_object* v_x_3468_){
_start:
{
if (lean_obj_tag(v_x_3468_) == 0)
{
return v_x_3467_;
}
else
{
lean_object* v_key_3469_; lean_object* v_value_3470_; lean_object* v_tail_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3495_; 
v_key_3469_ = lean_ctor_get(v_x_3468_, 0);
v_value_3470_ = lean_ctor_get(v_x_3468_, 1);
v_tail_3471_ = lean_ctor_get(v_x_3468_, 2);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_x_3468_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3473_ = v_x_3468_;
v_isShared_3474_ = v_isSharedCheck_3495_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_tail_3471_);
lean_inc(v_value_3470_);
lean_inc(v_key_3469_);
lean_dec(v_x_3468_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3495_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; uint64_t v___x_3476_; uint64_t v___x_3477_; uint64_t v___x_3478_; uint64_t v___x_3479_; uint64_t v_fold_3480_; uint64_t v___x_3481_; uint64_t v___x_3482_; uint64_t v___x_3483_; size_t v___x_3484_; size_t v___x_3485_; size_t v___x_3486_; size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3475_ = lean_array_get_size(v_x_3467_);
v___x_3476_ = 32ULL;
v___x_3477_ = lean_unbox_uint64(v_key_3469_);
v___x_3478_ = lean_uint64_shift_right(v___x_3477_, v___x_3476_);
v___x_3479_ = lean_unbox_uint64(v_key_3469_);
v_fold_3480_ = lean_uint64_xor(v___x_3479_, v___x_3478_);
v___x_3481_ = 16ULL;
v___x_3482_ = lean_uint64_shift_right(v_fold_3480_, v___x_3481_);
v___x_3483_ = lean_uint64_xor(v_fold_3480_, v___x_3482_);
v___x_3484_ = lean_uint64_to_usize(v___x_3483_);
v___x_3485_ = lean_usize_of_nat(v___x_3475_);
v___x_3486_ = ((size_t)1ULL);
v___x_3487_ = lean_usize_sub(v___x_3485_, v___x_3486_);
v___x_3488_ = lean_usize_land(v___x_3484_, v___x_3487_);
v___x_3489_ = lean_array_uget_borrowed(v_x_3467_, v___x_3488_);
lean_inc(v___x_3489_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 2, v___x_3489_);
v___x_3491_ = v___x_3473_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_key_3469_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_value_3470_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_array_uset(v_x_3467_, v___x_3488_, v___x_3491_);
v_x_3467_ = v___x_3492_;
v_x_3468_ = v_tail_3471_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_i_3496_, lean_object* v_source_3497_, lean_object* v_target_3498_){
_start:
{
lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3499_ = lean_array_get_size(v_source_3497_);
v___x_3500_ = lean_nat_dec_lt(v_i_3496_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_dec_ref(v_source_3497_);
lean_dec(v_i_3496_);
return v_target_3498_;
}
else
{
lean_object* v_es_3501_; lean_object* v___x_3502_; lean_object* v_source_3503_; lean_object* v_target_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_es_3501_ = lean_array_fget(v_source_3497_, v_i_3496_);
v___x_3502_ = lean_box(0);
v_source_3503_ = lean_array_fset(v_source_3497_, v_i_3496_, v___x_3502_);
v_target_3504_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(v_target_3498_, v_es_3501_);
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = lean_nat_add(v_i_3496_, v___x_3505_);
lean_dec(v_i_3496_);
v_i_3496_ = v___x_3506_;
v_source_3497_ = v_source_3503_;
v_target_3498_ = v_target_3504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_data_3508_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v_nbuckets_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3509_ = lean_array_get_size(v_data_3508_);
v___x_3510_ = lean_unsigned_to_nat(2u);
v_nbuckets_3511_ = lean_nat_mul(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_unsigned_to_nat(0u);
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_mk_array(v_nbuckets_3511_, v___x_3513_);
v___x_3515_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v___x_3512_, v_data_3508_, v___x_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3516_, uint64_t v_a_3517_, lean_object* v_b_3518_){
_start:
{
lean_object* v_size_3519_; lean_object* v_buckets_3520_; lean_object* v___x_3521_; uint64_t v___x_3522_; uint64_t v___x_3523_; uint64_t v_fold_3524_; uint64_t v___x_3525_; uint64_t v___x_3526_; uint64_t v___x_3527_; size_t v___x_3528_; size_t v___x_3529_; size_t v___x_3530_; size_t v___x_3531_; size_t v___x_3532_; lean_object* v_bkt_3533_; uint8_t v___x_3534_; 
v_size_3519_ = lean_ctor_get(v_m_3516_, 0);
v_buckets_3520_ = lean_ctor_get(v_m_3516_, 1);
v___x_3521_ = lean_array_get_size(v_buckets_3520_);
v___x_3522_ = 32ULL;
v___x_3523_ = lean_uint64_shift_right(v_a_3517_, v___x_3522_);
v_fold_3524_ = lean_uint64_xor(v_a_3517_, v___x_3523_);
v___x_3525_ = 16ULL;
v___x_3526_ = lean_uint64_shift_right(v_fold_3524_, v___x_3525_);
v___x_3527_ = lean_uint64_xor(v_fold_3524_, v___x_3526_);
v___x_3528_ = lean_uint64_to_usize(v___x_3527_);
v___x_3529_ = lean_usize_of_nat(v___x_3521_);
v___x_3530_ = ((size_t)1ULL);
v___x_3531_ = lean_usize_sub(v___x_3529_, v___x_3530_);
v___x_3532_ = lean_usize_land(v___x_3528_, v___x_3531_);
v_bkt_3533_ = lean_array_uget_borrowed(v_buckets_3520_, v___x_3532_);
v___x_3534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3517_, v_bkt_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3556_; 
lean_inc_ref(v_buckets_3520_);
lean_inc(v_size_3519_);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_m_3516_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; lean_object* v_unused_3558_; 
v_unused_3557_ = lean_ctor_get(v_m_3516_, 1);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_m_3516_, 0);
lean_dec(v_unused_3558_);
v___x_3536_ = v_m_3516_;
v_isShared_3537_ = v_isSharedCheck_3556_;
goto v_resetjp_3535_;
}
else
{
lean_dec(v_m_3516_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3556_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v_size_x27_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v_buckets_x27_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3538_ = lean_unsigned_to_nat(1u);
v_size_x27_3539_ = lean_nat_add(v_size_3519_, v___x_3538_);
lean_dec(v_size_3519_);
v___x_3540_ = lean_box_uint64(v_a_3517_);
lean_inc(v_bkt_3533_);
v___x_3541_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v_b_3518_);
lean_ctor_set(v___x_3541_, 2, v_bkt_3533_);
v_buckets_x27_3542_ = lean_array_uset(v_buckets_3520_, v___x_3532_, v___x_3541_);
v___x_3543_ = lean_unsigned_to_nat(4u);
v___x_3544_ = lean_nat_mul(v_size_x27_3539_, v___x_3543_);
v___x_3545_ = lean_unsigned_to_nat(3u);
v___x_3546_ = lean_nat_div(v___x_3544_, v___x_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_array_get_size(v_buckets_x27_3542_);
v___x_3548_ = lean_nat_dec_le(v___x_3546_, v___x_3547_);
lean_dec(v___x_3546_);
if (v___x_3548_ == 0)
{
lean_object* v_val_3549_; lean_object* v___x_3551_; 
v_val_3549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_buckets_x27_3542_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v_val_3549_);
lean_ctor_set(v___x_3536_, 0, v_size_x27_3539_);
v___x_3551_ = v___x_3536_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_size_x27_3539_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_val_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
else
{
lean_object* v___x_3554_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 1, v_buckets_x27_3542_);
lean_ctor_set(v___x_3536_, 0, v_size_x27_3539_);
v___x_3554_ = v___x_3536_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_size_x27_3539_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_buckets_x27_3542_);
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
lean_dec(v_b_3518_);
return v_m_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3559_, lean_object* v_a_3560_, lean_object* v_b_3561_){
_start:
{
uint64_t v_a_boxed_3562_; lean_object* v_res_3563_; 
v_a_boxed_3562_ = lean_unbox_uint64(v_a_3560_);
lean_dec_ref(v_a_3560_);
v_res_3563_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3559_, v_a_boxed_3562_, v_b_3561_);
return v_res_3563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_unsigned_to_nat(16u);
v___x_3566_ = lean_mk_array(v___x_3565_, v___x_3564_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v_found_3569_; 
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3568_ = lean_unsigned_to_nat(0u);
v_found_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3569_, 0, v___x_3568_);
lean_ctor_set(v_found_3569_, 1, v___x_3567_);
return v_found_3569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v_found_3570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v_found_3570_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3573_, lean_object* v_numDigits_3574_, lean_object* v_es_3575_, lean_object* v_as_3576_, size_t v_sz_3577_, size_t v_i_3578_, lean_object* v_b_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_usize_dec_lt(v_i_3578_, v_sz_3577_);
if (v___x_3580_ == 0)
{
return v_b_3579_;
}
else
{
lean_object* v_snd_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3606_; 
v_snd_3581_ = lean_ctor_get(v_b_3579_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_b_3579_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v_b_3579_, 0);
lean_dec(v_unused_3607_);
v___x_3583_ = v_b_3579_;
v_isShared_3584_ = v_isSharedCheck_3606_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_snd_3581_);
lean_dec(v_b_3579_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3606_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v_a_3585_; uint64_t v_anchor_3586_; uint64_t v___x_3587_; uint64_t v___x_3588_; uint8_t v___x_3589_; 
v_a_3585_ = lean_array_uget_borrowed(v_as_3576_, v_i_3578_);
v_anchor_3586_ = lean_ctor_get_uint64(v_a_3585_, sizeof(void*)*3);
v___x_3587_ = lean_uint64_of_nat(v_shift_3573_);
v___x_3588_ = lean_uint64_shift_right(v_anchor_3586_, v___x_3587_);
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3581_, v___x_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3590_ = lean_box(0);
v___x_3591_ = lean_box(0);
v___x_3592_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3581_, v___x_3588_, v___x_3591_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 1, v___x_3592_);
lean_ctor_set(v___x_3583_, 0, v___x_3590_);
v___x_3594_ = v___x_3583_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
size_t v___x_3595_; size_t v___x_3596_; 
v___x_3595_ = ((size_t)1ULL);
v___x_3596_ = lean_usize_add(v_i_3578_, v___x_3595_);
v_i_3578_ = v___x_3596_;
v_b_3579_ = v___x_3594_;
goto _start;
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3600_ = lean_nat_add(v_numDigits_3574_, v___x_3599_);
v___x_3601_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3575_, v___x_3600_);
lean_dec(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3602_);
v___x_3604_ = v___x_3583_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_snd_3581_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3608_, lean_object* v_numDigits_3609_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3610_ = lean_unsigned_to_nat(4u);
v___x_3611_ = lean_nat_mul(v___x_3610_, v_numDigits_3609_);
v___x_3612_ = lean_unsigned_to_nat(64u);
v___x_3613_ = lean_nat_dec_lt(v___x_3611_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_dec(v___x_3611_);
lean_inc(v_numDigits_3609_);
return v_numDigits_3609_;
}
else
{
lean_object* v_shift_3614_; lean_object* v___x_3615_; size_t v_sz_3616_; size_t v___x_3617_; lean_object* v___x_3618_; lean_object* v_fst_3619_; 
v_shift_3614_ = lean_nat_sub(v___x_3612_, v___x_3611_);
lean_dec(v___x_3611_);
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3616_ = lean_array_size(v_es_3608_);
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3614_, v_numDigits_3609_, v_es_3608_, v_es_3608_, v_sz_3616_, v___x_3617_, v___x_3615_);
lean_dec(v_shift_3614_);
v_fst_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_fst_3619_);
lean_dec_ref(v___x_3618_);
if (lean_obj_tag(v_fst_3619_) == 0)
{
lean_inc(v_numDigits_3609_);
return v_numDigits_3609_;
}
else
{
lean_object* v_val_3620_; 
v_val_3620_ = lean_ctor_get(v_fst_3619_, 0);
lean_inc(v_val_3620_);
lean_dec_ref(v_fst_3619_);
return v_val_3620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3621_, lean_object* v_numDigits_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3621_, v_numDigits_3622_);
lean_dec(v_numDigits_3622_);
lean_dec_ref(v_es_3621_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3624_, lean_object* v_numDigits_3625_, lean_object* v_es_3626_, lean_object* v_as_3627_, lean_object* v_sz_3628_, lean_object* v_i_3629_, lean_object* v_b_3630_){
_start:
{
size_t v_sz_boxed_3631_; size_t v_i_boxed_3632_; lean_object* v_res_3633_; 
v_sz_boxed_3631_ = lean_unbox_usize(v_sz_3628_);
lean_dec(v_sz_3628_);
v_i_boxed_3632_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3624_, v_numDigits_3625_, v_es_3626_, v_as_3627_, v_sz_boxed_3631_, v_i_boxed_3632_, v_b_3630_);
lean_dec_ref(v_as_3627_);
lean_dec_ref(v_es_3626_);
lean_dec(v_numDigits_3625_);
lean_dec(v_shift_3624_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_unsigned_to_nat(4u);
v___x_3636_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3634_, v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3637_);
lean_dec_ref(v_es_3637_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3639_, lean_object* v_as_3640_, size_t v_i_3641_, size_t v_stop_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_a_3656_; uint8_t v___x_3660_; 
v___x_3660_ = lean_usize_dec_eq(v_i_3641_, v_stop_3642_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_array_uget_borrowed(v_as_3640_, v_i_3641_);
v___x_3662_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3661_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
v___x_3664_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3661_);
lean_inc(v___x_3661_);
v___x_3665_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3661_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v___x_3665_);
if (lean_obj_tag(v_a_3666_) == 2)
{
lean_object* v_numCases_3667_; uint8_t v_isRec_3668_; lean_object* v___x_3669_; 
v_numCases_3667_ = lean_ctor_get(v_a_3666_, 0);
lean_inc(v_numCases_3667_);
v_isRec_3668_ = lean_ctor_get_uint8(v_a_3666_, sizeof(void*)*1);
lean_dec_ref(v_a_3666_);
lean_inc_ref(v_filter_3639_);
lean_inc(v___y_3653_);
lean_inc_ref(v___y_3652_);
lean_inc(v___y_3651_);
lean_inc_ref(v___y_3650_);
lean_inc(v___y_3649_);
lean_inc_ref(v___y_3648_);
lean_inc(v___y_3647_);
lean_inc_ref(v___y_3646_);
lean_inc(v___y_3645_);
lean_inc(v___y_3644_);
lean_inc_ref(v___x_3664_);
v___x_3669_ = lean_apply_12(v_filter_3639_, v___x_3664_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, lean_box(0));
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; uint8_t v___x_3671_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v___x_3671_ = lean_unbox(v_a_3670_);
lean_dec(v_a_3670_);
if (v___x_3671_ == 0)
{
lean_dec(v_numCases_3667_);
lean_dec_ref(v___x_3664_);
lean_dec(v_a_3663_);
v_a_3656_ = v_b_3643_;
goto v___jp_3655_;
}
else
{
lean_object* v___x_3672_; uint64_t v___x_3673_; lean_object* v___x_3674_; 
lean_inc(v___x_3661_);
v___x_3672_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3672_, 0, v___x_3661_);
lean_ctor_set(v___x_3672_, 1, v_numCases_3667_);
lean_ctor_set(v___x_3672_, 2, v___x_3664_);
lean_ctor_set_uint8(v___x_3672_, sizeof(void*)*3 + 8, v_isRec_3668_);
v___x_3673_ = lean_unbox_uint64(v_a_3663_);
lean_dec(v_a_3663_);
lean_ctor_set_uint64(v___x_3672_, sizeof(void*)*3, v___x_3673_);
v___x_3674_ = lean_array_push(v_b_3643_, v___x_3672_);
v_a_3656_ = v___x_3674_;
goto v___jp_3655_;
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_numCases_3667_);
lean_dec_ref(v___x_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_b_3643_);
lean_dec_ref(v_filter_3639_);
v_a_3675_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3669_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3669_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_dec(v_a_3666_);
lean_dec_ref(v___x_3664_);
lean_dec(v_a_3663_);
v_a_3656_ = v_b_3643_;
goto v___jp_3655_;
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v___x_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_b_3643_);
lean_dec_ref(v_filter_3639_);
v_a_3683_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3665_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3665_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
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
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_b_3643_);
lean_dec_ref(v_filter_3639_);
v_a_3691_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3662_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3662_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v___x_3699_; 
lean_dec_ref(v_filter_3639_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v_b_3643_);
return v___x_3699_;
}
v___jp_3655_:
{
size_t v___x_3657_; size_t v___x_3658_; 
v___x_3657_ = ((size_t)1ULL);
v___x_3658_ = lean_usize_add(v_i_3641_, v___x_3657_);
v_i_3641_ = v___x_3658_;
v_b_3643_ = v_a_3656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3700_, lean_object* v_as_3701_, lean_object* v_i_3702_, lean_object* v_stop_3703_, lean_object* v_b_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
size_t v_i_boxed_3716_; size_t v_stop_boxed_3717_; lean_object* v_res_3718_; 
v_i_boxed_3716_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_stop_boxed_3717_ = lean_unbox_usize(v_stop_3703_);
lean_dec(v_stop_3703_);
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3700_, v_as_3701_, v_i_boxed_3716_, v_stop_boxed_3717_, v_b_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v_as_3701_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3721_, lean_object* v_as_3722_, lean_object* v_start_3723_, lean_object* v_stop_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3737_ = lean_nat_dec_lt(v_start_3723_, v_stop_3724_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; 
lean_dec_ref(v_filter_3721_);
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
return v___x_3738_;
}
else
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = lean_array_get_size(v_as_3722_);
v___x_3740_ = lean_nat_dec_le(v_stop_3724_, v___x_3739_);
if (v___x_3740_ == 0)
{
uint8_t v___x_3741_; 
v___x_3741_ = lean_nat_dec_lt(v_start_3723_, v___x_3739_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v_filter_3721_);
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3736_);
return v___x_3742_;
}
else
{
size_t v___x_3743_; size_t v___x_3744_; lean_object* v___x_3745_; 
v___x_3743_ = lean_usize_of_nat(v_start_3723_);
v___x_3744_ = lean_usize_of_nat(v___x_3739_);
v___x_3745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3721_, v_as_3722_, v___x_3743_, v___x_3744_, v___x_3736_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3745_;
}
}
else
{
size_t v___x_3746_; size_t v___x_3747_; lean_object* v___x_3748_; 
v___x_3746_ = lean_usize_of_nat(v_start_3723_);
v___x_3747_ = lean_usize_of_nat(v_stop_3724_);
v___x_3748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3721_, v_as_3722_, v___x_3746_, v___x_3747_, v___x_3736_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3749_, lean_object* v_as_3750_, lean_object* v_start_3751_, lean_object* v_stop_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3749_, v_as_3750_, v_start_3751_, v_stop_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec(v_stop_3752_);
lean_dec(v_start_3751_);
lean_dec_ref(v_as_3750_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v___x_3777_; lean_object* v_toGoalState_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3808_; 
v___x_3777_ = lean_st_ref_get(v_a_3766_);
v_toGoalState_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v___x_3777_, 1);
lean_dec(v_unused_3809_);
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3808_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_toGoalState_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3808_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_split_3782_; lean_object* v_candidates_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_split_3782_ = lean_ctor_get(v_toGoalState_3778_, 14);
lean_inc_ref(v_split_3782_);
lean_dec_ref(v_toGoalState_3778_);
v_candidates_3783_ = lean_ctor_get(v_split_3782_, 1);
lean_inc(v_candidates_3783_);
lean_dec_ref(v_split_3782_);
v___x_3784_ = lean_array_mk(v_candidates_3783_);
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_array_get_size(v___x_3784_);
v___x_3787_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3765_, v___x_3784_, v___x_3785_, v___x_3786_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec_ref(v___x_3784_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3799_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3799_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3799_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3792_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3788_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 1, v___x_3792_);
lean_ctor_set(v___x_3780_, 0, v_a_3788_);
v___x_3794_ = v___x_3780_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3788_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3794_);
v___x_3796_ = v___x_3790_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_del_object(v___x_3780_);
v_a_3800_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3787_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3787_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec(v_a_3811_);
return v_res_3822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3823_, lean_object* v_m_3824_, uint64_t v_a_3825_){
_start:
{
uint8_t v___x_3826_; 
v___x_3826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3824_, v_a_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3827_, lean_object* v_m_3828_, lean_object* v_a_3829_){
_start:
{
uint64_t v_a_boxed_3830_; uint8_t v_res_3831_; lean_object* v_r_3832_; 
v_a_boxed_3830_ = lean_unbox_uint64(v_a_3829_);
lean_dec_ref(v_a_3829_);
v_res_3831_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_3827_, v_m_3828_, v_a_boxed_3830_);
lean_dec_ref(v_m_3828_);
v_r_3832_ = lean_box(v_res_3831_);
return v_r_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3833_, lean_object* v_m_3834_, uint64_t v_a_3835_, lean_object* v_b_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3834_, v_a_3835_, v_b_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3838_, lean_object* v_m_3839_, lean_object* v_a_3840_, lean_object* v_b_3841_){
_start:
{
uint64_t v_a_boxed_3842_; lean_object* v_res_3843_; 
v_a_boxed_3842_ = lean_unbox_uint64(v_a_3840_);
lean_dec_ref(v_a_3840_);
v_res_3843_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_3838_, v_m_3839_, v_a_boxed_3842_, v_b_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3844_, uint64_t v_a_3845_, lean_object* v_x_3846_){
_start:
{
uint8_t v___x_3847_; 
v___x_3847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3845_, v_x_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3848_, lean_object* v_a_3849_, lean_object* v_x_3850_){
_start:
{
uint64_t v_a_boxed_3851_; uint8_t v_res_3852_; lean_object* v_r_3853_; 
v_a_boxed_3851_ = lean_unbox_uint64(v_a_3849_);
lean_dec_ref(v_a_3849_);
v_res_3852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_3848_, v_a_boxed_3851_, v_x_3850_);
lean_dec(v_x_3850_);
v_r_3853_ = lean_box(v_res_3852_);
return v_r_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_3854_, lean_object* v_data_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_data_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_3857_, lean_object* v_i_3858_, lean_object* v_source_3859_, lean_object* v_target_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_i_3858_, v_source_3859_, v_target_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_3862_, lean_object* v_x_3863_, lean_object* v_x_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(v_x_3863_, v_x_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_p_3885_; lean_object* v___x_3888_; 
lean_inc_ref(v_proof_3878_);
v___x_3888_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_3878_, v_a_3880_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3927_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3927_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3927_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3909_ = l_Lean_Expr_cleanupAnnotations(v_a_3889_);
v___x_3910_ = l_Lean_Expr_isApp(v___x_3909_);
if (v___x_3910_ == 0)
{
lean_dec_ref(v___x_3909_);
v___y_3894_ = v_a_3879_;
v___y_3895_ = v_a_3880_;
v___y_3896_ = v_a_3881_;
v___y_3897_ = v_a_3882_;
goto v___jp_3893_;
}
else
{
lean_object* v_arg_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v_arg_3911_ = lean_ctor_get(v___x_3909_, 1);
lean_inc_ref(v_arg_3911_);
v___x_3912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3909_);
v___x_3913_ = l_Lean_Expr_isApp(v___x_3912_);
if (v___x_3913_ == 0)
{
lean_dec_ref(v___x_3912_);
lean_dec_ref(v_arg_3911_);
v___y_3894_ = v_a_3879_;
v___y_3895_ = v_a_3880_;
v___y_3896_ = v_a_3881_;
v___y_3897_ = v_a_3882_;
goto v___jp_3893_;
}
else
{
lean_object* v_arg_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v_arg_3914_ = lean_ctor_get(v___x_3912_, 1);
lean_inc_ref(v_arg_3914_);
v___x_3915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3912_);
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_3917_ = l_Lean_Expr_isConstOf(v___x_3915_, v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; uint8_t v___x_3919_; 
lean_dec_ref(v_arg_3914_);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_3919_ = l_Lean_Expr_isConstOf(v___x_3915_, v___x_3918_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_3921_ = l_Lean_Expr_isConstOf(v___x_3915_, v___x_3920_);
lean_dec_ref(v___x_3915_);
if (v___x_3921_ == 0)
{
lean_dec_ref(v_arg_3911_);
v___y_3894_ = v_a_3879_;
v___y_3895_ = v_a_3880_;
v___y_3896_ = v_a_3881_;
v___y_3897_ = v_a_3882_;
goto v___jp_3893_;
}
else
{
lean_del_object(v___x_3891_);
lean_dec_ref(v_proof_3878_);
v_p_3885_ = v_arg_3911_;
goto v___jp_3884_;
}
}
else
{
lean_dec_ref(v___x_3915_);
lean_del_object(v___x_3891_);
lean_dec_ref(v_proof_3878_);
v_p_3885_ = v_arg_3911_;
goto v___jp_3884_;
}
}
else
{
uint8_t v___x_3922_; 
lean_dec_ref(v___x_3915_);
lean_del_object(v___x_3891_);
lean_dec_ref(v_proof_3878_);
v___x_3922_ = l_Lean_Expr_isFalse(v_arg_3914_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec_ref(v_arg_3911_);
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v_arg_3911_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
return v___x_3926_;
}
}
}
}
v___jp_3893_:
{
if (lean_obj_tag(v_proof_3878_) == 6)
{
lean_object* v_body_3898_; uint8_t v___x_3899_; 
v_body_3898_ = lean_ctor_get(v_proof_3878_, 2);
lean_inc_ref(v_body_3898_);
lean_dec_ref(v_proof_3878_);
v___x_3899_ = l_Lean_Expr_hasLooseBVars(v_body_3898_);
if (v___x_3899_ == 0)
{
lean_del_object(v___x_3891_);
v_proof_3878_ = v_body_3898_;
v_a_3879_ = v___y_3894_;
v_a_3880_ = v___y_3895_;
v_a_3881_ = v___y_3896_;
v_a_3882_ = v___y_3897_;
goto _start;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
lean_dec_ref(v_body_3898_);
v___x_3901_ = lean_box(0);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3901_);
v___x_3903_ = v___x_3891_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_dec_ref(v_proof_3878_);
v___x_3905_ = lean_box(0);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3905_);
v___x_3907_ = v___x_3891_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v_proof_3878_);
v_a_3928_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3888_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3888_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
v___jp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_p_3885_);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_3943_, lean_object* v___y_3944_){
_start:
{
uint8_t v___x_3946_; 
v___x_3946_ = l_Lean_Expr_hasMVar(v_e_3943_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_e_3943_);
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; lean_object* v_mctx_3949_; lean_object* v___x_3950_; lean_object* v_fst_3951_; lean_object* v_snd_3952_; lean_object* v___x_3953_; lean_object* v_cache_3954_; lean_object* v_zetaDeltaFVarIds_3955_; lean_object* v_postponed_3956_; lean_object* v_diag_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3966_; 
v___x_3948_ = lean_st_ref_get(v___y_3944_);
v_mctx_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_ref(v_mctx_3949_);
lean_dec(v___x_3948_);
v___x_3950_ = l_Lean_instantiateMVarsCore(v_mctx_3949_, v_e_3943_);
v_fst_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_fst_3951_);
v_snd_3952_ = lean_ctor_get(v___x_3950_, 1);
lean_inc(v_snd_3952_);
lean_dec_ref(v___x_3950_);
v___x_3953_ = lean_st_ref_take(v___y_3944_);
v_cache_3954_ = lean_ctor_get(v___x_3953_, 1);
v_zetaDeltaFVarIds_3955_ = lean_ctor_get(v___x_3953_, 2);
v_postponed_3956_ = lean_ctor_get(v___x_3953_, 3);
v_diag_3957_ = lean_ctor_get(v___x_3953_, 4);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v___x_3953_, 0);
lean_dec(v_unused_3967_);
v___x_3959_ = v___x_3953_;
v_isShared_3960_ = v_isSharedCheck_3966_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_diag_3957_);
lean_inc(v_postponed_3956_);
lean_inc(v_zetaDeltaFVarIds_3955_);
lean_inc(v_cache_3954_);
lean_dec(v___x_3953_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3966_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v_snd_3952_);
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_snd_3952_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_cache_3954_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_zetaDeltaFVarIds_3955_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_postponed_3956_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_diag_3957_);
v___x_3962_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_st_ref_set(v___y_3944_, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v_fst_3951_);
return v___x_3964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_3968_, v___y_3969_);
lean_dec(v___y_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_3972_, v___y_3974_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_3986_, lean_object* v_x_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3986_, v_x_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v_a_4002_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3993_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3993_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4010_, lean_object* v_x_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4010_, v_x_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4018_, lean_object* v_mvarId_4019_, lean_object* v_x_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4019_, v_x_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4027_, lean_object* v_mvarId_4028_, lean_object* v_x_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4027_, v_mvarId_4028_, v_x_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4053_; 
v___x_4042_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4036_, v___y_4038_);
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
uint8_t v___x_4047_; 
v___x_4047_ = l_Lean_Expr_hasSyntheticSorry(v_a_4043_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; 
lean_del_object(v___x_4045_);
v___x_4048_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4043_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4048_;
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
lean_dec(v_a_4043_);
v___x_4049_ = lean_box(0);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4049_);
v___x_4051_ = v___x_4045_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; 
lean_inc(v_mvarId_4061_);
v___x_4067_ = l_Lean_mkMVar(v_mvarId_4061_);
v___f_4068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4068_, 0, v___x_4067_);
v___x_4069_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4061_, v___f_4068_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4100_){
_start:
{
if (lean_obj_tag(v_x_4100_) == 0)
{
uint8_t v___x_4101_; 
v___x_4101_ = 1;
return v___x_4101_;
}
else
{
lean_object* v_head_4102_; lean_object* v_tail_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_head_4102_ = lean_ctor_get(v_x_4100_, 0);
lean_inc_n(v_head_4102_, 2);
v_tail_4103_ = lean_ctor_get(v_x_4100_, 1);
lean_inc(v_tail_4103_);
lean_dec_ref(v_x_4100_);
v___x_4104_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
v___x_4105_ = l_Lean_Syntax_isOfKind(v_head_4102_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4106_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
lean_inc(v_head_4102_);
v___x_4107_ = l_Lean_Syntax_isOfKind(v_head_4102_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_dec(v_head_4102_);
v_x_4100_ = v_tail_4103_;
goto _start;
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4109_ = lean_unsigned_to_nat(1u);
v___x_4110_ = l_Lean_Syntax_getArg(v_head_4102_, v___x_4109_);
lean_dec(v_head_4102_);
v___x_4111_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7));
v___x_4112_ = l_Lean_Syntax_isOfKind(v___x_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
v_x_4100_ = v_tail_4103_;
goto _start;
}
else
{
if (v___x_4105_ == 0)
{
lean_dec(v_tail_4103_);
return v___x_4105_;
}
else
{
v_x_4100_ = v_tail_4103_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
v___x_4115_ = lean_unsigned_to_nat(3u);
v___x_4116_ = l_Lean_Syntax_getArg(v_head_4102_, v___x_4115_);
lean_dec(v_head_4102_);
v___x_4117_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__7));
v___x_4118_ = l_Lean_Syntax_isOfKind(v___x_4116_, v___x_4117_);
if (v___x_4118_ == 0)
{
v_x_4100_ = v_tail_4103_;
goto _start;
}
else
{
uint8_t v___x_4120_; 
lean_dec(v_tail_4103_);
v___x_4120_ = 0;
return v___x_4120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4121_){
_start:
{
uint8_t v_res_4122_; lean_object* v_r_4123_; 
v_res_4122_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4121_);
v_r_4123_ = lean_box(v_res_4122_);
return v_r_4123_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4124_){
_start:
{
uint8_t v___x_4125_; 
v___x_4125_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4126_){
_start:
{
uint8_t v_res_4127_; lean_object* v_r_4128_; 
v_res_4127_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4126_);
v_r_4128_ = lean_box(v_res_4127_);
return v_r_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4144_, lean_object* v_a_4145_){
_start:
{
if (lean_obj_tag(v_seq_4144_) == 0)
{
lean_object* v_ref_4147_; uint8_t v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_ref_4147_ = lean_ctor_get(v_a_4145_, 5);
v___x_4148_ = 0;
v___x_4149_ = l_Lean_SourceInfo_fromRef(v_ref_4147_, v___x_4148_);
v___x_4150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4149_);
v___x_4152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4149_);
lean_ctor_set(v___x_4152_, 1, v___x_4150_);
v___x_4153_ = l_Lean_Syntax_node1(v___x_4149_, v___x_4151_, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
return v___x_4154_;
}
else
{
lean_object* v_tail_4155_; 
v_tail_4155_ = lean_ctor_get(v_seq_4144_, 1);
if (lean_obj_tag(v_tail_4155_) == 0)
{
lean_object* v_head_4156_; lean_object* v___x_4157_; 
v_head_4156_ = lean_ctor_get(v_seq_4144_, 0);
lean_inc(v_head_4156_);
lean_dec_ref(v_seq_4144_);
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_head_4156_);
return v___x_4157_;
}
else
{
lean_object* v_head_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4180_; 
lean_inc(v_tail_4155_);
v_head_4158_ = lean_ctor_get(v_seq_4144_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_seq_4144_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v_seq_4144_, 1);
lean_dec(v_unused_4181_);
v___x_4160_ = v_seq_4144_;
v_isShared_4161_ = v_isSharedCheck_4180_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_head_4158_);
lean_dec(v_seq_4144_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4180_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4179_; 
v___x_4162_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4155_, v_a_4145_);
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4179_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4179_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v_ref_4167_; uint8_t v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v_ref_4167_ = lean_ctor_get(v_a_4145_, 5);
v___x_4168_ = 0;
v___x_4169_ = l_Lean_SourceInfo_fromRef(v_ref_4167_, v___x_4168_);
v___x_4170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4169_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 2);
lean_ctor_set(v___x_4160_, 1, v___x_4171_);
lean_ctor_set(v___x_4160_, 0, v___x_4169_);
v___x_4173_ = v___x_4160_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4174_ = l_Lean_Syntax_node3(v___x_4169_, v___x_4170_, v_head_4158_, v___x_4173_, v_a_4163_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4174_);
v___x_4176_ = v___x_4165_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4182_, v_a_4183_);
lean_dec_ref(v_a_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4186_, v_a_4187_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4196_, lean_object* v_seq_4197_, lean_object* v_a_4198_){
_start:
{
if (lean_obj_tag(v_seq_4197_) == 0)
{
lean_object* v___x_4200_; 
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_cases_4196_);
return v___x_4200_;
}
else
{
lean_object* v___x_4201_; lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4216_; 
v___x_4201_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4197_, v_a_4198_);
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_ref_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4214_; 
v_ref_4206_ = lean_ctor_get(v_a_4198_, 5);
v___x_4207_ = 0;
v___x_4208_ = l_Lean_SourceInfo_fromRef(v_ref_4206_, v___x_4207_);
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4208_);
v___x_4211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4208_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = l_Lean_Syntax_node3(v___x_4208_, v___x_4209_, v_cases_4196_, v___x_4211_, v_a_4202_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4212_);
v___x_4214_ = v___x_4204_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4217_, lean_object* v_seq_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4217_, v_seq_4218_, v_a_4219_);
lean_dec_ref(v_a_4219_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4222_, lean_object* v_seq_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4222_, v_seq_4223_, v_a_4224_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4228_, lean_object* v_seq_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4228_, v_seq_4229_, v_a_4230_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
return v_res_4233_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4234_, lean_object* v_x_4235_){
_start:
{
if (lean_obj_tag(v_x_4234_) == 0)
{
if (lean_obj_tag(v_x_4235_) == 0)
{
uint8_t v___x_4236_; 
v___x_4236_ = 1;
return v___x_4236_;
}
else
{
uint8_t v___x_4237_; 
lean_dec_ref(v_x_4235_);
v___x_4237_ = 0;
return v___x_4237_;
}
}
else
{
if (lean_obj_tag(v_x_4235_) == 0)
{
uint8_t v___x_4238_; 
lean_dec_ref(v_x_4234_);
v___x_4238_ = 0;
return v___x_4238_;
}
else
{
lean_object* v_head_4239_; lean_object* v_tail_4240_; lean_object* v_head_4241_; lean_object* v_tail_4242_; uint8_t v___x_4243_; 
v_head_4239_ = lean_ctor_get(v_x_4234_, 0);
lean_inc(v_head_4239_);
v_tail_4240_ = lean_ctor_get(v_x_4234_, 1);
lean_inc(v_tail_4240_);
lean_dec_ref(v_x_4234_);
v_head_4241_ = lean_ctor_get(v_x_4235_, 0);
lean_inc(v_head_4241_);
v_tail_4242_ = lean_ctor_get(v_x_4235_, 1);
lean_inc(v_tail_4242_);
lean_dec_ref(v_x_4235_);
v___x_4243_ = l_Lean_Syntax_structEq(v_head_4239_, v_head_4241_);
if (v___x_4243_ == 0)
{
lean_dec(v_tail_4242_);
lean_dec(v_tail_4240_);
return v___x_4243_;
}
else
{
v_x_4234_ = v_tail_4240_;
v_x_4235_ = v_tail_4242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
uint8_t v_res_4247_; lean_object* v_r_4248_; 
v_res_4247_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4245_, v_x_4246_);
v_r_4248_ = lean_box(v_res_4247_);
return v_r_4248_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4249_, uint8_t v___x_4250_, lean_object* v_as_4251_, size_t v_i_4252_, size_t v_stop_4253_){
_start:
{
uint8_t v___x_4254_; 
v___x_4254_ = lean_usize_dec_eq(v_i_4252_, v_stop_4253_);
if (v___x_4254_ == 0)
{
uint8_t v___x_4255_; uint8_t v___y_4257_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4255_ = 1;
v___x_4261_ = lean_array_uget_borrowed(v_as_4251_, v_i_4252_);
lean_inc(v_alt_4249_);
lean_inc(v___x_4261_);
v___x_4262_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4261_, v_alt_4249_);
if (v___x_4262_ == 0)
{
v___y_4257_ = v___x_4250_;
goto v___jp_4256_;
}
else
{
v___y_4257_ = v___x_4254_;
goto v___jp_4256_;
}
v___jp_4256_:
{
if (v___y_4257_ == 0)
{
size_t v___x_4258_; size_t v___x_4259_; 
v___x_4258_ = ((size_t)1ULL);
v___x_4259_ = lean_usize_add(v_i_4252_, v___x_4258_);
v_i_4252_ = v___x_4259_;
goto _start;
}
else
{
lean_dec(v_alt_4249_);
return v___x_4255_;
}
}
}
else
{
uint8_t v___x_4263_; 
lean_dec(v_alt_4249_);
v___x_4263_ = 0;
return v___x_4263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4264_, lean_object* v___x_4265_, lean_object* v_as_4266_, lean_object* v_i_4267_, lean_object* v_stop_4268_){
_start:
{
uint8_t v___x_359__boxed_4269_; size_t v_i_boxed_4270_; size_t v_stop_boxed_4271_; uint8_t v_res_4272_; lean_object* v_r_4273_; 
v___x_359__boxed_4269_ = lean_unbox(v___x_4265_);
v_i_boxed_4270_ = lean_unbox_usize(v_i_4267_);
lean_dec(v_i_4267_);
v_stop_boxed_4271_ = lean_unbox_usize(v_stop_4268_);
lean_dec(v_stop_4268_);
v_res_4272_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4264_, v___x_359__boxed_4269_, v_as_4266_, v_i_boxed_4270_, v_stop_boxed_4271_);
lean_dec_ref(v_as_4266_);
v_r_4273_ = lean_box(v_res_4272_);
return v_r_4273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4274_){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4275_ = lean_unsigned_to_nat(0u);
v___x_4276_ = lean_array_get_size(v_alts_4274_);
v___x_4277_ = lean_nat_dec_lt(v___x_4275_, v___x_4276_);
if (v___x_4277_ == 0)
{
uint8_t v___x_4278_; 
v___x_4278_ = 1;
return v___x_4278_;
}
else
{
lean_object* v_alt_4279_; uint8_t v___x_4280_; 
v_alt_4279_ = lean_array_fget_borrowed(v_alts_4274_, v___x_4275_);
lean_inc(v_alt_4279_);
v___x_4280_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4279_);
if (v___x_4280_ == 0)
{
return v___x_4280_;
}
else
{
if (v___x_4277_ == 0)
{
return v___x_4280_;
}
else
{
if (v___x_4277_ == 0)
{
return v___x_4280_;
}
else
{
size_t v___x_4281_; size_t v___x_4282_; uint8_t v___x_4283_; 
v___x_4281_ = ((size_t)0ULL);
v___x_4282_ = lean_usize_of_nat(v___x_4276_);
lean_inc(v_alt_4279_);
v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4279_, v___x_4280_, v_alts_4274_, v___x_4281_, v___x_4282_);
if (v___x_4283_ == 0)
{
return v___x_4280_;
}
else
{
uint8_t v___x_4284_; 
v___x_4284_ = 0;
return v___x_4284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4285_){
_start:
{
uint8_t v_res_4286_; lean_object* v_r_4287_; 
v_res_4286_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4285_);
lean_dec_ref(v_alts_4285_);
v_r_4287_ = lean_box(v_res_4286_);
return v_r_4287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4295_){
_start:
{
if (lean_obj_tag(v_alt_4295_) == 1)
{
lean_object* v_tail_4296_; 
v_tail_4296_ = lean_ctor_get(v_alt_4295_, 1);
if (lean_obj_tag(v_tail_4296_) == 0)
{
lean_object* v_head_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_head_4297_ = lean_ctor_get(v_alt_4295_, 0);
lean_inc(v_head_4297_);
lean_dec_ref(v_alt_4295_);
v___x_4298_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4299_ = l_Lean_Syntax_isOfKind(v_head_4297_, v___x_4298_);
return v___x_4299_;
}
else
{
uint8_t v___x_4300_; 
lean_dec_ref(v_alt_4295_);
v___x_4300_ = 0;
return v___x_4300_;
}
}
else
{
uint8_t v___x_4301_; 
lean_dec(v_alt_4295_);
v___x_4301_ = 0;
return v___x_4301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4302_){
_start:
{
uint8_t v_res_4303_; lean_object* v_r_4304_; 
v_res_4303_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4302_);
v_r_4304_ = lean_box(v_res_4303_);
return v_r_4304_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4305_, lean_object* v_x_4306_, lean_object* v___y_4307_){
_start:
{
if (lean_obj_tag(v_x_4305_) == 0)
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = l_List_reverse___redArg(v_x_4306_);
v___x_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
return v___x_4310_;
}
else
{
lean_object* v_head_4311_; lean_object* v_tail_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4330_; 
v_head_4311_ = lean_ctor_get(v_x_4305_, 0);
v_tail_4312_ = lean_ctor_get(v_x_4305_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_x_4305_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4314_ = v_x_4305_;
v_isShared_4315_ = v_isSharedCheck_4330_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_tail_4312_);
lean_inc(v_head_4311_);
lean_dec(v_x_4305_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4330_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4311_, v___y_4307_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4319_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref(v___x_4316_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 1, v_x_4306_);
lean_ctor_set(v___x_4314_, 0, v_a_4317_);
v___x_4319_ = v___x_4314_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4317_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_x_4306_);
v___x_4319_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v_x_4305_ = v_tail_4312_;
v_x_4306_ = v___x_4319_;
goto _start;
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_del_object(v___x_4314_);
lean_dec(v_tail_4312_);
lean_dec(v_x_4306_);
v_a_4322_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4316_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4316_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4331_, lean_object* v_x_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4331_, v_x_4332_, v___y_4333_);
lean_dec_ref(v___y_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4336_, lean_object* v_alts_4337_, uint8_t v_compress_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_seq_4343_; 
if (v_compress_4338_ == 0)
{
goto v___jp_4346_;
}
else
{
uint8_t v___x_4356_; 
v___x_4356_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4337_);
if (v___x_4356_ == 0)
{
goto v___jp_4346_;
}
else
{
lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4357_ = lean_unsigned_to_nat(0u);
v___x_4358_ = lean_array_get_size(v_alts_4337_);
v___x_4359_ = lean_nat_dec_lt(v___x_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec_ref(v_alts_4337_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4361_, 0, v_cases_4336_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
else
{
lean_object* v___x_4363_; lean_object* v_firstAlt_4364_; uint8_t v___x_4365_; 
v___x_4363_ = lean_box(0);
v_firstAlt_4364_ = lean_array_get(v___x_4363_, v_alts_4337_, v___x_4357_);
lean_dec_ref(v_alts_4337_);
lean_inc(v_firstAlt_4364_);
v___x_4365_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4375_; 
v___x_4366_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4336_, v_firstAlt_4364_, v_a_4339_);
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4371_, 0, v_a_4367_);
lean_ctor_set(v___x_4371_, 1, v___x_4363_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4371_);
v___x_4373_ = v___x_4369_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_object* v___x_4376_; 
lean_dec(v_cases_4336_);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v_firstAlt_4364_);
return v___x_4376_;
}
}
}
}
v___jp_4342_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4344_, 0, v_cases_4336_);
lean_ctor_set(v___x_4344_, 1, v_seq_4343_);
v___x_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
return v___x_4345_;
}
v___jp_4346_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4347_ = lean_array_get_size(v_alts_4337_);
v___x_4348_ = lean_unsigned_to_nat(1u);
v___x_4349_ = lean_nat_dec_eq(v___x_4347_, v___x_4348_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4350_ = lean_array_to_list(v_alts_4337_);
v___x_4351_ = lean_box(0);
v___x_4352_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4350_, v___x_4351_, v_a_4339_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref(v___x_4352_);
v_seq_4343_ = v_a_4353_;
goto v___jp_4342_;
}
else
{
lean_dec(v_cases_4336_);
return v___x_4352_;
}
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_unsigned_to_nat(0u);
v___x_4355_ = lean_array_fget(v_alts_4337_, v___x_4354_);
lean_dec_ref(v_alts_4337_);
v_seq_4343_ = v___x_4355_;
goto v___jp_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4377_, lean_object* v_alts_4378_, lean_object* v_compress_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
uint8_t v_compress_boxed_4383_; lean_object* v_res_4384_; 
v_compress_boxed_4383_ = lean_unbox(v_compress_4379_);
v_res_4384_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4377_, v_alts_4378_, v_compress_boxed_4383_, v_a_4380_, v_a_4381_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4385_, lean_object* v_x_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4385_, v_x_4386_, v___y_4387_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4391_, lean_object* v_x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4391_, v_x_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; lean_object* v_env_4401_; uint8_t v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4400_ = lean_st_ref_get(v___y_4398_);
v_env_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc_ref(v_env_4401_);
lean_dec(v___x_4400_);
v___x_4402_ = l_Lean_Meta_isMatcherAppCore(v_env_4401_, v_e_4397_);
v___x_4403_ = lean_box(v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v_e_4405_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4409_, v___y_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v_e_4422_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc(v___y_4436_);
v___x_4446_ = lean_apply_10(v_x_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, lean_box(0));
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4459_, lean_object* v_x_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v___f_4471_; lean_object* v___x_4472_; 
lean_inc(v___y_4465_);
lean_inc_ref(v___y_4464_);
lean_inc(v___y_4463_);
lean_inc_ref(v___y_4462_);
lean_inc(v___y_4461_);
v___f_4471_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4471_, 0, v_x_4460_);
lean_closure_set(v___f_4471_, 1, v___y_4461_);
lean_closure_set(v___f_4471_, 2, v___y_4462_);
lean_closure_set(v___f_4471_, 3, v___y_4463_);
lean_closure_set(v___f_4471_, 4, v___y_4464_);
lean_closure_set(v___f_4471_, 5, v___y_4465_);
v___x_4472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4459_, v___f_4471_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
if (lean_obj_tag(v___x_4472_) == 0)
{
return v___x_4472_;
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4481_, lean_object* v_x_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4481_, v_x_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_4494_, lean_object* v_mvarId_4495_, lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4495_, v_x_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_4508_, lean_object* v_mvarId_4509_, lean_object* v_x_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_4508_, v_mvarId_4509_, v_x_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_4522_, lean_object* v___y_4523_){
_start:
{
uint8_t v___x_4525_; 
v___x_4525_ = l_Lean_Expr_hasMVar(v_e_4522_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v_e_4522_);
return v___x_4526_;
}
else
{
lean_object* v___x_4527_; lean_object* v_mctx_4528_; lean_object* v___x_4529_; lean_object* v_fst_4530_; lean_object* v_snd_4531_; lean_object* v___x_4532_; lean_object* v_cache_4533_; lean_object* v_zetaDeltaFVarIds_4534_; lean_object* v_postponed_4535_; lean_object* v_diag_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4545_; 
v___x_4527_ = lean_st_ref_get(v___y_4523_);
v_mctx_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc_ref(v_mctx_4528_);
lean_dec(v___x_4527_);
v___x_4529_ = l_Lean_instantiateMVarsCore(v_mctx_4528_, v_e_4522_);
v_fst_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_fst_4530_);
v_snd_4531_ = lean_ctor_get(v___x_4529_, 1);
lean_inc(v_snd_4531_);
lean_dec_ref(v___x_4529_);
v___x_4532_ = lean_st_ref_take(v___y_4523_);
v_cache_4533_ = lean_ctor_get(v___x_4532_, 1);
v_zetaDeltaFVarIds_4534_ = lean_ctor_get(v___x_4532_, 2);
v_postponed_4535_ = lean_ctor_get(v___x_4532_, 3);
v_diag_4536_ = lean_ctor_get(v___x_4532_, 4);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v___x_4532_, 0);
lean_dec(v_unused_4546_);
v___x_4538_ = v___x_4532_;
v_isShared_4539_ = v_isSharedCheck_4545_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_diag_4536_);
lean_inc(v_postponed_4535_);
lean_inc(v_zetaDeltaFVarIds_4534_);
lean_inc(v_cache_4533_);
lean_dec(v___x_4532_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4545_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v_snd_4531_);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_snd_4531_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_cache_4533_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v_zetaDeltaFVarIds_4534_);
lean_ctor_set(v_reuseFailAlloc_4544_, 3, v_postponed_4535_);
lean_ctor_set(v_reuseFailAlloc_4544_, 4, v_diag_4536_);
v___x_4541_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = lean_st_ref_set(v___y_4523_, v___x_4541_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_fst_4530_);
return v___x_4543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_4547_, v___y_4548_);
lean_dec(v___y_4548_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_4551_, v___y_4558_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(uint8_t v___x_4575_, lean_object* v_x_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_box(v___x_4575_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object* v___x_4590_, lean_object* v_x_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v___x_90937__boxed_4603_; lean_object* v_res_4604_; 
v___x_90937__boxed_4603_ = lean_unbox(v___x_4590_);
v_res_4604_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_90937__boxed_4603_, v_x_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v_x_4591_);
return v_res_4604_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__0));
v___x_4607_ = l_Lean_stringToMessageData(v___x_4606_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_4611_, lean_object* v___x_4612_, uint8_t v_trace_4613_, lean_object* v_c_4614_, lean_object* v_a_4615_, lean_object* v_numCases_4616_, uint8_t v_isRec_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v___x_4628_; lean_object* v___y_4630_; lean_object* v_numDigits_4631_; lean_object* v___y_4637_; lean_object* v_mvarIds_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___x_4719_; 
v___x_4628_ = lean_st_mk_ref(v_goal_4611_);
v___x_4719_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_4612_, v___x_4628_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___x_4774_; uint8_t v___y_4776_; uint8_t v___x_4779_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref(v___x_4719_);
v___x_4774_ = lean_unsigned_to_nat(1u);
v___x_4779_ = lean_nat_dec_lt(v___x_4774_, v_numCases_4616_);
if (v___x_4779_ == 0)
{
v___y_4776_ = v_isRec_4617_;
goto v___jp_4775_;
}
else
{
v___y_4776_ = v___x_4779_;
goto v___jp_4775_;
}
v___jp_4721_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_4614_);
lean_inc_ref(v___x_4612_);
v___x_4725_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_4612_, v___y_4723_, v_numCases_4616_, v___x_4724_, v___y_4620_, v___y_4623_, v___y_4625_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v___x_4726_; 
lean_dec_ref(v___x_4725_);
lean_inc_ref(v___x_4612_);
v___x_4726_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_4612_, v___x_4628_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_options_4727_; uint8_t v_hasTrace_4728_; 
lean_dec_ref(v___x_4726_);
v_options_4727_ = lean_ctor_get(v___y_4625_, 2);
v_hasTrace_4728_ = lean_ctor_get_uint8(v_options_4727_, sizeof(void*)*1);
if (v_hasTrace_4728_ == 0)
{
lean_dec(v_a_4720_);
lean_inc(v___x_4628_);
v___y_4662_ = v___y_4722_;
v___y_4663_ = v___x_4628_;
v___y_4664_ = v___y_4618_;
v___y_4665_ = v___y_4619_;
v___y_4666_ = v___y_4620_;
v___y_4667_ = v___y_4621_;
v___y_4668_ = v___y_4622_;
v___y_4669_ = v___y_4623_;
v___y_4670_ = v___y_4624_;
v___y_4671_ = v___y_4625_;
v___y_4672_ = v___y_4626_;
goto v___jp_4661_;
}
else
{
lean_object* v_inheritedTraceOptions_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v_inheritedTraceOptions_4729_ = lean_ctor_get(v___y_4625_, 13);
v___x_4730_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__1));
v___x_4731_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___closed__2);
v___x_4732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4729_, v_options_4727_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_dec(v_a_4720_);
lean_inc(v___x_4628_);
v___y_4662_ = v___y_4722_;
v___y_4663_ = v___x_4628_;
v___y_4664_ = v___y_4618_;
v___y_4665_ = v___y_4619_;
v___y_4666_ = v___y_4620_;
v___y_4667_ = v___y_4621_;
v___y_4668_ = v___y_4622_;
v___y_4669_ = v___y_4623_;
v___y_4670_ = v___y_4624_;
v___y_4671_ = v___y_4625_;
v___y_4672_ = v___y_4626_;
goto v___jp_4661_;
}
else
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_Meta_Grind_updateLastTag(v___x_4628_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_dec_ref(v___x_4733_);
lean_inc_ref(v___x_4612_);
v___x_4734_ = l_Lean_MessageData_ofExpr(v___x_4612_);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__1);
v___x_4736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4734_);
lean_ctor_set(v___x_4736_, 1, v___x_4735_);
v___x_4737_ = l_Nat_reprFast(v_a_4720_);
v___x_4738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
v___x_4739_ = l_Lean_MessageData_ofFormat(v___x_4738_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4736_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_4730_, v___x_4740_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_dec_ref(v___x_4741_);
lean_inc(v___x_4628_);
v___y_4662_ = v___y_4722_;
v___y_4663_ = v___x_4628_;
v___y_4664_ = v___y_4618_;
v___y_4665_ = v___y_4619_;
v___y_4666_ = v___y_4620_;
v___y_4667_ = v___y_4621_;
v___y_4668_ = v___y_4622_;
v___y_4669_ = v___y_4623_;
v___y_4670_ = v___y_4624_;
v___y_4671_ = v___y_4625_;
v___y_4672_ = v___y_4626_;
goto v___jp_4661_;
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec(v___x_4628_);
lean_dec(v_a_4615_);
lean_dec_ref(v_c_4614_);
lean_dec_ref(v___x_4612_);
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4741_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4741_);
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
lean_dec(v_a_4720_);
lean_dec(v___x_4628_);
lean_dec(v_a_4615_);
lean_dec_ref(v_c_4614_);
lean_dec_ref(v___x_4612_);
v_a_4750_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4733_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4733_);
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
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec(v_a_4720_);
lean_dec(v___x_4628_);
lean_dec(v_a_4615_);
lean_dec_ref(v_c_4614_);
lean_dec_ref(v___x_4612_);
v_a_4758_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4726_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4726_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_dec(v_a_4720_);
lean_dec(v___x_4628_);
lean_dec(v_a_4615_);
lean_dec_ref(v_c_4614_);
lean_dec_ref(v___x_4612_);
v_a_4766_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4725_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4725_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
v___jp_4775_:
{
lean_object* v___f_4777_; 
v___f_4777_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___closed__2));
if (v___y_4776_ == 0)
{
lean_inc(v_a_4720_);
v___y_4722_ = v___f_4777_;
v___y_4723_ = v_a_4720_;
goto v___jp_4721_;
}
else
{
lean_object* v___x_4778_; 
v___x_4778_ = lean_nat_add(v_a_4720_, v___x_4774_);
v___y_4722_ = v___f_4777_;
v___y_4723_ = v___x_4778_;
goto v___jp_4721_;
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_dec(v___x_4628_);
lean_dec(v_numCases_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_c_4614_);
lean_dec_ref(v___x_4612_);
v_a_4780_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4719_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4719_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
v___jp_4629_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4632_ = lean_st_ref_get(v___x_4628_);
lean_dec(v___x_4628_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___y_4630_);
lean_ctor_set(v___x_4633_, 1, v_numDigits_4631_);
v___x_4634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
lean_ctor_set(v___x_4634_, 1, v___x_4632_);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
v___jp_4636_:
{
if (v_trace_4613_ == 0)
{
lean_object* v___x_4649_; 
lean_dec(v___y_4639_);
v___x_4649_ = lean_unsigned_to_nat(0u);
v___y_4630_ = v_mvarIds_4638_;
v_numDigits_4631_ = v___x_4649_;
goto v___jp_4629_;
}
else
{
lean_object* v___x_4650_; 
lean_inc_ref(v___y_4637_);
v___x_4650_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___y_4637_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4639_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v_numDigits_4652_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref(v___x_4650_);
v_numDigits_4652_ = lean_ctor_get(v_a_4651_, 1);
lean_inc(v_numDigits_4652_);
lean_dec(v_a_4651_);
v___y_4630_ = v_mvarIds_4638_;
v_numDigits_4631_ = v_numDigits_4652_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec(v_mvarIds_4638_);
lean_dec(v___x_4628_);
v_a_4653_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4650_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4650_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
v___jp_4661_:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_4612_, v___y_4672_);
if (lean_obj_tag(v_c_4614_) == 1)
{
lean_object* v_e_4674_; lean_object* v_binderType_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
lean_dec_ref(v___x_4673_);
lean_dec_ref(v___x_4612_);
v_e_4674_ = lean_ctor_get(v_c_4614_, 0);
lean_inc_ref(v_e_4674_);
lean_dec_ref(v_c_4614_);
v_binderType_4675_ = lean_ctor_get(v_e_4674_, 1);
lean_inc_ref(v_binderType_4675_);
lean_dec_ref(v_e_4674_);
v___x_4676_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_4675_);
v___x_4677_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_4615_, v___x_4676_, v___y_4665_, v___y_4666_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___y_4637_ = v___y_4662_;
v_mvarIds_4638_ = v_a_4678_;
v___y_4639_ = v___y_4663_;
v___y_4640_ = v___y_4664_;
v___y_4641_ = v___y_4665_;
v___y_4642_ = v___y_4666_;
v___y_4643_ = v___y_4667_;
v___y_4644_ = v___y_4668_;
v___y_4645_ = v___y_4669_;
v___y_4646_ = v___y_4670_;
v___y_4647_ = v___y_4671_;
v___y_4648_ = v___y_4672_;
goto v___jp_4636_;
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_dec(v___y_4663_);
lean_dec(v___x_4628_);
v_a_4679_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4677_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4677_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_object* v_a_4687_; uint8_t v___x_4688_; 
lean_dec_ref(v_c_4614_);
v_a_4687_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4687_);
lean_dec_ref(v___x_4673_);
v___x_4688_ = lean_unbox(v_a_4687_);
lean_dec(v_a_4687_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4689_; 
v___x_4689_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_4612_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4691_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref(v___x_4689_);
v___x_4691_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_4615_, v_a_4690_, v___y_4665_, v___y_4666_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref(v___x_4691_);
v___y_4637_ = v___y_4662_;
v_mvarIds_4638_ = v_a_4692_;
v___y_4639_ = v___y_4663_;
v___y_4640_ = v___y_4664_;
v___y_4641_ = v___y_4665_;
v___y_4642_ = v___y_4666_;
v___y_4643_ = v___y_4667_;
v___y_4644_ = v___y_4668_;
v___y_4645_ = v___y_4669_;
v___y_4646_ = v___y_4670_;
v___y_4647_ = v___y_4671_;
v___y_4648_ = v___y_4672_;
goto v___jp_4636_;
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec(v___y_4663_);
lean_dec(v___x_4628_);
v_a_4693_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4691_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4691_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_dec(v___y_4663_);
lean_dec(v___x_4628_);
lean_dec(v_a_4615_);
v_a_4701_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4689_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4689_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
else
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_Meta_Grind_casesMatch(v_a_4615_, v___x_4612_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4709_);
v___y_4637_ = v___y_4662_;
v_mvarIds_4638_ = v_a_4710_;
v___y_4639_ = v___y_4663_;
v___y_4640_ = v___y_4664_;
v___y_4641_ = v___y_4665_;
v___y_4642_ = v___y_4666_;
v___y_4643_ = v___y_4667_;
v___y_4644_ = v___y_4668_;
v___y_4645_ = v___y_4669_;
v___y_4646_ = v___y_4670_;
v___y_4647_ = v___y_4671_;
v___y_4648_ = v___y_4672_;
goto v___jp_4636_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v___y_4663_);
lean_dec(v___x_4628_);
v_a_4711_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4709_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4709_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_goal_4788_ = _args[0];
lean_object* v___x_4789_ = _args[1];
lean_object* v_trace_4790_ = _args[2];
lean_object* v_c_4791_ = _args[3];
lean_object* v_a_4792_ = _args[4];
lean_object* v_numCases_4793_ = _args[5];
lean_object* v_isRec_4794_ = _args[6];
lean_object* v___y_4795_ = _args[7];
lean_object* v___y_4796_ = _args[8];
lean_object* v___y_4797_ = _args[9];
lean_object* v___y_4798_ = _args[10];
lean_object* v___y_4799_ = _args[11];
lean_object* v___y_4800_ = _args[12];
lean_object* v___y_4801_ = _args[13];
lean_object* v___y_4802_ = _args[14];
lean_object* v___y_4803_ = _args[15];
lean_object* v___y_4804_ = _args[16];
_start:
{
uint8_t v_trace_boxed_4805_; uint8_t v_isRec_boxed_4806_; lean_object* v_res_4807_; 
v_trace_boxed_4805_ = lean_unbox(v_trace_4790_);
v_isRec_boxed_4806_ = lean_unbox(v_isRec_4794_);
v_res_4807_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_4788_, v___x_4789_, v_trace_boxed_4805_, v_c_4791_, v_a_4792_, v_numCases_4793_, v_isRec_boxed_4806_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_4808_, lean_object* v_x_4809_, lean_object* v_x_4810_, lean_object* v_x_4811_){
_start:
{
lean_object* v_ks_4812_; lean_object* v_vs_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4837_; 
v_ks_4812_ = lean_ctor_get(v_x_4808_, 0);
v_vs_4813_ = lean_ctor_get(v_x_4808_, 1);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_x_4808_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4815_ = v_x_4808_;
v_isShared_4816_ = v_isSharedCheck_4837_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_vs_4813_);
lean_inc(v_ks_4812_);
lean_dec(v_x_4808_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4837_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___x_4817_ = lean_array_get_size(v_ks_4812_);
v___x_4818_ = lean_nat_dec_lt(v_x_4809_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
lean_dec(v_x_4809_);
v___x_4819_ = lean_array_push(v_ks_4812_, v_x_4810_);
v___x_4820_ = lean_array_push(v_vs_4813_, v_x_4811_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 1, v___x_4820_);
lean_ctor_set(v___x_4815_, 0, v___x_4819_);
v___x_4822_ = v___x_4815_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4819_);
lean_ctor_set(v_reuseFailAlloc_4823_, 1, v___x_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
else
{
lean_object* v_k_x27_4824_; uint8_t v___x_4825_; 
v_k_x27_4824_ = lean_array_fget_borrowed(v_ks_4812_, v_x_4809_);
v___x_4825_ = l_Lean_instBEqMVarId_beq(v_x_4810_, v_k_x27_4824_);
if (v___x_4825_ == 0)
{
lean_object* v___x_4827_; 
if (v_isShared_4816_ == 0)
{
v___x_4827_ = v___x_4815_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_ks_4812_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_vs_4813_);
v___x_4827_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = lean_nat_add(v_x_4809_, v___x_4828_);
lean_dec(v_x_4809_);
v_x_4808_ = v___x_4827_;
v_x_4809_ = v___x_4829_;
goto _start;
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4832_ = lean_array_fset(v_ks_4812_, v_x_4809_, v_x_4810_);
v___x_4833_ = lean_array_fset(v_vs_4813_, v_x_4809_, v_x_4811_);
lean_dec(v_x_4809_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 1, v___x_4833_);
lean_ctor_set(v___x_4815_, 0, v___x_4832_);
v___x_4835_ = v___x_4815_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4832_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v___x_4833_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_4838_, lean_object* v_k_4839_, lean_object* v_v_4840_){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_4838_, v___x_4841_, v_k_4839_, v_v_4840_);
return v___x_4842_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_4843_; size_t v___x_4844_; size_t v___x_4845_; 
v___x_4843_ = ((size_t)5ULL);
v___x_4844_ = ((size_t)1ULL);
v___x_4845_ = lean_usize_shift_left(v___x_4844_, v___x_4843_);
return v___x_4845_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_4846_; size_t v___x_4847_; size_t v___x_4848_; 
v___x_4846_ = ((size_t)1ULL);
v___x_4847_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_4848_ = lean_usize_sub(v___x_4847_, v___x_4846_);
return v___x_4848_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_4850_, size_t v_x_4851_, size_t v_x_4852_, lean_object* v_x_4853_, lean_object* v_x_4854_){
_start:
{
if (lean_obj_tag(v_x_4850_) == 0)
{
lean_object* v_es_4855_; size_t v___x_4856_; size_t v___x_4857_; size_t v___x_4858_; size_t v___x_4859_; lean_object* v_j_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v_es_4855_ = lean_ctor_get(v_x_4850_, 0);
v___x_4856_ = ((size_t)5ULL);
v___x_4857_ = ((size_t)1ULL);
v___x_4858_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__1);
v___x_4859_ = lean_usize_land(v_x_4851_, v___x_4858_);
v_j_4860_ = lean_usize_to_nat(v___x_4859_);
v___x_4861_ = lean_array_get_size(v_es_4855_);
v___x_4862_ = lean_nat_dec_lt(v_j_4860_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_dec(v_j_4860_);
lean_dec(v_x_4854_);
lean_dec(v_x_4853_);
return v_x_4850_;
}
else
{
lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4899_; 
lean_inc_ref(v_es_4855_);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_x_4850_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v_x_4850_, 0);
lean_dec(v_unused_4900_);
v___x_4864_ = v_x_4850_;
v_isShared_4865_ = v_isSharedCheck_4899_;
goto v_resetjp_4863_;
}
else
{
lean_dec(v_x_4850_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4899_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v_v_4866_; lean_object* v___x_4867_; lean_object* v_xs_x27_4868_; lean_object* v___y_4870_; 
v_v_4866_ = lean_array_fget(v_es_4855_, v_j_4860_);
v___x_4867_ = lean_box(0);
v_xs_x27_4868_ = lean_array_fset(v_es_4855_, v_j_4860_, v___x_4867_);
switch(lean_obj_tag(v_v_4866_))
{
case 0:
{
lean_object* v_key_4875_; lean_object* v_val_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4886_; 
v_key_4875_ = lean_ctor_get(v_v_4866_, 0);
v_val_4876_ = lean_ctor_get(v_v_4866_, 1);
v_isSharedCheck_4886_ = !lean_is_exclusive(v_v_4866_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4878_ = v_v_4866_;
v_isShared_4879_ = v_isSharedCheck_4886_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_val_4876_);
lean_inc(v_key_4875_);
lean_dec(v_v_4866_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4886_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint8_t v___x_4880_; 
v___x_4880_ = l_Lean_instBEqMVarId_beq(v_x_4853_, v_key_4875_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_del_object(v___x_4878_);
v___x_4881_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4875_, v_val_4876_, v_x_4853_, v_x_4854_);
v___x_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
v___y_4870_ = v___x_4882_;
goto v___jp_4869_;
}
else
{
lean_object* v___x_4884_; 
lean_dec(v_val_4876_);
lean_dec(v_key_4875_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 1, v_x_4854_);
lean_ctor_set(v___x_4878_, 0, v_x_4853_);
v___x_4884_ = v___x_4878_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_x_4853_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_x_4854_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
v___y_4870_ = v___x_4884_;
goto v___jp_4869_;
}
}
}
}
case 1:
{
lean_object* v_node_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4897_; 
v_node_4887_ = lean_ctor_get(v_v_4866_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_v_4866_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4889_ = v_v_4866_;
v_isShared_4890_ = v_isSharedCheck_4897_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_node_4887_);
lean_dec(v_v_4866_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4897_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
size_t v___x_4891_; size_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4891_ = lean_usize_shift_right(v_x_4851_, v___x_4856_);
v___x_4892_ = lean_usize_add(v_x_4852_, v___x_4857_);
v___x_4893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_4887_, v___x_4891_, v___x_4892_, v_x_4853_, v_x_4854_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4893_);
v___x_4895_ = v___x_4889_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
v___y_4870_ = v___x_4895_;
goto v___jp_4869_;
}
}
}
default: 
{
lean_object* v___x_4898_; 
v___x_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4898_, 0, v_x_4853_);
lean_ctor_set(v___x_4898_, 1, v_x_4854_);
v___y_4870_ = v___x_4898_;
goto v___jp_4869_;
}
}
v___jp_4869_:
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4871_ = lean_array_fset(v_xs_x27_4868_, v_j_4860_, v___y_4870_);
lean_dec(v_j_4860_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4871_);
v___x_4873_ = v___x_4864_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
else
{
lean_object* v_ks_4901_; lean_object* v_vs_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4922_; 
v_ks_4901_ = lean_ctor_get(v_x_4850_, 0);
v_vs_4902_ = lean_ctor_get(v_x_4850_, 1);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_x_4850_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4904_ = v_x_4850_;
v_isShared_4905_ = v_isSharedCheck_4922_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_vs_4902_);
lean_inc(v_ks_4901_);
lean_dec(v_x_4850_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4922_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_ks_4901_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_vs_4902_);
v___x_4907_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v_newNode_4908_; uint8_t v___y_4910_; size_t v___x_4916_; uint8_t v___x_4917_; 
v_newNode_4908_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_4907_, v_x_4853_, v_x_4854_);
v___x_4916_ = ((size_t)7ULL);
v___x_4917_ = lean_usize_dec_le(v___x_4916_, v_x_4852_);
if (v___x_4917_ == 0)
{
lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4908_);
v___x_4919_ = lean_unsigned_to_nat(4u);
v___x_4920_ = lean_nat_dec_lt(v___x_4918_, v___x_4919_);
lean_dec(v___x_4918_);
v___y_4910_ = v___x_4920_;
goto v___jp_4909_;
}
else
{
v___y_4910_ = v___x_4917_;
goto v___jp_4909_;
}
v___jp_4909_:
{
if (v___y_4910_ == 0)
{
lean_object* v_ks_4911_; lean_object* v_vs_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v_ks_4911_ = lean_ctor_get(v_newNode_4908_, 0);
lean_inc_ref(v_ks_4911_);
v_vs_4912_ = lean_ctor_get(v_newNode_4908_, 1);
lean_inc_ref(v_vs_4912_);
lean_dec_ref(v_newNode_4908_);
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__2);
v___x_4915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_4852_, v_ks_4911_, v_vs_4912_, v___x_4913_, v___x_4914_);
lean_dec_ref(v_vs_4912_);
lean_dec_ref(v_ks_4911_);
return v___x_4915_;
}
else
{
return v_newNode_4908_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_4923_, lean_object* v_keys_4924_, lean_object* v_vals_4925_, lean_object* v_i_4926_, lean_object* v_entries_4927_){
_start:
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4928_ = lean_array_get_size(v_keys_4924_);
v___x_4929_ = lean_nat_dec_lt(v_i_4926_, v___x_4928_);
if (v___x_4929_ == 0)
{
lean_dec(v_i_4926_);
return v_entries_4927_;
}
else
{
lean_object* v_k_4930_; lean_object* v_v_4931_; uint64_t v___x_4932_; size_t v_h_4933_; size_t v___x_4934_; lean_object* v___x_4935_; size_t v___x_4936_; size_t v___x_4937_; size_t v___x_4938_; size_t v_h_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v_k_4930_ = lean_array_fget_borrowed(v_keys_4924_, v_i_4926_);
v_v_4931_ = lean_array_fget_borrowed(v_vals_4925_, v_i_4926_);
v___x_4932_ = l_Lean_instHashableMVarId_hash(v_k_4930_);
v_h_4933_ = lean_uint64_to_usize(v___x_4932_);
v___x_4934_ = ((size_t)5ULL);
v___x_4935_ = lean_unsigned_to_nat(1u);
v___x_4936_ = ((size_t)1ULL);
v___x_4937_ = lean_usize_sub(v_depth_4923_, v___x_4936_);
v___x_4938_ = lean_usize_mul(v___x_4934_, v___x_4937_);
v_h_4939_ = lean_usize_shift_right(v_h_4933_, v___x_4938_);
v___x_4940_ = lean_nat_add(v_i_4926_, v___x_4935_);
lean_dec(v_i_4926_);
lean_inc(v_v_4931_);
lean_inc(v_k_4930_);
v___x_4941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_4927_, v_h_4939_, v_depth_4923_, v_k_4930_, v_v_4931_);
v_i_4926_ = v___x_4940_;
v_entries_4927_ = v___x_4941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_4943_, lean_object* v_keys_4944_, lean_object* v_vals_4945_, lean_object* v_i_4946_, lean_object* v_entries_4947_){
_start:
{
size_t v_depth_boxed_4948_; lean_object* v_res_4949_; 
v_depth_boxed_4948_ = lean_unbox_usize(v_depth_4943_);
lean_dec(v_depth_4943_);
v_res_4949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_4948_, v_keys_4944_, v_vals_4945_, v_i_4946_, v_entries_4947_);
lean_dec_ref(v_vals_4945_);
lean_dec_ref(v_keys_4944_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_4950_, lean_object* v_x_4951_, lean_object* v_x_4952_, lean_object* v_x_4953_, lean_object* v_x_4954_){
_start:
{
size_t v_x_91448__boxed_4955_; size_t v_x_91449__boxed_4956_; lean_object* v_res_4957_; 
v_x_91448__boxed_4955_ = lean_unbox_usize(v_x_4951_);
lean_dec(v_x_4951_);
v_x_91449__boxed_4956_ = lean_unbox_usize(v_x_4952_);
lean_dec(v_x_4952_);
v_res_4957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_4950_, v_x_91448__boxed_4955_, v_x_91449__boxed_4956_, v_x_4953_, v_x_4954_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_4958_, lean_object* v_x_4959_, lean_object* v_x_4960_){
_start:
{
uint64_t v___x_4961_; size_t v___x_4962_; size_t v___x_4963_; lean_object* v___x_4964_; 
v___x_4961_ = l_Lean_instHashableMVarId_hash(v_x_4959_);
v___x_4962_ = lean_uint64_to_usize(v___x_4961_);
v___x_4963_ = ((size_t)1ULL);
v___x_4964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_4958_, v___x_4962_, v___x_4963_, v_x_4959_, v_x_4960_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_4965_, lean_object* v_val_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v___x_4969_; lean_object* v_mctx_4970_; lean_object* v_cache_4971_; lean_object* v_zetaDeltaFVarIds_4972_; lean_object* v_postponed_4973_; lean_object* v_diag_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5002_; 
v___x_4969_ = lean_st_ref_take(v___y_4967_);
v_mctx_4970_ = lean_ctor_get(v___x_4969_, 0);
v_cache_4971_ = lean_ctor_get(v___x_4969_, 1);
v_zetaDeltaFVarIds_4972_ = lean_ctor_get(v___x_4969_, 2);
v_postponed_4973_ = lean_ctor_get(v___x_4969_, 3);
v_diag_4974_ = lean_ctor_get(v___x_4969_, 4);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4976_ = v___x_4969_;
v_isShared_4977_ = v_isSharedCheck_5002_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_diag_4974_);
lean_inc(v_postponed_4973_);
lean_inc(v_zetaDeltaFVarIds_4972_);
lean_inc(v_cache_4971_);
lean_inc(v_mctx_4970_);
lean_dec(v___x_4969_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5002_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v_depth_4978_; lean_object* v_levelAssignDepth_4979_; lean_object* v_lmvarCounter_4980_; lean_object* v_mvarCounter_4981_; lean_object* v_lDecls_4982_; lean_object* v_decls_4983_; lean_object* v_userNames_4984_; lean_object* v_lAssignment_4985_; lean_object* v_eAssignment_4986_; lean_object* v_dAssignment_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5001_; 
v_depth_4978_ = lean_ctor_get(v_mctx_4970_, 0);
v_levelAssignDepth_4979_ = lean_ctor_get(v_mctx_4970_, 1);
v_lmvarCounter_4980_ = lean_ctor_get(v_mctx_4970_, 2);
v_mvarCounter_4981_ = lean_ctor_get(v_mctx_4970_, 3);
v_lDecls_4982_ = lean_ctor_get(v_mctx_4970_, 4);
v_decls_4983_ = lean_ctor_get(v_mctx_4970_, 5);
v_userNames_4984_ = lean_ctor_get(v_mctx_4970_, 6);
v_lAssignment_4985_ = lean_ctor_get(v_mctx_4970_, 7);
v_eAssignment_4986_ = lean_ctor_get(v_mctx_4970_, 8);
v_dAssignment_4987_ = lean_ctor_get(v_mctx_4970_, 9);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_mctx_4970_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4989_ = v_mctx_4970_;
v_isShared_4990_ = v_isSharedCheck_5001_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_dAssignment_4987_);
lean_inc(v_eAssignment_4986_);
lean_inc(v_lAssignment_4985_);
lean_inc(v_userNames_4984_);
lean_inc(v_decls_4983_);
lean_inc(v_lDecls_4982_);
lean_inc(v_mvarCounter_4981_);
lean_inc(v_lmvarCounter_4980_);
lean_inc(v_levelAssignDepth_4979_);
lean_inc(v_depth_4978_);
lean_dec(v_mctx_4970_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5001_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4993_; 
v___x_4991_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_4986_, v_mvarId_4965_, v_val_4966_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 8, v___x_4991_);
v___x_4993_ = v___x_4989_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_depth_4978_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v_levelAssignDepth_4979_);
lean_ctor_set(v_reuseFailAlloc_5000_, 2, v_lmvarCounter_4980_);
lean_ctor_set(v_reuseFailAlloc_5000_, 3, v_mvarCounter_4981_);
lean_ctor_set(v_reuseFailAlloc_5000_, 4, v_lDecls_4982_);
lean_ctor_set(v_reuseFailAlloc_5000_, 5, v_decls_4983_);
lean_ctor_set(v_reuseFailAlloc_5000_, 6, v_userNames_4984_);
lean_ctor_set(v_reuseFailAlloc_5000_, 7, v_lAssignment_4985_);
lean_ctor_set(v_reuseFailAlloc_5000_, 8, v___x_4991_);
lean_ctor_set(v_reuseFailAlloc_5000_, 9, v_dAssignment_4987_);
v___x_4993_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
lean_object* v___x_4995_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4993_);
v___x_4995_ = v___x_4976_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4993_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_cache_4971_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v_zetaDeltaFVarIds_4972_);
lean_ctor_set(v_reuseFailAlloc_4999_, 3, v_postponed_4973_);
lean_ctor_set(v_reuseFailAlloc_4999_, 4, v_diag_4974_);
v___x_4995_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4996_ = lean_st_ref_set(v___y_4967_, v___x_4995_);
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4997_);
return v___x_4998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5003_, lean_object* v_val_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5003_, v_val_5004_, v___y_5005_);
lean_dec(v___y_5005_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5008_, lean_object* v_snd_5009_, uint8_t v_stopAtFirstFailure_5010_, lean_object* v_as_x27_5011_, lean_object* v_b_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
if (lean_obj_tag(v_as_x27_5011_) == 0)
{
lean_object* v___x_5023_; 
lean_dec_ref(v_snd_5009_);
lean_dec_ref(v_kp_5008_);
v___x_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5023_, 0, v_b_5012_);
return v___x_5023_;
}
else
{
lean_object* v_head_5024_; lean_object* v_tail_5025_; lean_object* v___x_5026_; 
v_head_5024_ = lean_ctor_get(v_as_x27_5011_, 0);
v_tail_5025_ = lean_ctor_get(v_as_x27_5011_, 1);
lean_inc_ref(v_kp_5008_);
lean_inc(v___y_5021_);
lean_inc_ref(v___y_5020_);
lean_inc(v___y_5019_);
lean_inc_ref(v___y_5018_);
lean_inc(v___y_5017_);
lean_inc_ref(v___y_5016_);
lean_inc(v___y_5015_);
lean_inc_ref(v___y_5014_);
lean_inc(v___y_5013_);
lean_inc(v_head_5024_);
v___x_5026_ = lean_apply_11(v_kp_5008_, v_head_5024_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, lean_box(0));
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_snd_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5122_; 
v_snd_5027_ = lean_ctor_get(v_b_5012_, 1);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_b_5012_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; 
v_unused_5123_ = lean_ctor_get(v_b_5012_, 0);
lean_dec(v_unused_5123_);
v___x_5029_ = v_b_5012_;
v_isShared_5030_ = v_isSharedCheck_5122_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_snd_5027_);
lean_dec(v_b_5012_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5122_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5121_; 
v_a_5031_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5033_ = v___x_5026_;
v_isShared_5034_ = v_isSharedCheck_5121_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5026_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5121_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v_fst_5035_; lean_object* v_snd_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5120_; 
v_fst_5035_ = lean_ctor_get(v_snd_5027_, 0);
v_snd_5036_ = lean_ctor_get(v_snd_5027_, 1);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_snd_5027_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5038_ = v_snd_5027_;
v_isShared_5039_ = v_isSharedCheck_5120_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_snd_5036_);
lean_inc(v_fst_5035_);
lean_dec(v_snd_5027_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5120_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5040_; 
v___x_5040_ = lean_box(0);
if (lean_obj_tag(v_a_5031_) == 0)
{
lean_object* v_seq_5041_; lean_object* v_mvarId_5042_; lean_object* v___x_5043_; 
lean_del_object(v___x_5033_);
v_seq_5041_ = lean_ctor_get(v_a_5031_, 0);
v_mvarId_5042_ = lean_ctor_get(v_head_5024_, 1);
lean_inc(v_mvarId_5042_);
v___x_5043_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5042_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref(v___x_5043_);
if (lean_obj_tag(v_a_5044_) == 1)
{
lean_object* v_val_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref(v_kp_5008_);
v_val_5045_ = lean_ctor_get(v_a_5044_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_a_5044_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5047_ = v_a_5044_;
v_isShared_5048_ = v_isSharedCheck_5076_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_val_5045_);
lean_dec(v_a_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5076_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v_mvarId_5049_; lean_object* v___x_5050_; 
v_mvarId_5049_ = lean_ctor_get(v_snd_5009_, 1);
lean_inc(v_mvarId_5049_);
lean_dec_ref(v_snd_5009_);
v___x_5050_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5049_, v_val_5045_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5066_; 
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v___x_5050_, 0);
lean_dec(v_unused_5067_);
v___x_5052_ = v___x_5050_;
v_isShared_5053_ = v_isSharedCheck_5066_;
goto v_resetjp_5051_;
}
else
{
lean_dec(v___x_5050_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5066_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v_a_5031_);
v___x_5055_ = v___x_5047_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5031_);
v___x_5055_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5057_; 
if (v_isShared_5039_ == 0)
{
v___x_5057_ = v___x_5038_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_snd_5036_);
v___x_5057_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
lean_object* v___x_5059_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5057_);
lean_ctor_set(v___x_5029_, 0, v___x_5055_);
v___x_5059_ = v___x_5029_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5055_);
lean_ctor_set(v_reuseFailAlloc_5063_, 1, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5061_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5059_);
v___x_5061_ = v___x_5052_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5059_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_del_object(v___x_5047_);
lean_dec_ref(v_a_5031_);
lean_del_object(v___x_5038_);
lean_dec(v_snd_5036_);
lean_dec(v_fst_5035_);
lean_del_object(v___x_5029_);
v_a_5068_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5050_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5050_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
else
{
uint8_t v___x_5077_; 
lean_inc(v_seq_5041_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5031_);
v___x_5077_ = l_List_isEmpty___redArg(v_seq_5041_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5078_ = lean_array_push(v_fst_5035_, v_seq_5041_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 0, v___x_5078_);
v___x_5080_ = v___x_5038_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_snd_5036_);
v___x_5080_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5082_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5080_);
lean_ctor_set(v___x_5029_, 0, v___x_5040_);
v___x_5082_ = v___x_5029_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5040_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
v_as_x27_5011_ = v_tail_5025_;
v_b_5012_ = v___x_5082_;
goto _start;
}
}
}
else
{
lean_object* v___x_5087_; 
lean_dec(v_seq_5041_);
if (v_isShared_5039_ == 0)
{
v___x_5087_ = v___x_5038_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v_snd_5036_);
v___x_5087_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5089_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5087_);
lean_ctor_set(v___x_5029_, 0, v___x_5040_);
v___x_5089_ = v___x_5029_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5040_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
v_as_x27_5011_ = v_tail_5025_;
v_b_5012_ = v___x_5089_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec_ref(v_a_5031_);
lean_del_object(v___x_5038_);
lean_dec(v_snd_5036_);
lean_dec(v_fst_5035_);
lean_del_object(v___x_5029_);
lean_dec_ref(v_snd_5009_);
lean_dec_ref(v_kp_5008_);
v_a_5093_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5043_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5043_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5010_ == 0)
{
lean_object* v_gs_5101_; lean_object* v___x_5102_; lean_object* v___x_5104_; 
lean_del_object(v___x_5033_);
v_gs_5101_ = lean_ctor_get(v_a_5031_, 0);
lean_inc(v_gs_5101_);
lean_dec_ref(v_a_5031_);
v___x_5102_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5036_, v_gs_5101_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 1, v___x_5102_);
v___x_5104_ = v___x_5038_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5106_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5104_);
lean_ctor_set(v___x_5029_, 0, v___x_5040_);
v___x_5106_ = v___x_5029_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5040_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___x_5104_);
v___x_5106_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
v_as_x27_5011_ = v_tail_5025_;
v_b_5012_ = v___x_5106_;
goto _start;
}
}
}
else
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
lean_dec_ref(v_snd_5009_);
lean_dec_ref(v_kp_5008_);
v___x_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5110_, 0, v_a_5031_);
if (v_isShared_5039_ == 0)
{
v___x_5112_ = v___x_5038_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_fst_5035_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_snd_5036_);
v___x_5112_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
lean_object* v___x_5114_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5112_);
lean_ctor_set(v___x_5029_, 0, v___x_5110_);
v___x_5114_ = v___x_5029_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v___x_5112_);
v___x_5114_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
lean_object* v___x_5116_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 0, v___x_5114_);
v___x_5116_ = v___x_5033_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5114_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
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
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
lean_dec_ref(v_b_5012_);
lean_dec_ref(v_snd_5009_);
lean_dec_ref(v_kp_5008_);
v_a_5124_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5026_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5026_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5132_, lean_object* v_snd_5133_, lean_object* v_stopAtFirstFailure_5134_, lean_object* v_as_x27_5135_, lean_object* v_b_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5147_; lean_object* v_res_5148_; 
v_stopAtFirstFailure_boxed_5147_ = lean_unbox(v_stopAtFirstFailure_5134_);
v_res_5148_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5132_, v_snd_5133_, v_stopAtFirstFailure_boxed_5147_, v_as_x27_5135_, v_b_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec(v_as_x27_5135_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5149_, lean_object* v_c_5150_, lean_object* v___x_5151_, lean_object* v___x_5152_, uint8_t v_isRec_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
if (lean_obj_tag(v_a_5154_) == 0)
{
lean_object* v___x_5156_; 
lean_dec(v___x_5152_);
lean_dec_ref(v___x_5151_);
lean_dec_ref(v_snd_5149_);
v___x_5156_ = lean_array_to_list(v_a_5155_);
return v___x_5156_;
}
else
{
lean_object* v_toGoalState_5157_; lean_object* v_split_5158_; lean_object* v_head_5159_; lean_object* v_tail_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5221_; 
v_toGoalState_5157_ = lean_ctor_get(v_snd_5149_, 0);
lean_inc_ref(v_toGoalState_5157_);
v_split_5158_ = lean_ctor_get(v_toGoalState_5157_, 14);
lean_inc_ref(v_split_5158_);
v_head_5159_ = lean_ctor_get(v_a_5154_, 0);
v_tail_5160_ = lean_ctor_get(v_a_5154_, 1);
v_isSharedCheck_5221_ = !lean_is_exclusive(v_a_5154_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5162_ = v_a_5154_;
v_isShared_5163_ = v_isSharedCheck_5221_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_tail_5160_);
lean_inc(v_head_5159_);
lean_dec(v_a_5154_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5221_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v_nextDeclIdx_5164_; lean_object* v_enodeMap_5165_; lean_object* v_exprs_5166_; lean_object* v_parents_5167_; lean_object* v_congrTable_5168_; lean_object* v_appMap_5169_; lean_object* v_indicesFound_5170_; lean_object* v_newFacts_5171_; uint8_t v_inconsistent_5172_; lean_object* v_nextIdx_5173_; lean_object* v_newRawFacts_5174_; lean_object* v_facts_5175_; lean_object* v_extThms_5176_; lean_object* v_ematch_5177_; lean_object* v_inj_5178_; lean_object* v_clean_5179_; lean_object* v_sstates_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5219_; 
v_nextDeclIdx_5164_ = lean_ctor_get(v_toGoalState_5157_, 0);
v_enodeMap_5165_ = lean_ctor_get(v_toGoalState_5157_, 1);
v_exprs_5166_ = lean_ctor_get(v_toGoalState_5157_, 2);
v_parents_5167_ = lean_ctor_get(v_toGoalState_5157_, 3);
v_congrTable_5168_ = lean_ctor_get(v_toGoalState_5157_, 4);
v_appMap_5169_ = lean_ctor_get(v_toGoalState_5157_, 5);
v_indicesFound_5170_ = lean_ctor_get(v_toGoalState_5157_, 6);
v_newFacts_5171_ = lean_ctor_get(v_toGoalState_5157_, 7);
v_inconsistent_5172_ = lean_ctor_get_uint8(v_toGoalState_5157_, sizeof(void*)*17);
v_nextIdx_5173_ = lean_ctor_get(v_toGoalState_5157_, 8);
v_newRawFacts_5174_ = lean_ctor_get(v_toGoalState_5157_, 9);
v_facts_5175_ = lean_ctor_get(v_toGoalState_5157_, 10);
v_extThms_5176_ = lean_ctor_get(v_toGoalState_5157_, 11);
v_ematch_5177_ = lean_ctor_get(v_toGoalState_5157_, 12);
v_inj_5178_ = lean_ctor_get(v_toGoalState_5157_, 13);
v_clean_5179_ = lean_ctor_get(v_toGoalState_5157_, 15);
v_sstates_5180_ = lean_ctor_get(v_toGoalState_5157_, 16);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_toGoalState_5157_);
if (v_isSharedCheck_5219_ == 0)
{
lean_object* v_unused_5220_; 
v_unused_5220_ = lean_ctor_get(v_toGoalState_5157_, 14);
lean_dec(v_unused_5220_);
v___x_5182_ = v_toGoalState_5157_;
v_isShared_5183_ = v_isSharedCheck_5219_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_sstates_5180_);
lean_inc(v_clean_5179_);
lean_inc(v_inj_5178_);
lean_inc(v_ematch_5177_);
lean_inc(v_extThms_5176_);
lean_inc(v_facts_5175_);
lean_inc(v_newRawFacts_5174_);
lean_inc(v_nextIdx_5173_);
lean_inc(v_newFacts_5171_);
lean_inc(v_indicesFound_5170_);
lean_inc(v_appMap_5169_);
lean_inc(v_congrTable_5168_);
lean_inc(v_parents_5167_);
lean_inc(v_exprs_5166_);
lean_inc(v_enodeMap_5165_);
lean_inc(v_nextDeclIdx_5164_);
lean_dec(v_toGoalState_5157_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5219_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v_num_5184_; lean_object* v_candidates_5185_; lean_object* v_added_5186_; lean_object* v_resolved_5187_; lean_object* v_trace_5188_; lean_object* v_lookaheads_5189_; lean_object* v_argPosMap_5190_; lean_object* v_argsAt_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5218_; 
v_num_5184_ = lean_ctor_get(v_split_5158_, 0);
v_candidates_5185_ = lean_ctor_get(v_split_5158_, 1);
v_added_5186_ = lean_ctor_get(v_split_5158_, 2);
v_resolved_5187_ = lean_ctor_get(v_split_5158_, 3);
v_trace_5188_ = lean_ctor_get(v_split_5158_, 4);
v_lookaheads_5189_ = lean_ctor_get(v_split_5158_, 5);
v_argPosMap_5190_ = lean_ctor_get(v_split_5158_, 6);
v_argsAt_5191_ = lean_ctor_get(v_split_5158_, 7);
v_isSharedCheck_5218_ = !lean_is_exclusive(v_split_5158_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5193_ = v_split_5158_;
v_isShared_5194_ = v_isSharedCheck_5218_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_argsAt_5191_);
lean_inc(v_argPosMap_5190_);
lean_inc(v_lookaheads_5189_);
lean_inc(v_trace_5188_);
lean_inc(v_resolved_5187_);
lean_inc(v_added_5186_);
lean_inc(v_candidates_5185_);
lean_inc(v_num_5184_);
lean_dec(v_split_5158_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5218_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5195_; lean_object* v___y_5197_; uint8_t v___y_5213_; lean_object* v___x_5216_; uint8_t v___x_5217_; 
v___x_5195_ = lean_array_get_size(v_a_5155_);
v___x_5216_ = lean_unsigned_to_nat(0u);
v___x_5217_ = lean_nat_dec_lt(v___x_5216_, v___x_5195_);
if (v___x_5217_ == 0)
{
v___y_5213_ = v_isRec_5153_;
goto v___jp_5212_;
}
else
{
v___y_5213_ = v___x_5217_;
goto v___jp_5212_;
}
v___jp_5196_:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5201_; 
v___x_5198_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5150_);
lean_inc(v___x_5152_);
lean_inc_ref(v___x_5151_);
v___x_5199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5151_);
lean_ctor_set(v___x_5199_, 1, v___x_5195_);
lean_ctor_set(v___x_5199_, 2, v___x_5152_);
lean_ctor_set(v___x_5199_, 3, v___x_5198_);
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 1, v_trace_5188_);
lean_ctor_set(v___x_5162_, 0, v___x_5199_);
v___x_5201_ = v___x_5162_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5199_);
lean_ctor_set(v_reuseFailAlloc_5211_, 1, v_trace_5188_);
v___x_5201_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5203_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 4, v___x_5201_);
lean_ctor_set(v___x_5193_, 0, v___y_5197_);
v___x_5203_ = v___x_5193_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___y_5197_);
lean_ctor_set(v_reuseFailAlloc_5210_, 1, v_candidates_5185_);
lean_ctor_set(v_reuseFailAlloc_5210_, 2, v_added_5186_);
lean_ctor_set(v_reuseFailAlloc_5210_, 3, v_resolved_5187_);
lean_ctor_set(v_reuseFailAlloc_5210_, 4, v___x_5201_);
lean_ctor_set(v_reuseFailAlloc_5210_, 5, v_lookaheads_5189_);
lean_ctor_set(v_reuseFailAlloc_5210_, 6, v_argPosMap_5190_);
lean_ctor_set(v_reuseFailAlloc_5210_, 7, v_argsAt_5191_);
v___x_5203_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5205_; 
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 14, v___x_5203_);
v___x_5205_ = v___x_5182_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_nextDeclIdx_5164_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_enodeMap_5165_);
lean_ctor_set(v_reuseFailAlloc_5209_, 2, v_exprs_5166_);
lean_ctor_set(v_reuseFailAlloc_5209_, 3, v_parents_5167_);
lean_ctor_set(v_reuseFailAlloc_5209_, 4, v_congrTable_5168_);
lean_ctor_set(v_reuseFailAlloc_5209_, 5, v_appMap_5169_);
lean_ctor_set(v_reuseFailAlloc_5209_, 6, v_indicesFound_5170_);
lean_ctor_set(v_reuseFailAlloc_5209_, 7, v_newFacts_5171_);
lean_ctor_set(v_reuseFailAlloc_5209_, 8, v_nextIdx_5173_);
lean_ctor_set(v_reuseFailAlloc_5209_, 9, v_newRawFacts_5174_);
lean_ctor_set(v_reuseFailAlloc_5209_, 10, v_facts_5175_);
lean_ctor_set(v_reuseFailAlloc_5209_, 11, v_extThms_5176_);
lean_ctor_set(v_reuseFailAlloc_5209_, 12, v_ematch_5177_);
lean_ctor_set(v_reuseFailAlloc_5209_, 13, v_inj_5178_);
lean_ctor_set(v_reuseFailAlloc_5209_, 14, v___x_5203_);
lean_ctor_set(v_reuseFailAlloc_5209_, 15, v_clean_5179_);
lean_ctor_set(v_reuseFailAlloc_5209_, 16, v_sstates_5180_);
lean_ctor_set_uint8(v_reuseFailAlloc_5209_, sizeof(void*)*17, v_inconsistent_5172_);
v___x_5205_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5205_);
lean_ctor_set(v___x_5206_, 1, v_head_5159_);
v___x_5207_ = lean_array_push(v_a_5155_, v___x_5206_);
v_a_5154_ = v_tail_5160_;
v_a_5155_ = v___x_5207_;
goto _start;
}
}
}
}
v___jp_5212_:
{
if (v___y_5213_ == 0)
{
v___y_5197_ = v_num_5184_;
goto v___jp_5196_;
}
else
{
lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5214_ = lean_unsigned_to_nat(1u);
v___x_5215_ = lean_nat_add(v_num_5184_, v___x_5214_);
lean_dec(v_num_5184_);
v___y_5197_ = v___x_5215_;
goto v___jp_5196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5222_, lean_object* v_c_5223_, lean_object* v___x_5224_, lean_object* v___x_5225_, lean_object* v_isRec_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
uint8_t v_isRec_boxed_5229_; lean_object* v_res_5230_; 
v_isRec_boxed_5229_ = lean_unbox(v_isRec_5226_);
v_res_5230_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5222_, v_c_5223_, v___x_5224_, v___x_5225_, v_isRec_boxed_5229_, v_a_5227_, v_a_5228_);
lean_dec_ref(v_c_5223_);
return v_res_5230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9(void){
_start:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v___x_5256_ = lean_box(0);
v___x_5257_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__8));
v___x_5258_ = l_Lean_mkConst(v___x_5257_, v___x_5256_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5259_, lean_object* v_numCases_5260_, uint8_t v_isRec_5261_, uint8_t v_stopAtFirstFailure_5262_, uint8_t v_compress_5263_, lean_object* v_goal_5264_, lean_object* v_kp_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_){
_start:
{
lean_object* v___x_5276_; 
v___x_5276_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5267_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5278_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc(v_a_5277_);
lean_dec_ref(v___x_5276_);
lean_inc_ref(v_goal_5264_);
v___x_5278_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5264_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; uint8_t v_trace_5280_; lean_object* v_mvarId_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___f_5285_; lean_object* v___x_5286_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
lean_inc_n(v_a_5279_, 2);
lean_dec_ref(v___x_5278_);
v_trace_5280_ = lean_ctor_get_uint8(v_a_5277_, sizeof(void*)*11);
lean_dec(v_a_5277_);
v_mvarId_5281_ = lean_ctor_get(v_goal_5264_, 1);
lean_inc(v_mvarId_5281_);
v___x_5282_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5259_);
v___x_5283_ = lean_box(v_trace_5280_);
v___x_5284_ = lean_box(v_isRec_5261_);
lean_inc_ref(v_c_5259_);
lean_inc_ref(v___x_5282_);
v___f_5285_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 17, 7);
lean_closure_set(v___f_5285_, 0, v_goal_5264_);
lean_closure_set(v___f_5285_, 1, v___x_5282_);
lean_closure_set(v___f_5285_, 2, v___x_5283_);
lean_closure_set(v___f_5285_, 3, v_c_5259_);
lean_closure_set(v___f_5285_, 4, v_a_5279_);
lean_closure_set(v___f_5285_, 5, v_numCases_5260_);
lean_closure_set(v___f_5285_, 6, v___x_5284_);
v___x_5286_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5281_, v___f_5285_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v_fst_5288_; lean_object* v_snd_5289_; lean_object* v_fst_5290_; lean_object* v_snd_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_a_5287_);
lean_dec_ref(v___x_5286_);
v_fst_5288_ = lean_ctor_get(v_a_5287_, 0);
lean_inc(v_fst_5288_);
v_snd_5289_ = lean_ctor_get(v_a_5287_, 1);
lean_inc_n(v_snd_5289_, 3);
lean_dec(v_a_5287_);
v_fst_5290_ = lean_ctor_get(v_fst_5288_, 0);
lean_inc(v_fst_5290_);
v_snd_5291_ = lean_ctor_get(v_fst_5288_, 1);
lean_inc(v_snd_5291_);
lean_dec(v_fst_5288_);
v___x_5292_ = l_List_lengthTR___redArg(v_fst_5290_);
v___x_5293_ = lean_unsigned_to_nat(0u);
v___x_5294_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
lean_inc_ref(v___x_5282_);
v___x_5295_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5289_, v_c_5259_, v___x_5282_, v___x_5292_, v_isRec_5261_, v_fst_5290_, v___x_5294_);
lean_dec_ref(v_c_5259_);
v___x_5296_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5297_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5265_, v_snd_5289_, v_stopAtFirstFailure_5262_, v___x_5295_, v___x_5296_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
lean_dec(v___x_5295_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5412_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5300_ = v___x_5297_;
v_isShared_5301_ = v_isSharedCheck_5412_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5297_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5412_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v_fst_5302_; 
v_fst_5302_ = lean_ctor_get(v_a_5298_, 0);
if (lean_obj_tag(v_fst_5302_) == 0)
{
lean_object* v_snd_5303_; lean_object* v_mvarId_5304_; lean_object* v___x_5305_; 
lean_del_object(v___x_5300_);
v_snd_5303_ = lean_ctor_get(v_a_5298_, 1);
lean_inc(v_snd_5303_);
lean_dec(v_a_5298_);
v_mvarId_5304_ = lean_ctor_get(v_snd_5289_, 1);
lean_inc_n(v_mvarId_5304_, 2);
lean_dec(v_snd_5289_);
v___x_5305_ = l_Lean_MVarId_getType(v_mvarId_5304_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5399_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5399_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5308_ = v___x_5305_;
v_isShared_5309_ = v_isSharedCheck_5399_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5399_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v_fst_5310_; lean_object* v_snd_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5398_; 
v_fst_5310_ = lean_ctor_get(v_snd_5303_, 0);
v_snd_5311_ = lean_ctor_get(v_snd_5303_, 1);
v_isSharedCheck_5398_ = !lean_is_exclusive(v_snd_5303_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5313_ = v_snd_5303_;
v_isShared_5314_ = v_isSharedCheck_5398_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_snd_5311_);
lean_inc(v_fst_5310_);
lean_dec(v_snd_5303_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5398_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___y_5316_; lean_object* v___y_5317_; lean_object* v___y_5318_; lean_object* v___y_5319_; lean_object* v___y_5320_; lean_object* v___y_5321_; lean_object* v___y_5322_; lean_object* v___y_5323_; lean_object* v___y_5324_; uint8_t v___x_5387_; 
v___x_5387_ = l_Lean_Expr_isFalse(v_a_5306_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v_a_5390_; lean_object* v___x_5391_; 
v___x_5388_ = l_Lean_mkMVar(v_a_5279_);
v___x_5389_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5388_, v_a_5272_);
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
lean_inc(v_a_5390_);
lean_dec_ref(v___x_5389_);
lean_inc(v_mvarId_5304_);
v___x_5391_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5304_, v_a_5390_, v_a_5272_);
lean_dec_ref(v___x_5391_);
v___y_5316_ = v_a_5266_;
v___y_5317_ = v_a_5267_;
v___y_5318_ = v_a_5268_;
v___y_5319_ = v_a_5269_;
v___y_5320_ = v_a_5270_;
v___y_5321_ = v_a_5271_;
v___y_5322_ = v_a_5272_;
v___y_5323_ = v_a_5273_;
v___y_5324_ = v_a_5274_;
goto v___jp_5315_;
}
else
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v_a_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5392_ = l_Lean_mkMVar(v_a_5279_);
v___x_5393_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5392_, v_a_5272_);
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref(v___x_5393_);
v___x_5395_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__9);
v___x_5396_ = l_Lean_Meta_mkExpectedPropHint(v_a_5394_, v___x_5395_);
lean_inc(v_mvarId_5304_);
v___x_5397_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5304_, v___x_5396_, v_a_5272_);
lean_dec_ref(v___x_5397_);
v___y_5316_ = v_a_5266_;
v___y_5317_ = v_a_5267_;
v___y_5318_ = v_a_5268_;
v___y_5319_ = v_a_5269_;
v___y_5320_ = v_a_5270_;
v___y_5321_ = v_a_5271_;
v___y_5322_ = v_a_5272_;
v___y_5323_ = v_a_5273_;
v___y_5324_ = v_a_5274_;
goto v___jp_5315_;
}
v___jp_5315_:
{
lean_object* v___x_5325_; uint8_t v___x_5326_; 
v___x_5325_ = lean_array_get_size(v_snd_5311_);
v___x_5326_ = lean_nat_dec_eq(v___x_5325_, v___x_5293_);
if (v___x_5326_ == 0)
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_dec(v_mvarId_5304_);
lean_dec(v_snd_5291_);
lean_dec_ref(v___x_5282_);
v___x_5327_ = lean_array_to_list(v_snd_5311_);
v___x_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5327_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5328_);
v___x_5330_ = v___x_5308_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
else
{
lean_dec(v_snd_5311_);
if (v_trace_5280_ == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5334_; 
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_dec(v_mvarId_5304_);
lean_dec(v_snd_5291_);
lean_dec_ref(v___x_5282_);
v___x_5332_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5332_);
v___x_5334_ = v___x_5308_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
else
{
lean_object* v___x_5336_; lean_object* v___x_5337_; 
lean_del_object(v___x_5308_);
v___x_5336_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_5336_, 0, v___x_5282_);
v___x_5337_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5304_, v___x_5336_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; uint64_t v___x_5339_; lean_object* v___x_5340_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
lean_inc(v_a_5338_);
lean_dec_ref(v___x_5337_);
v___x_5339_ = lean_unbox_uint64(v_a_5338_);
lean_dec(v_a_5338_);
v___x_5340_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_snd_5291_, v___x_5339_, v___y_5323_);
lean_dec(v_snd_5291_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; lean_object* v_ref_5342_; uint8_t v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref(v___x_5340_);
v_ref_5342_ = lean_ctor_get(v___y_5323_, 5);
v___x_5343_ = 0;
v___x_5344_ = l_Lean_SourceInfo_fromRef(v_ref_5342_, v___x_5343_);
v___x_5345_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5346_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5));
lean_inc(v___x_5344_);
if (v_isShared_5314_ == 0)
{
lean_ctor_set_tag(v___x_5313_, 2);
lean_ctor_set(v___x_5313_, 1, v___x_5345_);
lean_ctor_set(v___x_5313_, 0, v___x_5344_);
v___x_5348_ = v___x_5313_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v___x_5345_);
v___x_5348_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5349_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__7));
lean_inc(v___x_5344_);
v___x_5350_ = l_Lean_Syntax_node1(v___x_5344_, v___x_5349_, v_a_5341_);
v___x_5351_ = l_Lean_Syntax_node2(v___x_5344_, v___x_5346_, v___x_5348_, v___x_5350_);
v___x_5352_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v___x_5351_, v_fst_5310_, v_compress_5263_, v___y_5323_, v___y_5324_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5361_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5361_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5361_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v___x_5359_; 
v___x_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5357_, 0, v_a_5353_);
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 0, v___x_5357_);
v___x_5359_ = v___x_5355_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v___x_5357_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
v_a_5362_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5352_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5352_);
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
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
v_a_5371_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5340_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5340_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
else
{
lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
lean_del_object(v___x_5313_);
lean_dec(v_fst_5310_);
lean_dec(v_snd_5291_);
v_a_5379_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5337_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5337_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
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
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec(v_mvarId_5304_);
lean_dec(v_snd_5303_);
lean_dec(v_snd_5291_);
lean_dec_ref(v___x_5282_);
lean_dec(v_a_5279_);
v_a_5400_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5305_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5305_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
else
{
lean_object* v_val_5408_; lean_object* v___x_5410_; 
lean_inc_ref(v_fst_5302_);
lean_dec(v_a_5298_);
lean_dec(v_snd_5291_);
lean_dec(v_snd_5289_);
lean_dec_ref(v___x_5282_);
lean_dec(v_a_5279_);
v_val_5408_ = lean_ctor_get(v_fst_5302_, 0);
lean_inc(v_val_5408_);
lean_dec_ref(v_fst_5302_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 0, v_val_5408_);
v___x_5410_ = v___x_5300_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_val_5408_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
else
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
lean_dec(v_snd_5291_);
lean_dec(v_snd_5289_);
lean_dec_ref(v___x_5282_);
lean_dec(v_a_5279_);
v_a_5413_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5297_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5297_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
lean_dec_ref(v___x_5282_);
lean_dec(v_a_5279_);
lean_dec_ref(v_kp_5265_);
lean_dec_ref(v_c_5259_);
v_a_5421_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5286_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5286_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec(v_a_5277_);
lean_dec_ref(v_kp_5265_);
lean_dec_ref(v_goal_5264_);
lean_dec(v_numCases_5260_);
lean_dec_ref(v_c_5259_);
v_a_5429_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5278_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5278_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_dec_ref(v_kp_5265_);
lean_dec_ref(v_goal_5264_);
lean_dec(v_numCases_5260_);
lean_dec_ref(v_c_5259_);
v_a_5437_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5276_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5276_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5445_ = _args[0];
lean_object* v_numCases_5446_ = _args[1];
lean_object* v_isRec_5447_ = _args[2];
lean_object* v_stopAtFirstFailure_5448_ = _args[3];
lean_object* v_compress_5449_ = _args[4];
lean_object* v_goal_5450_ = _args[5];
lean_object* v_kp_5451_ = _args[6];
lean_object* v_a_5452_ = _args[7];
lean_object* v_a_5453_ = _args[8];
lean_object* v_a_5454_ = _args[9];
lean_object* v_a_5455_ = _args[10];
lean_object* v_a_5456_ = _args[11];
lean_object* v_a_5457_ = _args[12];
lean_object* v_a_5458_ = _args[13];
lean_object* v_a_5459_ = _args[14];
lean_object* v_a_5460_ = _args[15];
lean_object* v_a_5461_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5462_; uint8_t v_stopAtFirstFailure_boxed_5463_; uint8_t v_compress_boxed_5464_; lean_object* v_res_5465_; 
v_isRec_boxed_5462_ = lean_unbox(v_isRec_5447_);
v_stopAtFirstFailure_boxed_5463_ = lean_unbox(v_stopAtFirstFailure_5448_);
v_compress_boxed_5464_ = lean_unbox(v_compress_5449_);
v_res_5465_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5445_, v_numCases_5446_, v_isRec_boxed_5462_, v_stopAtFirstFailure_boxed_5463_, v_compress_boxed_5464_, v_goal_5450_, v_kp_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_);
lean_dec(v_a_5460_);
lean_dec_ref(v_a_5459_);
lean_dec(v_a_5458_);
lean_dec_ref(v_a_5457_);
lean_dec(v_a_5456_);
lean_dec_ref(v_a_5455_);
lean_dec(v_a_5454_);
lean_dec_ref(v_a_5453_);
lean_dec(v_a_5452_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5466_, lean_object* v_numCases_5467_, uint8_t v_isRec_5468_, uint8_t v_stopAtFirstFailure_5469_, uint8_t v_compress_5470_, lean_object* v_goal_5471_, lean_object* v_x_5472_, lean_object* v_kp_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_){
_start:
{
lean_object* v___x_5484_; 
v___x_5484_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5466_, v_numCases_5467_, v_isRec_5468_, v_stopAtFirstFailure_5469_, v_compress_5470_, v_goal_5471_, v_kp_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5485_ = _args[0];
lean_object* v_numCases_5486_ = _args[1];
lean_object* v_isRec_5487_ = _args[2];
lean_object* v_stopAtFirstFailure_5488_ = _args[3];
lean_object* v_compress_5489_ = _args[4];
lean_object* v_goal_5490_ = _args[5];
lean_object* v_x_5491_ = _args[6];
lean_object* v_kp_5492_ = _args[7];
lean_object* v_a_5493_ = _args[8];
lean_object* v_a_5494_ = _args[9];
lean_object* v_a_5495_ = _args[10];
lean_object* v_a_5496_ = _args[11];
lean_object* v_a_5497_ = _args[12];
lean_object* v_a_5498_ = _args[13];
lean_object* v_a_5499_ = _args[14];
lean_object* v_a_5500_ = _args[15];
lean_object* v_a_5501_ = _args[16];
lean_object* v_a_5502_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5503_; uint8_t v_stopAtFirstFailure_boxed_5504_; uint8_t v_compress_boxed_5505_; lean_object* v_res_5506_; 
v_isRec_boxed_5503_ = lean_unbox(v_isRec_5487_);
v_stopAtFirstFailure_boxed_5504_ = lean_unbox(v_stopAtFirstFailure_5488_);
v_compress_boxed_5505_ = lean_unbox(v_compress_5489_);
v_res_5506_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5485_, v_numCases_5486_, v_isRec_boxed_5503_, v_stopAtFirstFailure_boxed_5504_, v_compress_boxed_5505_, v_goal_5490_, v_x_5491_, v_kp_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
lean_dec(v_a_5499_);
lean_dec_ref(v_a_5498_);
lean_dec(v_a_5497_);
lean_dec_ref(v_a_5496_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec_ref(v_x_5491_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5507_, lean_object* v_snd_5508_, uint8_t v_stopAtFirstFailure_5509_, lean_object* v_as_5510_, lean_object* v_as_x27_5511_, lean_object* v_b_5512_, lean_object* v_a_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v___x_5524_; 
v___x_5524_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5507_, v_snd_5508_, v_stopAtFirstFailure_5509_, v_as_x27_5511_, v_b_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5525_ = _args[0];
lean_object* v_snd_5526_ = _args[1];
lean_object* v_stopAtFirstFailure_5527_ = _args[2];
lean_object* v_as_5528_ = _args[3];
lean_object* v_as_x27_5529_ = _args[4];
lean_object* v_b_5530_ = _args[5];
lean_object* v_a_5531_ = _args[6];
lean_object* v___y_5532_ = _args[7];
lean_object* v___y_5533_ = _args[8];
lean_object* v___y_5534_ = _args[9];
lean_object* v___y_5535_ = _args[10];
lean_object* v___y_5536_ = _args[11];
lean_object* v___y_5537_ = _args[12];
lean_object* v___y_5538_ = _args[13];
lean_object* v___y_5539_ = _args[14];
lean_object* v___y_5540_ = _args[15];
lean_object* v___y_5541_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5542_; lean_object* v_res_5543_; 
v_stopAtFirstFailure_boxed_5542_ = lean_unbox(v_stopAtFirstFailure_5527_);
v_res_5543_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5525_, v_snd_5526_, v_stopAtFirstFailure_boxed_5542_, v_as_5528_, v_as_x27_5529_, v_b_5530_, v_a_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
lean_dec(v___y_5532_);
lean_dec(v_as_x27_5529_);
lean_dec(v_as_5528_);
return v_res_5543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_5544_, lean_object* v_val_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_){
_start:
{
lean_object* v___x_5556_; 
v___x_5556_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5544_, v_val_5545_, v___y_5552_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_5557_, lean_object* v_val_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_){
_start:
{
lean_object* v_res_5569_; 
v_res_5569_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_5557_, v_val_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
return v_res_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_5570_, lean_object* v_x_5571_, lean_object* v_x_5572_, lean_object* v_x_5573_){
_start:
{
lean_object* v___x_5574_; 
v___x_5574_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_5571_, v_x_5572_, v_x_5573_);
return v___x_5574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_5575_, lean_object* v_x_5576_, size_t v_x_5577_, size_t v_x_5578_, lean_object* v_x_5579_, lean_object* v_x_5580_){
_start:
{
lean_object* v___x_5581_; 
v___x_5581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5576_, v_x_5577_, v_x_5578_, v_x_5579_, v_x_5580_);
return v___x_5581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_5582_, lean_object* v_x_5583_, lean_object* v_x_5584_, lean_object* v_x_5585_, lean_object* v_x_5586_, lean_object* v_x_5587_){
_start:
{
size_t v_x_92511__boxed_5588_; size_t v_x_92512__boxed_5589_; lean_object* v_res_5590_; 
v_x_92511__boxed_5588_ = lean_unbox_usize(v_x_5584_);
lean_dec(v_x_5584_);
v_x_92512__boxed_5589_ = lean_unbox_usize(v_x_5585_);
lean_dec(v_x_5585_);
v_res_5590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_5582_, v_x_5583_, v_x_92511__boxed_5588_, v_x_92512__boxed_5589_, v_x_5586_, v_x_5587_);
return v_res_5590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_5591_, lean_object* v_n_5592_, lean_object* v_k_5593_, lean_object* v_v_5594_){
_start:
{
lean_object* v___x_5595_; 
v___x_5595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_5592_, v_k_5593_, v_v_5594_);
return v___x_5595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_5596_, size_t v_depth_5597_, lean_object* v_keys_5598_, lean_object* v_vals_5599_, lean_object* v_heq_5600_, lean_object* v_i_5601_, lean_object* v_entries_5602_){
_start:
{
lean_object* v___x_5603_; 
v___x_5603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_5597_, v_keys_5598_, v_vals_5599_, v_i_5601_, v_entries_5602_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_5604_, lean_object* v_depth_5605_, lean_object* v_keys_5606_, lean_object* v_vals_5607_, lean_object* v_heq_5608_, lean_object* v_i_5609_, lean_object* v_entries_5610_){
_start:
{
size_t v_depth_boxed_5611_; lean_object* v_res_5612_; 
v_depth_boxed_5611_ = lean_unbox_usize(v_depth_5605_);
lean_dec(v_depth_5605_);
v_res_5612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_5604_, v_depth_boxed_5611_, v_keys_5606_, v_vals_5607_, v_heq_5608_, v_i_5609_, v_entries_5610_);
lean_dec_ref(v_vals_5607_);
lean_dec_ref(v_keys_5606_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_5613_, lean_object* v_x_5614_, lean_object* v_x_5615_, lean_object* v_x_5616_, lean_object* v_x_5617_){
_start:
{
lean_object* v___x_5618_; 
v___x_5618_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_5614_, v_x_5615_, v_x_5616_, v_x_5617_);
return v___x_5618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_st_mk_ref(v_goal_5619_);
v___x_5631_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_5630_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5641_; 
v_a_5632_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5634_ = v___x_5631_;
v_isShared_5635_ = v_isSharedCheck_5641_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5631_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5641_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5639_; 
v___x_5636_ = lean_st_ref_get(v___x_5630_);
lean_dec(v___x_5630_);
v___x_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5637_, 0, v_a_5632_);
lean_ctor_set(v___x_5637_, 1, v___x_5636_);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 0, v___x_5637_);
v___x_5639_ = v___x_5634_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v___x_5637_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
lean_dec(v___x_5630_);
v_a_5642_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5631_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5631_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v___y_5655_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___y_5651_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_5662_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5677_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_5690_, lean_object* v___f_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5705_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_5705_, 0, v___y_5690_);
v___x_5706_ = l_Lean_Meta_Grind_Action_andThen(v___x_5705_, v___f_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_);
return v___x_5706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_5707_, lean_object* v___f_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
lean_object* v_res_5722_; 
v_res_5722_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_5707_, v___f_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
return v_res_5722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_5724_, uint8_t v_compress_5725_, lean_object* v_goal_5726_, lean_object* v_kna_5727_, lean_object* v_kp_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_){
_start:
{
lean_object* v_mvarId_5739_; lean_object* v___f_5740_; lean_object* v___x_5741_; 
v_mvarId_5739_ = lean_ctor_get(v_goal_5726_, 1);
lean_inc(v_mvarId_5739_);
v___f_5740_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5740_, 0, v_goal_5726_);
v___x_5741_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5739_, v___f_5740_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_object* v_a_5742_; lean_object* v_fst_5743_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref(v___x_5741_);
v_fst_5743_ = lean_ctor_get(v_a_5742_, 0);
if (lean_obj_tag(v_fst_5743_) == 1)
{
lean_object* v_snd_5744_; lean_object* v_c_5745_; lean_object* v_numCases_5746_; uint8_t v_isRec_5747_; lean_object* v___f_5748_; lean_object* v___y_5750_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; uint8_t v___y_5761_; uint8_t v___x_5763_; 
lean_inc_ref(v_fst_5743_);
v_snd_5744_ = lean_ctor_get(v_a_5742_, 1);
lean_inc(v_snd_5744_);
lean_dec(v_a_5742_);
v_c_5745_ = lean_ctor_get(v_fst_5743_, 0);
lean_inc_ref(v_c_5745_);
v_numCases_5746_ = lean_ctor_get(v_fst_5743_, 1);
lean_inc(v_numCases_5746_);
v_isRec_5747_ = lean_ctor_get_uint8(v_fst_5743_, sizeof(void*)*2);
lean_dec_ref(v_fst_5743_);
v___f_5748_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_5757_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5745_);
v___x_5758_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_5744_, v___x_5757_);
lean_dec_ref(v___x_5757_);
v___x_5759_ = lean_unsigned_to_nat(1u);
v___x_5763_ = lean_nat_dec_lt(v___x_5759_, v_numCases_5746_);
if (v___x_5763_ == 0)
{
v___y_5761_ = v_isRec_5747_;
goto v___jp_5760_;
}
else
{
v___y_5761_ = v___x_5763_;
goto v___jp_5760_;
}
v___jp_5749_:
{
lean_object* v___f_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___f_5751_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_5751_, 0, v___y_5750_);
lean_closure_set(v___f_5751_, 1, v___f_5748_);
v___x_5752_ = lean_box(v_isRec_5747_);
v___x_5753_ = lean_box(v_stopAtFirstFailure_5724_);
v___x_5754_ = lean_box(v_compress_5725_);
v___x_5755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 18, 5);
lean_closure_set(v___x_5755_, 0, v_c_5745_);
lean_closure_set(v___x_5755_, 1, v_numCases_5746_);
lean_closure_set(v___x_5755_, 2, v___x_5752_);
lean_closure_set(v___x_5755_, 3, v___x_5753_);
lean_closure_set(v___x_5755_, 4, v___x_5754_);
v___x_5756_ = l_Lean_Meta_Grind_Action_andThen(v___x_5755_, v___f_5751_, v_snd_5744_, v_kna_5727_, v_kp_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
return v___x_5756_;
}
v___jp_5760_:
{
if (v___y_5761_ == 0)
{
v___y_5750_ = v___x_5758_;
goto v___jp_5749_;
}
else
{
lean_object* v___x_5762_; 
v___x_5762_ = lean_nat_add(v___x_5758_, v___x_5759_);
lean_dec(v___x_5758_);
v___y_5750_ = v___x_5762_;
goto v___jp_5749_;
}
}
}
else
{
lean_object* v_snd_5764_; lean_object* v___x_5765_; 
lean_dec_ref(v_kp_5728_);
v_snd_5764_ = lean_ctor_get(v_a_5742_, 1);
lean_inc(v_snd_5764_);
lean_dec(v_a_5742_);
lean_inc(v_a_5737_);
lean_inc_ref(v_a_5736_);
lean_inc(v_a_5735_);
lean_inc_ref(v_a_5734_);
lean_inc(v_a_5733_);
lean_inc_ref(v_a_5732_);
lean_inc(v_a_5731_);
lean_inc_ref(v_a_5730_);
lean_inc(v_a_5729_);
v___x_5765_ = lean_apply_11(v_kna_5727_, v_snd_5764_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, lean_box(0));
return v___x_5765_;
}
}
else
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5773_; 
lean_dec_ref(v_kp_5728_);
lean_dec_ref(v_kna_5727_);
v_a_5766_ = lean_ctor_get(v___x_5741_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5741_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5768_ = v___x_5741_;
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5741_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5771_; 
if (v_isShared_5769_ == 0)
{
v___x_5771_ = v___x_5768_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5766_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_5774_, lean_object* v_compress_5775_, lean_object* v_goal_5776_, lean_object* v_kna_5777_, lean_object* v_kp_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5789_; uint8_t v_compress_boxed_5790_; lean_object* v_res_5791_; 
v_stopAtFirstFailure_boxed_5789_ = lean_unbox(v_stopAtFirstFailure_5774_);
v_compress_boxed_5790_ = lean_unbox(v_compress_5775_);
v_res_5791_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_5789_, v_compress_boxed_5790_, v_goal_5776_, v_kna_5777_, v_kp_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
lean_dec(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
lean_dec(v_a_5779_);
return v_res_5791_;
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
