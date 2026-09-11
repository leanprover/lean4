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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_7_, 1);
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
if (v_isRec_63_ == 0)
{
if (v_isRec_60_ == 0)
{
v___y_66_ = v___x_67_;
goto v___jp_65_;
}
else
{
return v_isRec_63_;
}
}
else
{
v___y_66_ = v_isRec_60_;
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
if (v_tryPostpone_64_ == 0)
{
if (v_tryPostpone_61_ == 0)
{
return v___y_66_;
}
else
{
return v_tryPostpone_64_;
}
}
else
{
return v_tryPostpone_61_;
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
lean_dec_ref_known(v_x_91_, 1);
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
lean_dec_ref_known(v___x_179_, 1);
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
lean_dec_ref_known(v___x_255_, 1);
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
lean_dec_ref_known(v___x_281_, 1);
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
lean_dec_ref_known(v___x_387_, 1);
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
lean_dec_ref_known(v___x_548_, 1);
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
lean_dec_ref_known(v___x_561_, 1);
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
lean_dec_ref_known(v___x_574_, 1);
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
lean_dec_ref_known(v___y_491_, 1);
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
lean_dec_ref_known(v___x_494_, 1);
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
lean_dec_ref_known(v___y_533_, 1);
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
lean_dec_ref_known(v___x_536_, 1);
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
v___x_645_ = lean_box(v_d_629_);
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
uint8_t v___x_7895__boxed_668_; uint8_t v_d_boxed_669_; lean_object* v_res_670_; 
v___x_7895__boxed_668_ = lean_unbox(v___x_653_);
v_d_boxed_669_ = lean_unbox(v_d_654_);
v_res_670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_652_, v___x_7895__boxed_668_, v_d_boxed_669_, v_a_655_, v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
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
lean_dec_ref_known(v___x_692_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_714_, lean_object* v_as_715_, size_t v_i_716_, size_t v_stop_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_a_731_; lean_object* v___y_736_; uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_eq(v_i_716_, v_stop_717_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_array_uget_borrowed(v_as_715_, v_i_716_);
switch(lean_obj_tag(v___x_739_))
{
case 0:
{
lean_object* v_key_740_; lean_object* v_val_741_; lean_object* v___x_742_; 
v_key_740_ = lean_ctor_get(v___x_739_, 0);
v_val_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc_ref(v_f_714_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc(v___y_719_);
lean_inc(v_val_741_);
lean_inc(v_key_740_);
v___x_742_ = lean_apply_14(v_f_714_, v_b_718_, v_key_740_, v_val_741_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, lean_box(0));
v___y_736_ = v___x_742_;
goto v___jp_735_;
}
case 1:
{
lean_object* v_node_743_; lean_object* v___x_744_; 
v_node_743_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_node_743_);
lean_inc_ref(v_f_714_);
v___x_744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_714_, v_node_743_, v_b_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
v___y_736_ = v___x_744_;
goto v___jp_735_;
}
default: 
{
v_a_731_ = v_b_718_;
goto v___jp_730_;
}
}
}
else
{
lean_object* v___x_745_; 
lean_dec_ref(v_f_714_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_b_718_);
return v___x_745_;
}
v___jp_730_:
{
size_t v___x_732_; size_t v___x_733_; 
v___x_732_ = ((size_t)1ULL);
v___x_733_ = lean_usize_add(v_i_716_, v___x_732_);
v_i_716_ = v___x_733_;
v_b_718_ = v_a_731_;
goto _start;
}
v___jp_735_:
{
if (lean_obj_tag(v___y_736_) == 0)
{
lean_object* v_a_737_; 
v_a_737_ = lean_ctor_get(v___y_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___y_736_, 1);
v_a_731_ = v_a_737_;
goto v___jp_730_;
}
else
{
lean_dec_ref(v_f_714_);
return v___y_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v_es_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_773_; 
v_es_760_ = lean_ctor_get(v_x_747_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_773_ == 0)
{
v___x_762_ = v_x_747_;
v_isShared_763_ = v_isSharedCheck_773_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_es_760_);
lean_dec(v_x_747_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_773_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_es_760_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v_es_760_);
lean_dec_ref(v_f_746_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_x_748_);
v___x_768_ = v___x_762_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_x_748_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
lean_del_object(v___x_762_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = lean_usize_of_nat(v___x_765_);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_746_, v_es_760_, v___x_770_, v___x_771_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec_ref(v_es_760_);
return v___x_772_;
}
}
}
else
{
lean_object* v_ks_774_; lean_object* v_vs_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_ks_774_ = lean_ctor_get(v_x_747_, 0);
lean_inc_ref(v_ks_774_);
v_vs_775_ = lean_ctor_get(v_x_747_, 1);
lean_inc_ref(v_vs_775_);
lean_dec_ref_known(v_x_747_, 2);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_746_, v_ks_774_, v_vs_775_, v___x_776_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec_ref(v_vs_775_);
lean_dec_ref(v_ks_774_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_778_, v_x_779_, v_x_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_793_, lean_object* v_as_794_, lean_object* v_i_795_, lean_object* v_stop_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
size_t v_i_boxed_809_; size_t v_stop_boxed_810_; lean_object* v_res_811_; 
v_i_boxed_809_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_stop_boxed_810_ = lean_unbox_usize(v_stop_796_);
lean_dec(v_stop_796_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_793_, v_as_794_, v_i_boxed_809_, v_stop_boxed_810_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v_as_794_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Expr_isApp(v_c_812_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_c_812_);
v___x_825_ = lean_box(v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v_toGoalState_828_; lean_object* v_split_829_; lean_object* v_resolved_830_; lean_object* v___x_831_; lean_object* v___f_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_827_ = lean_st_ref_get(v_a_813_);
v_toGoalState_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_toGoalState_828_);
lean_dec(v___x_827_);
v_split_829_ = lean_ctor_get(v_toGoalState_828_, 14);
lean_inc_ref(v_split_829_);
lean_dec_ref(v_toGoalState_828_);
v_resolved_830_ = lean_ctor_get(v_split_829_, 3);
lean_inc_ref(v_resolved_830_);
lean_dec_ref(v_split_829_);
v___x_831_ = lean_box(v___x_824_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_832_, 0, v_c_812_);
lean_closure_set(v___f_832_, 1, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_box(v___x_833_);
v___x_835_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_832_, v_resolved_830_, v___x_834_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_849_, lean_object* v_f_850_, lean_object* v_init_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_850_, v_map_849_, v_init_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_864_, lean_object* v_f_865_, lean_object* v_init_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_864_, v_f_865_, v_init_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_879_, lean_object* v_00_u03b2_880_, lean_object* v_map_881_, lean_object* v_f_882_, lean_object* v_init_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_882_, v_map_881_, v_init_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_896_, lean_object* v_00_u03b2_897_, lean_object* v_map_898_, lean_object* v_f_899_, lean_object* v_init_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_896_, v_00_u03b2_897_, v_map_898_, v_f_899_, v_init_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_913_, lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_f_916_, lean_object* v_x_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_916_, v_x_917_, v_x_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_931_ = _args[0];
lean_object* v_00_u03b1_932_ = _args[1];
lean_object* v_00_u03b2_933_ = _args[2];
lean_object* v_f_934_ = _args[3];
lean_object* v_x_935_ = _args[4];
lean_object* v_x_936_ = _args[5];
lean_object* v___y_937_ = _args[6];
lean_object* v___y_938_ = _args[7];
lean_object* v___y_939_ = _args[8];
lean_object* v___y_940_ = _args[9];
lean_object* v___y_941_ = _args[10];
lean_object* v___y_942_ = _args[11];
lean_object* v___y_943_ = _args[12];
lean_object* v___y_944_ = _args[13];
lean_object* v___y_945_ = _args[14];
lean_object* v___y_946_ = _args[15];
lean_object* v___y_947_ = _args[16];
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_931_, v_00_u03b1_932_, v_00_u03b2_933_, v_f_934_, v_x_935_, v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec(v___y_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_00_u03c3_951_, lean_object* v_f_952_, lean_object* v_as_953_, size_t v_i_954_, size_t v_stop_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_952_, v_as_953_, v_i_954_, v_stop_955_, v_b_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_969_ = _args[0];
lean_object* v_00_u03b2_970_ = _args[1];
lean_object* v_00_u03c3_971_ = _args[2];
lean_object* v_f_972_ = _args[3];
lean_object* v_as_973_ = _args[4];
lean_object* v_i_974_ = _args[5];
lean_object* v_stop_975_ = _args[6];
lean_object* v_b_976_ = _args[7];
lean_object* v___y_977_ = _args[8];
lean_object* v___y_978_ = _args[9];
lean_object* v___y_979_ = _args[10];
lean_object* v___y_980_ = _args[11];
lean_object* v___y_981_ = _args[12];
lean_object* v___y_982_ = _args[13];
lean_object* v___y_983_ = _args[14];
lean_object* v___y_984_ = _args[15];
lean_object* v___y_985_ = _args[16];
lean_object* v___y_986_ = _args[17];
lean_object* v___y_987_ = _args[18];
_start:
{
size_t v_i_boxed_988_; size_t v_stop_boxed_989_; lean_object* v_res_990_; 
v_i_boxed_988_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_stop_boxed_989_ = lean_unbox_usize(v_stop_975_);
lean_dec(v_stop_975_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_969_, v_00_u03b2_970_, v_00_u03c3_971_, v_f_972_, v_as_973_, v_i_boxed_988_, v_stop_boxed_989_, v_b_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v_as_973_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_991_, lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_f_994_, lean_object* v_keys_995_, lean_object* v_vals_996_, lean_object* v_heq_997_, lean_object* v_i_998_, lean_object* v_acc_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_994_, v_keys_995_, v_vals_996_, v_i_998_, v_acc_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1012_ = _args[0];
lean_object* v_00_u03b1_1013_ = _args[1];
lean_object* v_00_u03b2_1014_ = _args[2];
lean_object* v_f_1015_ = _args[3];
lean_object* v_keys_1016_ = _args[4];
lean_object* v_vals_1017_ = _args[5];
lean_object* v_heq_1018_ = _args[6];
lean_object* v_i_1019_ = _args[7];
lean_object* v_acc_1020_ = _args[8];
lean_object* v___y_1021_ = _args[9];
lean_object* v___y_1022_ = _args[10];
lean_object* v___y_1023_ = _args[11];
lean_object* v___y_1024_ = _args[12];
lean_object* v___y_1025_ = _args[13];
lean_object* v___y_1026_ = _args[14];
lean_object* v___y_1027_ = _args[15];
lean_object* v___y_1028_ = _args[16];
lean_object* v___y_1029_ = _args[17];
lean_object* v___y_1030_ = _args[18];
lean_object* v___y_1031_ = _args[19];
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1012_, v_00_u03b1_1013_, v_00_u03b2_1014_, v_f_1015_, v_keys_1016_, v_vals_1017_, v_heq_1018_, v_i_1019_, v_acc_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v_vals_1017_);
lean_dec_ref(v_keys_1016_);
return v_res_1032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set(v___x_1038_, 3, v___x_1037_);
lean_ctor_set(v___x_1038_, 4, v___x_1036_);
lean_ctor_set(v___x_1038_, 5, v___x_1036_);
lean_ctor_set(v___x_1038_, 6, v___x_1036_);
lean_ctor_set(v___x_1038_, 7, v___x_1036_);
lean_ctor_set(v___x_1038_, 8, v___x_1036_);
lean_ctor_set(v___x_1038_, 9, v___x_1036_);
lean_ctor_set(v___x_1038_, 10, v___x_1036_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(32u);
v___x_1040_ = lean_mk_empty_array_with_capacity(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_unsigned_to_nat(32u);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1047_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
lean_ctor_set(v___x_1047_, 2, v___x_1043_);
lean_ctor_set(v___x_1047_, 3, v___x_1043_);
lean_ctor_set_usize(v___x_1047_, 4, v___x_1042_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = lean_box(1);
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1049_);
lean_ctor_set(v___x_1051_, 2, v___x_1048_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1073_, lean_object* v_declHint_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_env_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_st_ref_get(v___y_1075_);
v_env_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_env_1078_);
lean_dec(v___x_1077_);
v___x_1079_ = l_Lean_Name_isAnonymous(v_declHint_1074_);
if (v___x_1079_ == 0)
{
uint8_t v_isExporting_1080_; 
v_isExporting_1080_ = lean_ctor_get_uint8(v_env_1078_, sizeof(void*)*8);
if (v_isExporting_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1074_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_msg_1073_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
lean_inc_ref(v_env_1078_);
v___x_1082_ = l_Lean_Environment_setExporting(v_env_1078_, v___x_1079_);
lean_inc(v_declHint_1074_);
lean_inc_ref(v___x_1082_);
v___x_1083_ = l_Lean_Environment_contains(v___x_1082_, v_declHint_1074_, v_isExporting_1080_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref(v___x_1082_);
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1074_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_msg_1073_);
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
lean_inc(v_declHint_1074_);
v___x_1089_ = l_Lean_MessageData_ofConstName(v_declHint_1074_, v___x_1079_);
v_c_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1090_, 0, v___x_1088_);
lean_ctor_set(v_c_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1078_, v_declHint_1074_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1074_);
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
lean_ctor_set(v___x_1097_, 0, v_msg_1073_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1134_; 
v_val_1099_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1101_ = v___x_1091_;
v_isShared_1102_ = v_isSharedCheck_1134_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v___x_1091_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1134_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_mod_1106_; uint8_t v___x_1107_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Lean_Environment_header(v_env_1078_);
lean_dec_ref(v_env_1078_);
v___x_1105_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1104_);
v_mod_1106_ = lean_array_get(v___x_1103_, v___x_1105_, v_val_1099_);
lean_dec(v_val_1099_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = l_Lean_isPrivateName(v_declHint_1074_);
lean_dec(v_declHint_1074_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_c_1090_);
v___x_1110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_MessageData_ofName(v_mod_1106_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = l_Lean_MessageData_note(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_msg_1073_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1117_);
v___x_1119_ = v___x_1101_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_c_1090_);
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofName(v_mod_1106_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_note(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_msg_1073_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1130_);
v___x_1132_ = v___x_1101_;
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
}
}
}
else
{
lean_object* v___x_1135_; 
lean_dec_ref(v_env_1078_);
lean_dec(v_declHint_1074_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1073_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1136_, lean_object* v_declHint_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1136_, v_declHint_1137_, v___y_1138_);
lean_dec(v___y_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1141_, lean_object* v_declHint_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1164_; 
v___x_1154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1141_, v_declHint_1142_, v___y_1152_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1159_ = l_Lean_unknownIdentifierMessageTag;
v___x_1160_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1165_, lean_object* v_declHint_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1165_, v_declHint_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; lean_object* v_toCold_1188_; lean_object* v_mctx_1189_; lean_object* v_lctx_1190_; lean_object* v_options_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1185_ = lean_st_ref_get(v___y_1183_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_st_ref_get(v___y_1181_);
v_toCold_1188_ = lean_ctor_get(v___y_1182_, 0);
v_mctx_1189_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_mctx_1189_);
lean_dec(v___x_1187_);
v_lctx_1190_ = lean_ctor_get(v___y_1180_, 2);
v_options_1191_ = lean_ctor_get(v_toCold_1188_, 2);
lean_inc_ref(v_options_1191_);
lean_inc_ref(v_lctx_1190_);
v___x_1192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1192_, 0, v_env_1186_);
lean_ctor_set(v___x_1192_, 1, v_mctx_1189_);
lean_ctor_set(v___x_1192_, 2, v_lctx_1190_);
lean_ctor_set(v___x_1192_, 3, v_options_1191_);
v___x_1193_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_msgData_1179_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_ref_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_ref_1208_ = lean_ctor_get(v___y_1205_, 2);
v___x_1209_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_inc(v_ref_1208_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_ref_1208_);
lean_ctor_set(v___x_1214_, 1, v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 1);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1226_, lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_toCold_1239_; lean_object* v_currRecDepth_1240_; lean_object* v_ref_1241_; uint8_t v_diag_1242_; uint8_t v_suppressElabErrors_1243_; lean_object* v_ref_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_toCold_1239_ = lean_ctor_get(v___y_1236_, 0);
v_currRecDepth_1240_ = lean_ctor_get(v___y_1236_, 1);
v_ref_1241_ = lean_ctor_get(v___y_1236_, 2);
v_diag_1242_ = lean_ctor_get_uint8(v___y_1236_, sizeof(void*)*3);
v_suppressElabErrors_1243_ = lean_ctor_get_uint8(v___y_1236_, sizeof(void*)*3 + 1);
v_ref_1244_ = l_Lean_replaceRef(v_ref_1226_, v_ref_1241_);
lean_inc(v_currRecDepth_1240_);
lean_inc_ref(v_toCold_1239_);
v___x_1245_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1245_, 0, v_toCold_1239_);
lean_ctor_set(v___x_1245_, 1, v_currRecDepth_1240_);
lean_ctor_set(v___x_1245_, 2, v_ref_1244_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3, v_diag_1242_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3 + 1, v_suppressElabErrors_1243_);
v___x_1246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1227_, v___y_1234_, v___y_1235_, v___x_1245_, v___y_1237_);
lean_dec_ref_known(v___x_1245_, 3);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1247_, lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1247_, v_msg_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_ref_1247_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1261_, lean_object* v_msg_1262_, lean_object* v_declHint_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v_a_1276_; lean_object* v___x_1277_; 
v___x_1275_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1262_, v_declHint_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1261_, v_a_1276_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1278_, lean_object* v_msg_1279_, lean_object* v_declHint_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1278_, v_msg_1279_, v_declHint_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec(v_ref_1278_);
return v_res_1292_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1299_, lean_object* v_constName_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1312_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1313_ = 0;
lean_inc(v_constName_1300_);
v___x_1314_ = l_Lean_MessageData_ofConstName(v_constName_1300_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1312_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1299_, v___x_1317_, v_constName_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1319_, lean_object* v_constName_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1319_, v_constName_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v_ref_1319_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_ref_1345_; lean_object* v___x_1346_; 
v_ref_1345_ = lean_ctor_get(v___y_1342_, 2);
v___x_1346_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1345_, v_constName_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec(v___y_1348_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_env_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_st_ref_get(v___y_1370_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_env_1373_);
lean_dec(v___x_1372_);
v___x_1374_ = 0;
lean_inc(v_constName_1360_);
v___x_1375_ = l_Lean_Environment_find_x3f(v_env_1373_, v_constName_1360_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_constName_1360_);
v_val_1377_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 0);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_val_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1397_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1398_; double v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_float_of_nat(v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_ref_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1456_; 
v_ref_1410_ = lean_ctor_get(v___y_1407_, 2);
v___x_1411_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v_traceState_1417_; lean_object* v_env_1418_; lean_object* v_nextMacroScope_1419_; lean_object* v_ngen_1420_; lean_object* v_auxDeclNGen_1421_; lean_object* v_cache_1422_; lean_object* v_messages_1423_; lean_object* v_infoState_1424_; lean_object* v_snapshotTasks_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1455_; 
v___x_1416_ = lean_st_ref_take(v___y_1408_);
v_traceState_1417_ = lean_ctor_get(v___x_1416_, 4);
v_env_1418_ = lean_ctor_get(v___x_1416_, 0);
v_nextMacroScope_1419_ = lean_ctor_get(v___x_1416_, 1);
v_ngen_1420_ = lean_ctor_get(v___x_1416_, 2);
v_auxDeclNGen_1421_ = lean_ctor_get(v___x_1416_, 3);
v_cache_1422_ = lean_ctor_get(v___x_1416_, 5);
v_messages_1423_ = lean_ctor_get(v___x_1416_, 6);
v_infoState_1424_ = lean_ctor_get(v___x_1416_, 7);
v_snapshotTasks_1425_ = lean_ctor_get(v___x_1416_, 8);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1427_ = v___x_1416_;
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snapshotTasks_1425_);
lean_inc(v_infoState_1424_);
lean_inc(v_messages_1423_);
lean_inc(v_cache_1422_);
lean_inc(v_traceState_1417_);
lean_inc(v_auxDeclNGen_1421_);
lean_inc(v_ngen_1420_);
lean_inc(v_nextMacroScope_1419_);
lean_inc(v_env_1418_);
lean_dec(v___x_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint64_t v_tid_1429_; lean_object* v_traces_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_tid_1429_ = lean_ctor_get_uint64(v_traceState_1417_, sizeof(void*)*1);
v_traces_1430_ = lean_ctor_get(v_traceState_1417_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_traceState_1417_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1432_ = v_traceState_1417_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_traces_1430_);
lean_dec(v_traceState_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; double v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1436_ = 0;
v___x_1437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1438_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1438_, 0, v_cls_1403_);
lean_ctor_set(v___x_1438_, 1, v___x_1434_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3, v___x_1435_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3 + 8, v___x_1435_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*3 + 16, v___x_1436_);
v___x_1439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1440_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v_a_1412_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
lean_inc(v_ref_1410_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_ref_1410_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_PersistentArray_push___redArg(v_traces_1430_, v___x_1441_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1442_);
v___x_1444_ = v___x_1432_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1442_);
lean_ctor_set_uint64(v_reuseFailAlloc_1453_, sizeof(void*)*1, v_tid_1429_);
v___x_1444_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 4, v___x_1444_);
v___x_1446_ = v___x_1427_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_env_1418_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_nextMacroScope_1419_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_ngen_1420_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_auxDeclNGen_1421_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 5, v_cache_1422_);
lean_ctor_set(v_reuseFailAlloc_1452_, 6, v_messages_1423_);
lean_ctor_set(v_reuseFailAlloc_1452_, 7, v_infoState_1424_);
lean_ctor_set(v_reuseFailAlloc_1452_, 8, v_snapshotTasks_1425_);
v___x_1446_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = lean_st_ref_put(v___y_1408_, v___x_1446_);
v___x_1448_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1448_);
v___x_1450_ = v___x_1414_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1457_, v_msg_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1467_ = l_Lean_stringToMessageData(v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1470_ = l_Lean_stringToMessageData(v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1483_ = l_Lean_Name_append(v___x_1482_, v___x_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
uint8_t v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___x_1749_; 
lean_inc_ref(v_e_1496_);
v___x_1749_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1496_, v_a_1504_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1791_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1791_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1791_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = l_Lean_Expr_cleanupAnnotations(v_a_1750_);
v___x_1768_ = l_Lean_Expr_isApp(v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v___x_1767_);
lean_del_object(v___x_1752_);
v___y_1755_ = v_a_1497_;
v___y_1756_ = v_a_1498_;
v___y_1757_ = v_a_1499_;
v___y_1758_ = v_a_1500_;
v___y_1759_ = v_a_1501_;
v___y_1760_ = v_a_1502_;
v___y_1761_ = v_a_1503_;
v___y_1762_ = v_a_1504_;
v___y_1763_ = v_a_1505_;
v___y_1764_ = v_a_1506_;
goto v___jp_1754_;
}
else
{
lean_object* v_arg_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_arg_1769_ = lean_ctor_get(v___x_1767_, 1);
lean_inc_ref(v_arg_1769_);
v___x_1770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1767_);
v___x_1771_ = l_Lean_Expr_isApp(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_arg_1769_);
lean_del_object(v___x_1752_);
v___y_1755_ = v_a_1497_;
v___y_1756_ = v_a_1498_;
v___y_1757_ = v_a_1499_;
v___y_1758_ = v_a_1500_;
v___y_1759_ = v_a_1501_;
v___y_1760_ = v_a_1502_;
v___y_1761_ = v_a_1503_;
v___y_1762_ = v_a_1504_;
v___y_1763_ = v_a_1505_;
v___y_1764_ = v_a_1506_;
goto v___jp_1754_;
}
else
{
lean_object* v_arg_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_arg_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_arg_1772_);
v___x_1773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1770_);
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1775_ = l_Lean_Expr_isConstOf(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1777_ = l_Lean_Expr_isConstOf(v___x_1773_, v___x_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = l_Lean_Expr_isApp(v___x_1773_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_del_object(v___x_1752_);
v___y_1755_ = v_a_1497_;
v___y_1756_ = v_a_1498_;
v___y_1757_ = v_a_1499_;
v___y_1758_ = v_a_1500_;
v___y_1759_ = v_a_1501_;
v___y_1760_ = v_a_1502_;
v___y_1761_ = v_a_1503_;
v___y_1762_ = v_a_1504_;
v___y_1763_ = v_a_1505_;
v___y_1764_ = v_a_1506_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1773_);
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1781_ = l_Lean_Expr_isConstOf(v___x_1779_, v___x_1780_);
lean_dec_ref(v___x_1779_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_del_object(v___x_1752_);
v___y_1755_ = v_a_1497_;
v___y_1756_ = v_a_1498_;
v___y_1757_ = v_a_1499_;
v___y_1758_ = v_a_1500_;
v___y_1759_ = v_a_1501_;
v___y_1760_ = v_a_1502_;
v___y_1761_ = v_a_1503_;
v___y_1762_ = v_a_1504_;
v___y_1763_ = v_a_1505_;
v___y_1764_ = v_a_1506_;
goto v___jp_1754_;
}
else
{
uint8_t v___x_1782_; 
lean_inc_ref(v_e_1496_);
v___x_1782_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1496_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_e_1496_);
v___x_1783_ = lean_unsigned_to_nat(2u);
v___x_1784_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*1, v___x_1782_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*1 + 1, v___x_1782_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1784_);
v___x_1786_ = v___x_1752_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1752_);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1496_, v_arg_1772_, v_arg_1769_, v_a_1497_, v_a_1501_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1788_;
}
}
}
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref(v___x_1773_);
lean_del_object(v___x_1752_);
v___x_1789_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1496_, v_arg_1772_, v_arg_1769_, v_a_1497_, v_a_1501_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1789_;
}
}
else
{
lean_object* v___x_1790_; 
lean_dec_ref(v___x_1773_);
lean_del_object(v___x_1752_);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1496_, v_arg_1772_, v_arg_1769_, v_a_1497_, v_a_1501_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1790_;
}
}
}
v___jp_1754_:
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_isIte(v_e_1496_);
if (v___x_1765_ == 0)
{
uint8_t v___x_1766_; 
v___x_1766_ = l_Lean_Meta_Grind_isDIte(v_e_1496_);
v___y_1624_ = v___y_1761_;
v___y_1625_ = v___y_1764_;
v___y_1626_ = v___y_1762_;
v___y_1627_ = v___y_1757_;
v___y_1628_ = v___y_1760_;
v___y_1629_ = v___y_1763_;
v___y_1630_ = v___y_1755_;
v___y_1631_ = v___y_1758_;
v___y_1632_ = v___y_1759_;
v___y_1633_ = v___y_1756_;
v___y_1634_ = v___x_1766_;
goto v___jp_1623_;
}
else
{
v___y_1624_ = v___y_1761_;
v___y_1625_ = v___y_1764_;
v___y_1626_ = v___y_1762_;
v___y_1627_ = v___y_1757_;
v___y_1628_ = v___y_1760_;
v___y_1629_ = v___y_1763_;
v___y_1630_ = v___y_1755_;
v___y_1631_ = v___y_1758_;
v___y_1632_ = v___y_1759_;
v___y_1633_ = v___y_1756_;
v___y_1634_ = v___x_1765_;
goto v___jp_1623_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v_e_1496_);
v_a_1792_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1749_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1749_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
v___jp_1508_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
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
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_Expr_isFVar(v_e_1496_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v_e_1496_);
v___x_1527_ = lean_box(1);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; 
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1522_);
lean_inc_ref(v_e_1496_);
v___x_1529_ = lean_infer_type(v_e_1496_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Meta_whnfD(v_a_1530_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_n(v_a_1532_, 2);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1534_ = l_Lean_MessageData_ofExpr(v_e_1496_);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = l_Lean_indentExpr(v_a_1532_);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_Expr_getAppFn(v_a_1532_);
lean_dec(v_a_1532_);
if (lean_obj_tag(v___x_1540_) == 4)
{
lean_object* v_declName_1541_; lean_object* v___x_1542_; 
v_declName_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_declName_1541_);
lean_dec_ref_known(v___x_1540_, 2);
v___x_1542_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1541_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1575_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1575_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1575_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
if (lean_obj_tag(v_a_1543_) == 5)
{
lean_object* v_val_1547_; lean_object* v_ctors_1548_; uint8_t v_isRec_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_dec_ref_known(v___x_1539_, 2);
v_val_1547_ = lean_ctor_get(v_a_1543_, 0);
lean_inc_ref(v_val_1547_);
lean_dec_ref_known(v_a_1543_, 1);
v_ctors_1548_ = lean_ctor_get(v_val_1547_, 4);
lean_inc(v_ctors_1548_);
v_isRec_1549_ = lean_ctor_get_uint8(v_val_1547_, sizeof(void*)*6);
lean_dec_ref(v_val_1547_);
v___x_1550_ = l_List_lengthTR___redArg(v_ctors_1548_);
lean_dec(v_ctors_1548_);
v___x_1551_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*1, v_isRec_1549_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*1 + 1, v___y_1515_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1551_);
v___x_1553_ = v___x_1545_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
else
{
lean_object* v___x_1555_; 
lean_del_object(v___x_1545_);
lean_dec(v_a_1543_);
v___x_1555_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1520_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v_verbose_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_verbose_1557_ = lean_ctor_get_uint8(v_a_1556_, 0);
lean_dec(v_a_1556_);
if (v_verbose_1557_ == 0)
{
lean_dec_ref_known(v___x_1539_, 2);
goto v___jp_1511_;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Meta_Sym_reportIssue(v___x_1539_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
goto v___jp_1511_;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref_known(v___x_1539_, 2);
v_a_1567_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1555_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1555_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref_known(v___x_1539_, 2);
v_a_1576_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1542_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1542_);
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
else
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1540_);
v___x_1584_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1520_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v_verbose_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_verbose_1586_ = lean_ctor_get_uint8(v_a_1585_, 0);
lean_dec(v_a_1585_);
if (v_verbose_1586_ == 0)
{
lean_dec_ref_known(v___x_1539_, 2);
goto v___jp_1508_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Sym_reportIssue(v___x_1539_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_dec_ref_known(v___x_1587_, 1);
goto v___jp_1508_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref_known(v___x_1539_, 2);
v_a_1596_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1584_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1584_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_e_1496_);
v_a_1604_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1531_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1531_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_e_1496_);
v_a_1612_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1529_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1529_);
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
v___jp_1620_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1623_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1496_, v___y_1630_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; uint8_t v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_unbox(v_a_1636_);
lean_dec(v_a_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_inc_ref(v_e_1496_);
v___x_1638_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1496_, v___y_1630_, v___y_1633_, v___y_1627_, v___y_1631_, v___y_1632_, v___y_1628_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1698_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1698_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1698_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
uint8_t v___x_1643_; 
v___x_1643_ = lean_unbox(v_a_1639_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v_env_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_st_ref_get(v___y_1625_);
v_env_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc_ref(v_env_1645_);
lean_dec(v___x_1644_);
v___x_1646_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1645_, v_e_1496_);
if (lean_obj_tag(v___x_1646_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1653_; 
lean_dec_ref(v_e_1496_);
v_val_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1647_);
lean_dec(v_val_1647_);
v___x_1649_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = lean_unbox(v_a_1639_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*1, v___x_1650_);
v___x_1651_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*1 + 1, v___x_1651_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1649_);
v___x_1653_ = v___x_1641_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1649_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_object* v___x_1655_; 
lean_dec(v___x_1646_);
lean_del_object(v___x_1641_);
v___x_1655_ = l_Lean_Expr_getAppFn(v_e_1496_);
if (lean_obj_tag(v___x_1655_) == 4)
{
lean_object* v_declName_1656_; lean_object* v___x_1657_; 
v_declName_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_declName_1656_);
lean_dec_ref_known(v___x_1655_, 2);
v___x_1657_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1656_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
if (lean_obj_tag(v_a_1658_) == 1)
{
lean_object* v_val_1659_; lean_object* v___x_1660_; 
v_val_1659_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_val_1659_);
lean_dec_ref_known(v_a_1658_, 1);
lean_inc_ref(v_e_1496_);
v___x_1660_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1496_, v___y_1630_, v___y_1632_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1675_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1675_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1675_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_unbox(v_a_1661_);
lean_dec(v_a_1661_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; 
lean_del_object(v___x_1663_);
lean_dec(v_val_1659_);
v___x_1666_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
v___y_1515_ = v___x_1666_;
v___y_1516_ = v___y_1630_;
v___y_1517_ = v___y_1633_;
v___y_1518_ = v___y_1627_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1632_;
v___y_1521_ = v___y_1628_;
v___y_1522_ = v___y_1624_;
v___y_1523_ = v___y_1626_;
v___y_1524_ = v___y_1629_;
v___y_1525_ = v___y_1625_;
goto v___jp_1514_;
}
else
{
lean_object* v_ctors_1667_; uint8_t v_isRec_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1673_; 
lean_dec_ref(v_e_1496_);
v_ctors_1667_ = lean_ctor_get(v_val_1659_, 4);
lean_inc(v_ctors_1667_);
v_isRec_1668_ = lean_ctor_get_uint8(v_val_1659_, sizeof(void*)*6);
lean_dec(v_val_1659_);
v___x_1669_ = l_List_lengthTR___redArg(v_ctors_1667_);
lean_dec(v_ctors_1667_);
v___x_1670_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*1, v_isRec_1668_);
v___x_1671_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*1 + 1, v___x_1671_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1670_);
v___x_1673_ = v___x_1663_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1670_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_val_1659_);
lean_dec(v_a_1639_);
lean_dec_ref(v_e_1496_);
v_a_1676_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1660_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1660_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
uint8_t v___x_1684_; 
lean_dec(v_a_1658_);
v___x_1684_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
v___y_1515_ = v___x_1684_;
v___y_1516_ = v___y_1630_;
v___y_1517_ = v___y_1633_;
v___y_1518_ = v___y_1627_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1632_;
v___y_1521_ = v___y_1628_;
v___y_1522_ = v___y_1624_;
v___y_1523_ = v___y_1626_;
v___y_1524_ = v___y_1629_;
v___y_1525_ = v___y_1625_;
goto v___jp_1514_;
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1639_);
lean_dec_ref(v_e_1496_);
v_a_1685_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1657_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1657_);
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
else
{
uint8_t v___x_1693_; 
lean_dec_ref(v___x_1655_);
v___x_1693_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
v___y_1515_ = v___x_1693_;
v___y_1516_ = v___y_1630_;
v___y_1517_ = v___y_1633_;
v___y_1518_ = v___y_1627_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1632_;
v___y_1521_ = v___y_1628_;
v___y_1522_ = v___y_1624_;
v___y_1523_ = v___y_1626_;
v___y_1524_ = v___y_1629_;
v___y_1525_ = v___y_1625_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec(v_a_1639_);
lean_dec_ref(v_e_1496_);
v___x_1694_ = lean_box(0);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1694_);
v___x_1696_ = v___x_1641_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v_e_1496_);
v_a_1699_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1638_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1638_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_toCold_1707_; lean_object* v_options_1708_; uint8_t v_hasTrace_1709_; 
v_toCold_1707_ = lean_ctor_get(v___y_1629_, 0);
v_options_1708_ = lean_ctor_get(v_toCold_1707_, 2);
v_hasTrace_1709_ = lean_ctor_get_uint8(v_options_1708_, sizeof(void*)*1);
if (v_hasTrace_1709_ == 0)
{
lean_dec_ref(v_e_1496_);
goto v___jp_1620_;
}
else
{
lean_object* v_inheritedTraceOptions_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_inheritedTraceOptions_1710_ = lean_ctor_get(v_toCold_1707_, 11);
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1710_, v_options_1708_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec_ref(v_e_1496_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Meta_Grind_updateLastTag(v___y_1630_, v___y_1633_, v___y_1627_, v___y_1631_, v___y_1632_, v___y_1628_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref_known(v___x_1714_, 1);
v___x_1715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1716_ = l_Lean_MessageData_ofExpr(v_e_1496_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1711_, v___x_1717_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
goto v___jp_1620_;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
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
lean_dec_ref(v_e_1496_);
v_a_1727_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1714_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1714_);
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
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_e_1496_);
v_a_1735_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1635_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1635_);
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
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = l_Lean_Expr_getAppNumArgs(v_e_1496_);
v___x_1745_ = lean_nat_sub(v___x_1744_, v___x_1743_);
lean_dec(v___x_1744_);
v___x_1746_ = lean_nat_sub(v___x_1745_, v___x_1743_);
lean_dec(v___x_1745_);
v___x_1747_ = l_Lean_Expr_getRevArg_x21(v_e_1496_, v___x_1746_);
lean_dec_ref(v_e_1496_);
v___x_1748_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1747_, v___y_1630_, v___y_1632_, v___y_1624_, v___y_1626_, v___y_1629_, v___y_1625_);
return v___x_1748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec(v_a_1801_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1813_, lean_object* v_msg_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1813_, v_msg_1814_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1827_, lean_object* v_msg_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1827_, v_msg_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1841_, lean_object* v_constName_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_constName_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1855_, v_constName_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1869_, lean_object* v_ref_1870_, lean_object* v_constName_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1870_, v_constName_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1884_, lean_object* v_ref_1885_, lean_object* v_constName_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1884_, v_ref_1885_, v_constName_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v_ref_1885_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1899_, lean_object* v_ref_1900_, lean_object* v_msg_1901_, lean_object* v_declHint_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1900_, v_msg_1901_, v_declHint_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_ref_1916_, lean_object* v_msg_1917_, lean_object* v_declHint_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1915_, v_ref_1916_, v_msg_1917_, v_declHint_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
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
lean_dec(v_ref_1916_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1931_, lean_object* v_declHint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1931_, v_declHint_1932_, v___y_1942_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1945_, lean_object* v_declHint_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1945_, v_declHint_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec(v___y_1947_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1959_, lean_object* v_ref_1960_, lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1960_, v_msg_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_ref_1975_, lean_object* v_msg_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1974_, v_ref_1975_, v_msg_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec(v_ref_1975_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1989_, lean_object* v_msg_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1990_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2003_, v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2017_, lean_object* v_x_2018_){
_start:
{
if (lean_obj_tag(v_x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
return v___x_2019_;
}
else
{
lean_object* v_key_2020_; lean_object* v_value_2021_; lean_object* v_tail_2022_; uint8_t v___y_2024_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v_fst_2029_; lean_object* v_snd_2030_; uint8_t v___x_2031_; 
v_key_2020_ = lean_ctor_get(v_x_2018_, 0);
v_value_2021_ = lean_ctor_get(v_x_2018_, 1);
v_tail_2022_ = lean_ctor_get(v_x_2018_, 2);
v_fst_2027_ = lean_ctor_get(v_key_2020_, 0);
v_snd_2028_ = lean_ctor_get(v_key_2020_, 1);
v_fst_2029_ = lean_ctor_get(v_a_2017_, 0);
v_snd_2030_ = lean_ctor_get(v_a_2017_, 1);
v___x_2031_ = lean_expr_eqv(v_fst_2027_, v_fst_2029_);
if (v___x_2031_ == 0)
{
v___y_2024_ = v___x_2031_;
goto v___jp_2023_;
}
else
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_expr_eqv(v_snd_2028_, v_snd_2030_);
v___y_2024_ = v___x_2032_;
goto v___jp_2023_;
}
v___jp_2023_:
{
if (v___y_2024_ == 0)
{
v_x_2018_ = v_tail_2022_;
goto _start;
}
else
{
lean_object* v___x_2026_; 
lean_inc(v_value_2021_);
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_value_2021_);
return v___x_2026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2033_, v_x_2034_);
lean_dec(v_x_2034_);
lean_dec_ref(v_a_2033_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_buckets_2038_; lean_object* v_fst_2039_; lean_object* v_snd_2040_; lean_object* v___x_2041_; uint64_t v___x_2042_; uint64_t v___x_2043_; uint64_t v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; uint64_t v_fold_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; size_t v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_buckets_2038_ = lean_ctor_get(v_m_2036_, 1);
v_fst_2039_ = lean_ctor_get(v_a_2037_, 0);
v_snd_2040_ = lean_ctor_get(v_a_2037_, 1);
v___x_2041_ = lean_array_get_size(v_buckets_2038_);
v___x_2042_ = l_Lean_Expr_hash(v_fst_2039_);
v___x_2043_ = l_Lean_Expr_hash(v_snd_2040_);
v___x_2044_ = lean_uint64_mix_hash(v___x_2042_, v___x_2043_);
v___x_2045_ = 32ULL;
v___x_2046_ = lean_uint64_shift_right(v___x_2044_, v___x_2045_);
v_fold_2047_ = lean_uint64_xor(v___x_2044_, v___x_2046_);
v___x_2048_ = 16ULL;
v___x_2049_ = lean_uint64_shift_right(v_fold_2047_, v___x_2048_);
v___x_2050_ = lean_uint64_xor(v_fold_2047_, v___x_2049_);
v___x_2051_ = lean_uint64_to_usize(v___x_2050_);
v___x_2052_ = lean_usize_of_nat(v___x_2041_);
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_sub(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_usize_land(v___x_2051_, v___x_2054_);
v___x_2056_ = lean_array_uget_borrowed(v_buckets_2038_, v___x_2055_);
v___x_2057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2037_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2058_, v_a_2059_);
lean_dec_ref(v_a_2059_);
lean_dec_ref(v_m_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2061_, uint8_t v___x_2062_, lean_object* v_fst_2063_, lean_object* v_snd_2064_, lean_object* v___x_2065_, lean_object* v_____r_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2078_ = lean_unsigned_to_nat(2u);
v___x_2079_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*1, v_a_2061_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*1 + 1, v___x_2062_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_fst_2063_);
lean_ctor_set(v___x_2081_, 1, v_snd_2064_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2065_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2080_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2086_ = _args[0];
lean_object* v___x_2087_ = _args[1];
lean_object* v_fst_2088_ = _args[2];
lean_object* v_snd_2089_ = _args[3];
lean_object* v___x_2090_ = _args[4];
lean_object* v_____r_2091_ = _args[5];
lean_object* v___y_2092_ = _args[6];
lean_object* v___y_2093_ = _args[7];
lean_object* v___y_2094_ = _args[8];
lean_object* v___y_2095_ = _args[9];
lean_object* v___y_2096_ = _args[10];
lean_object* v___y_2097_ = _args[11];
lean_object* v___y_2098_ = _args[12];
lean_object* v___y_2099_ = _args[13];
lean_object* v___y_2100_ = _args[14];
lean_object* v___y_2101_ = _args[15];
lean_object* v___y_2102_ = _args[16];
_start:
{
uint8_t v_a_33719__boxed_2103_; uint8_t v___x_33720__boxed_2104_; lean_object* v_res_2105_; 
v_a_33719__boxed_2103_ = lean_unbox(v_a_2086_);
v___x_33720__boxed_2104_ = lean_unbox(v___x_2087_);
v_res_2105_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_33719__boxed_2103_, v___x_33720__boxed_2104_, v_fst_2088_, v_snd_2089_, v___x_2090_, v_____r_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec(v___y_2092_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2106_, lean_object* v_snd_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_____r_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2122_ = l_Lean_Expr_appFn_x21(v_fst_2106_);
v___x_2123_ = l_Lean_Expr_appFn_x21(v_snd_2107_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2108_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2109_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2129_, lean_object* v_snd_2130_, lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v_____r_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2129_, v_snd_2130_, v___x_2131_, v___x_2132_, v_____r_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec(v_snd_2130_);
lean_dec(v_fst_2129_);
return v_res_2145_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___f_2147_; 
v___x_2146_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2147_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2147_, 0, v___x_2146_);
return v___f_2147_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2153_ = l_Lean_Name_append(v___x_2152_, v___x_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2156_ = l_Lean_stringToMessageData(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2162_ = l_Lean_stringToMessageData(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2172_, lean_object* v___y_2173_, lean_object* v_eq_2174_, lean_object* v_a_2175_, lean_object* v_b_2176_, lean_object* v_a_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___y_2190_; lean_object* v_snd_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2333_; 
v_snd_2210_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_a_2177_, 0);
lean_dec(v_unused_2334_);
v___x_2212_ = v_a_2177_;
v_isShared_2213_ = v_isSharedCheck_2333_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_snd_2210_);
lean_dec(v_a_2177_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2333_;
goto v_resetjp_2211_;
}
v___jp_2189_:
{
if (lean_obj_tag(v___y_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2201_; 
v_a_2191_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2193_ = v___y_2190_;
v_isShared_2194_ = v_isSharedCheck_2201_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___y_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2201_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
if (lean_obj_tag(v_a_2191_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; 
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2195_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v_a_2191_, 1);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v_a_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
else
{
lean_object* v_a_2199_; 
lean_del_object(v___x_2193_);
v_a_2199_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v_a_2191_, 1);
v_a_2177_ = v_a_2199_;
goto _start;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2202_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___y_2190_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___y_2190_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
v_resetjp_2211_:
{
lean_object* v_snd_2214_; lean_object* v_fst_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2332_; 
v_snd_2214_ = lean_ctor_get(v_snd_2210_, 1);
v_fst_2215_ = lean_ctor_get(v_snd_2210_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_snd_2210_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2217_ = v_snd_2210_;
v_isShared_2218_ = v_isSharedCheck_2332_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snd_2214_);
lean_inc(v_fst_2215_);
lean_dec(v_snd_2210_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2332_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2331_; 
v_fst_2219_ = lean_ctor_get(v_snd_2214_, 0);
v_snd_2220_ = lean_ctor_get(v_snd_2214_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_snd_2214_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2222_ = v_snd_2214_;
v_isShared_2223_ = v_isSharedCheck_2331_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_snd_2220_);
lean_inc(v_fst_2219_);
lean_dec(v_snd_2214_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2331_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
uint8_t v___y_2225_; uint8_t v___x_2239_; 
v___x_2239_ = l_Lean_Expr_isApp(v_fst_2219_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v___y_2225_ = v_a_2172_;
goto v___jp_2224_;
}
else
{
uint8_t v___x_2240_; 
v___x_2240_ = l_Lean_Expr_isApp(v_snd_2220_);
if (v___x_2240_ == 0)
{
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v___y_2225_ = v___x_2240_;
goto v___jp_2224_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___f_2247_; uint8_t v___x_2248_; 
lean_del_object(v___x_2222_);
lean_del_object(v___x_2217_);
lean_del_object(v___x_2212_);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_sub(v_fst_2215_, v___x_2242_);
lean_dec(v_fst_2215_);
v___f_2247_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2173_);
lean_inc(v___x_2243_);
v___x_2248_ = l_List_elem___redArg(v___f_2247_, v___x_2243_, v___y_2173_);
if (v___x_2248_ == 0)
{
if (v___x_2240_ == 0)
{
goto v___jp_2244_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_Expr_appArg_x21(v_fst_2219_);
v___x_2250_ = l_Lean_Expr_appArg_x21(v_snd_2220_);
v___x_2251_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2249_, v___x_2250_, v___y_2178_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; uint8_t v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = lean_unbox(v_a_2252_);
if (v___x_2253_ == 0)
{
lean_object* v_toCold_2254_; lean_object* v_options_2255_; lean_object* v_inheritedTraceOptions_2256_; uint8_t v_hasTrace_2257_; 
v_toCold_2254_ = lean_ctor_get(v___y_2186_, 0);
v_options_2255_ = lean_ctor_get(v_toCold_2254_, 2);
v_inheritedTraceOptions_2256_ = lean_ctor_get(v_toCold_2254_, 11);
v_hasTrace_2257_ = lean_ctor_get_uint8(v_options_2255_, sizeof(void*)*1);
if (v_hasTrace_2257_ == 0)
{
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2263_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2264_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2256_, v_options_2255_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
goto v___jp_2258_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_Grind_updateLastTag(v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; 
lean_dec_ref_known(v___x_2265_, 1);
v___x_2266_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2174_, v___y_2178_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2175_);
v___x_2269_ = l_Lean_MessageData_ofExpr(v_a_2175_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_inc_ref(v_b_2176_);
v___x_2273_ = l_Lean_MessageData_ofExpr(v_b_2176_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
lean_inc_ref(v_eq_2174_);
v___x_2277_ = l_Lean_MessageData_ofExpr(v_eq_2174_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_MessageData_ofExpr(v___x_2249_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_MessageData_ofExpr(v___x_2250_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Nat_reprFast(v_a_2267_);
v___x_2290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = l_Lean_MessageData_ofFormat(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2288_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2262_, v___x_2292_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
v___x_2296_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2295_, v___x_2240_, v_fst_2219_, v_snd_2220_, v___x_2243_, v_a_2294_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2296_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_a_2252_);
lean_dec(v___x_2243_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2297_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2293_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2293_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2252_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2243_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2305_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2266_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2266_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2252_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2243_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2313_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2265_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2265_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
v___jp_2258_:
{
lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
v___x_2261_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2260_, v___x_2240_, v_fst_2219_, v_snd_2220_, v___x_2243_, v___x_2259_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2261_;
goto v___jp_2189_;
}
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v_a_2252_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
v___x_2321_ = lean_box(0);
v___x_2322_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2219_, v_snd_2220_, v___x_2243_, v___x_2241_, v___x_2321_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
v___y_2190_ = v___x_2322_;
goto v___jp_2189_;
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2243_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
lean_dec_ref(v_b_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_eq_2174_);
lean_dec(v___y_2173_);
v_a_2323_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2251_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2251_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
else
{
goto v___jp_2244_;
}
v___jp_2244_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2219_, v_snd_2220_, v___x_2243_, v___x_2241_, v___x_2245_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v_snd_2220_);
lean_dec(v_fst_2219_);
v___y_2190_ = v___x_2246_;
goto v___jp_2189_;
}
}
}
v___jp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___y_2225_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1 + 1, v___y_2225_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
if (v_isShared_2223_ == 0)
{
v___x_2230_ = v___x_2222_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_fst_2219_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_snd_2220_);
v___x_2230_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2230_);
v___x_2232_ = v___x_2217_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_fst_2215_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v___x_2232_);
lean_ctor_set(v___x_2212_, 0, v___x_2228_);
v___x_2234_ = v___x_2212_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
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
lean_object* v_a_2335_ = _args[0];
lean_object* v___y_2336_ = _args[1];
lean_object* v_eq_2337_ = _args[2];
lean_object* v_a_2338_ = _args[3];
lean_object* v_b_2339_ = _args[4];
lean_object* v_a_2340_ = _args[5];
lean_object* v___y_2341_ = _args[6];
lean_object* v___y_2342_ = _args[7];
lean_object* v___y_2343_ = _args[8];
lean_object* v___y_2344_ = _args[9];
lean_object* v___y_2345_ = _args[10];
lean_object* v___y_2346_ = _args[11];
lean_object* v___y_2347_ = _args[12];
lean_object* v___y_2348_ = _args[13];
lean_object* v___y_2349_ = _args[14];
lean_object* v___y_2350_ = _args[15];
lean_object* v___y_2351_ = _args[16];
_start:
{
uint8_t v_a_33893__boxed_2352_; lean_object* v_res_2353_; 
v_a_33893__boxed_2352_ = lean_unbox(v_a_2335_);
v_res_2353_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_33893__boxed_2352_, v___y_2336_, v_eq_2337_, v_a_2338_, v_b_2339_, v_a_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2354_, lean_object* v_b_2355_, lean_object* v_eq_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
uint8_t v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2401_; lean_object* v___x_2437_; 
lean_inc_ref(v_eq_2356_);
v___x_2437_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2356_, v_a_2357_, v_a_2361_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; uint8_t v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
v___x_2439_ = lean_unbox(v_a_2438_);
lean_dec(v_a_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
lean_dec_ref_known(v___x_2437_, 1);
lean_inc_ref(v_eq_2356_);
v___x_2440_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2356_, v_a_2357_, v_a_2361_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
v___y_2401_ = v___x_2440_;
goto v___jp_2400_;
}
else
{
v___y_2401_ = v___x_2437_;
goto v___jp_2400_;
}
}
else
{
v___y_2401_ = v___x_2437_;
goto v___jp_2400_;
}
v___jp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2371_ = l_Lean_Expr_getAppNumArgs(v_a_2354_);
v___x_2372_ = lean_box(0);
lean_inc_ref(v_b_2355_);
lean_inc_ref(v_a_2354_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_a_2354_);
lean_ctor_set(v___x_2373_, 1, v_b_2355_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2372_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2369_, v___y_2370_, v_eq_2356_, v_a_2354_, v_b_2355_, v___x_2375_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2391_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_fst_2381_; 
v_fst_2381_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_fst_2381_);
lean_dec(v_a_2377_);
if (lean_obj_tag(v_fst_2381_) == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2382_ = lean_unsigned_to_nat(2u);
v___x_2383_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*1, v___y_2369_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*1 + 1, v___y_2369_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2383_);
v___x_2385_ = v___x_2379_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2389_; 
v_val_2387_ = lean_ctor_get(v_fst_2381_, 0);
lean_inc(v_val_2387_);
lean_dec_ref_known(v_fst_2381_, 1);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v_val_2387_);
v___x_2389_ = v___x_2379_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_val_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2376_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2376_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
v___jp_2400_:
{
if (lean_obj_tag(v___y_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2428_; 
v_a_2402_ = lean_ctor_get(v___y_2401_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___y_2401_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2404_ = v___y_2401_;
v_isShared_2405_ = v_isSharedCheck_2428_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___y_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2428_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_unbox(v_a_2402_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v_toGoalState_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2404_);
v___x_2407_ = lean_st_ref_get(v_a_2357_);
v_toGoalState_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v___x_2407_, 1);
lean_dec(v_unused_2423_);
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_toGoalState_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_split_2412_; lean_object* v_argPosMap_2413_; lean_object* v___x_2415_; 
v_split_2412_ = lean_ctor_get(v_toGoalState_2408_, 14);
lean_inc_ref(v_split_2412_);
lean_dec_ref(v_toGoalState_2408_);
v_argPosMap_2413_ = lean_ctor_get(v_split_2412_, 6);
lean_inc_ref(v_argPosMap_2413_);
lean_dec_ref(v_split_2412_);
lean_inc_ref(v_b_2355_);
lean_inc_ref(v_a_2354_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v_b_2355_);
lean_ctor_set(v___x_2410_, 0, v_a_2354_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2354_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_b_2355_);
v___x_2415_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2413_, v___x_2415_);
lean_dec_ref(v___x_2415_);
lean_dec_ref(v_argPosMap_2413_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
v___y_2369_ = v___x_2418_;
v___y_2370_ = v___x_2417_;
goto v___jp_2368_;
}
else
{
lean_object* v_val_2419_; uint8_t v___x_2420_; 
v_val_2419_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_val_2419_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2420_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
v___y_2369_ = v___x_2420_;
v___y_2370_ = v_val_2419_;
goto v___jp_2368_;
}
}
}
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec(v_a_2402_);
lean_dec_ref(v_eq_2356_);
lean_dec_ref(v_b_2355_);
lean_dec_ref(v_a_2354_);
v___x_2424_ = lean_box(0);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2424_);
v___x_2426_ = v___x_2404_;
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
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v_eq_2356_);
lean_dec_ref(v_b_2355_);
lean_dec_ref(v_a_2354_);
v_a_2429_ = lean_ctor_get(v___y_2401_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___y_2401_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___y_2401_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___y_2401_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2441_, lean_object* v_b_2442_, lean_object* v_eq_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2441_, v_b_2442_, v_eq_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec(v_a_2444_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2456_, lean_object* v___y_2457_, lean_object* v_eq_2458_, lean_object* v_a_2459_, lean_object* v_b_2460_, lean_object* v_inst_2461_, lean_object* v_a_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2456_, v___y_2457_, v_eq_2458_, v_a_2459_, v_b_2460_, v_a_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2475_ = _args[0];
lean_object* v___y_2476_ = _args[1];
lean_object* v_eq_2477_ = _args[2];
lean_object* v_a_2478_ = _args[3];
lean_object* v_b_2479_ = _args[4];
lean_object* v_inst_2480_ = _args[5];
lean_object* v_a_2481_ = _args[6];
lean_object* v___y_2482_ = _args[7];
lean_object* v___y_2483_ = _args[8];
lean_object* v___y_2484_ = _args[9];
lean_object* v___y_2485_ = _args[10];
lean_object* v___y_2486_ = _args[11];
lean_object* v___y_2487_ = _args[12];
lean_object* v___y_2488_ = _args[13];
lean_object* v___y_2489_ = _args[14];
lean_object* v___y_2490_ = _args[15];
lean_object* v___y_2491_ = _args[16];
lean_object* v___y_2492_ = _args[17];
_start:
{
uint8_t v_a_34375__boxed_2493_; lean_object* v_res_2494_; 
v_a_34375__boxed_2493_ = lean_unbox(v_a_2475_);
v_res_2494_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34375__boxed_2493_, v___y_2476_, v_eq_2477_, v_a_2478_, v_b_2479_, v_inst_2480_, v_a_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2495_, lean_object* v_m_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2496_, v_a_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2499_, lean_object* v_m_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2499_, v_m_2500_, v_a_2501_);
lean_dec_ref(v_a_2501_);
lean_dec_ref(v_m_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2503_, lean_object* v_a_2504_, lean_object* v_x_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2504_, v_x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2507_, lean_object* v_a_2508_, lean_object* v_x_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2507_, v_a_2508_, v_x_2509_);
lean_dec(v_x_2509_);
lean_dec_ref(v_a_2508_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
uint8_t v___y_2520_; uint8_t v___y_2525_; lean_object* v___y_2526_; lean_object* v___x_2545_; 
lean_inc_ref(v_imp_2511_);
v___x_2545_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; uint8_t v___x_2547_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = lean_unbox(v_a_2546_);
lean_dec(v_a_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2562_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2562_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2562_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_unbox(v_a_2549_);
lean_dec(v_a_2549_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_box(1);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2554_);
v___x_2556_ = v___x_2551_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_box(0);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2558_);
v___x_2560_ = v___x_2551_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
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
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2548_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2548_);
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
}
else
{
lean_object* v_binderType_2571_; lean_object* v_body_2572_; lean_object* v___y_2574_; lean_object* v___x_2602_; 
v_binderType_2571_ = lean_ctor_get(v_imp_2511_, 1);
lean_inc_ref_n(v_binderType_2571_, 2);
v_body_2572_ = lean_ctor_get(v_imp_2511_, 2);
lean_inc_ref(v_body_2572_);
lean_dec_ref(v_imp_2511_);
v___x_2602_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2571_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; uint8_t v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
v___x_2604_ = lean_unbox(v_a_2603_);
lean_dec(v_a_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2602_, 1);
v___x_2605_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2571_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
v___y_2574_ = v___x_2605_;
goto v___jp_2573_;
}
else
{
lean_dec_ref(v_binderType_2571_);
v___y_2574_ = v___x_2602_;
goto v___jp_2573_;
}
}
else
{
lean_dec_ref(v_binderType_2571_);
v___y_2574_ = v___x_2602_;
goto v___jp_2573_;
}
v___jp_2573_:
{
if (lean_obj_tag(v___y_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2593_; 
v_a_2575_ = lean_ctor_get(v___y_2574_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___y_2574_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2577_ = v___y_2574_;
v_isShared_2578_ = v_isSharedCheck_2593_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___y_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2593_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_unbox(v_a_2575_);
if (v___x_2579_ == 0)
{
uint8_t v___x_2580_; 
lean_del_object(v___x_2577_);
v___x_2580_ = l_Lean_Expr_hasLooseBVars(v_body_2572_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
lean_inc_ref(v_body_2572_);
v___x_2581_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2572_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; uint8_t v___x_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
v___x_2583_ = lean_unbox(v_a_2582_);
lean_dec(v_a_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
lean_dec_ref_known(v___x_2581_, 1);
v___x_2584_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2572_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
v___x_2585_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
v___y_2525_ = v___x_2585_;
v___y_2526_ = v___x_2584_;
goto v___jp_2524_;
}
else
{
uint8_t v___x_2586_; 
lean_dec_ref(v_body_2572_);
v___x_2586_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
v___y_2525_ = v___x_2586_;
v___y_2526_ = v___x_2581_;
goto v___jp_2524_;
}
}
else
{
uint8_t v___x_2587_; 
lean_dec_ref(v_body_2572_);
v___x_2587_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
v___y_2525_ = v___x_2587_;
v___y_2526_ = v___x_2581_;
goto v___jp_2524_;
}
}
else
{
uint8_t v___x_2588_; 
lean_dec_ref(v_body_2572_);
v___x_2588_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
v___y_2520_ = v___x_2588_;
goto v___jp_2519_;
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_body_2572_);
v___x_2589_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2589_);
v___x_2591_ = v___x_2577_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_body_2572_);
v_a_2594_ = lean_ctor_get(v___y_2574_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___y_2574_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___y_2574_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___y_2574_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_imp_2511_);
v_a_2606_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2545_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2545_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_unsigned_to_nat(2u);
v___x_2522_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*1, v___y_2520_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*1 + 1, v___y_2520_);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
v___jp_2524_:
{
if (lean_obj_tag(v___y_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2536_; 
v_a_2527_ = lean_ctor_get(v___y_2526_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___y_2526_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2529_ = v___y_2526_;
v_isShared_2530_ = v_isSharedCheck_2536_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___y_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2536_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_unbox(v_a_2527_);
lean_dec(v_a_2527_);
if (v___x_2531_ == 0)
{
lean_del_object(v___x_2529_);
v___y_2520_ = v___y_2525_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_box(0);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2532_);
v___x_2534_ = v___x_2529_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_a_2537_ = lean_ctor_get(v___y_2526_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___y_2526_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___y_2526_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___y_2526_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2623_, lean_object* v_h_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2623_, v_a_2625_, v_a_2629_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2637_, lean_object* v_h_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2637_, v_h_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec(v_a_2639_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
switch(lean_obj_tag(v_s_2651_))
{
case 0:
{
lean_object* v_e_2663_; lean_object* v___x_2664_; 
v_e_2663_ = lean_ctor_get(v_s_2651_, 0);
lean_inc_ref(v_e_2663_);
lean_dec_ref_known(v_s_2651_, 2);
v___x_2664_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2663_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2664_;
}
case 1:
{
lean_object* v_e_2665_; lean_object* v___x_2666_; 
v_e_2665_ = lean_ctor_get(v_s_2651_, 0);
lean_inc_ref(v_e_2665_);
lean_dec_ref_known(v_s_2651_, 2);
v___x_2666_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2665_, v_a_2652_, v_a_2656_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2666_;
}
default: 
{
lean_object* v_a_2667_; lean_object* v_b_2668_; lean_object* v_eq_2669_; lean_object* v___x_2670_; 
v_a_2667_ = lean_ctor_get(v_s_2651_, 0);
lean_inc_ref(v_a_2667_);
v_b_2668_ = lean_ctor_get(v_s_2651_, 1);
lean_inc_ref(v_b_2668_);
v_eq_2669_ = lean_ctor_get(v_s_2651_, 3);
lean_inc_ref(v_eq_2669_);
lean_dec_ref_known(v_s_2651_, 5);
v___x_2670_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2667_, v_b_2668_, v_eq_2669_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec(v_a_2672_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2684_){
_start:
{
if (lean_obj_tag(v_x_2684_) == 0)
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
return v___x_2685_;
}
else
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_unsigned_to_nat(1u);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2687_);
lean_dec(v_x_2687_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2689_, lean_object* v_k_2690_){
_start:
{
if (lean_obj_tag(v_t_2689_) == 0)
{
return v_k_2690_;
}
else
{
lean_object* v_c_2691_; lean_object* v_numCases_2692_; uint8_t v_isRec_2693_; uint8_t v_tryPostpone_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_c_2691_ = lean_ctor_get(v_t_2689_, 0);
lean_inc_ref(v_c_2691_);
v_numCases_2692_ = lean_ctor_get(v_t_2689_, 1);
lean_inc(v_numCases_2692_);
v_isRec_2693_ = lean_ctor_get_uint8(v_t_2689_, sizeof(void*)*2);
v_tryPostpone_2694_ = lean_ctor_get_uint8(v_t_2689_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2689_, 2);
v___x_2695_ = lean_box(v_isRec_2693_);
v___x_2696_ = lean_box(v_tryPostpone_2694_);
v___x_2697_ = lean_apply_4(v_k_2690_, v_c_2691_, v_numCases_2692_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2698_, lean_object* v_ctorIdx_2699_, lean_object* v_t_2700_, lean_object* v_h_2701_, lean_object* v_k_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2700_, v_k_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2704_, lean_object* v_ctorIdx_2705_, lean_object* v_t_2706_, lean_object* v_h_2707_, lean_object* v_k_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2704_, v_ctorIdx_2705_, v_t_2706_, v_h_2707_, v_k_2708_);
lean_dec(v_ctorIdx_2705_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2710_, lean_object* v_none_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2710_, v_none_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2713_, lean_object* v_t_2714_, lean_object* v_h_2715_, lean_object* v_none_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2714_, v_none_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2718_, lean_object* v_some_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2718_, v_some_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2721_, lean_object* v_t_2722_, lean_object* v_h_2723_, lean_object* v_some_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2722_, v_some_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2726_, lean_object* v_as_2727_, size_t v_i_2728_, size_t v_stop_2729_){
_start:
{
uint8_t v___x_2730_; 
v___x_2730_ = lean_usize_dec_eq(v_i_2728_, v_stop_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_array_uget_borrowed(v_as_2727_, v_i_2728_);
v___x_2732_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2731_, v_a_2726_);
if (v___x_2732_ == 0)
{
size_t v___x_2733_; size_t v___x_2734_; 
v___x_2733_ = ((size_t)1ULL);
v___x_2734_ = lean_usize_add(v_i_2728_, v___x_2733_);
v_i_2728_ = v___x_2734_;
goto _start;
}
else
{
return v___x_2732_;
}
}
else
{
uint8_t v___x_2736_; 
v___x_2736_ = 0;
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2737_, lean_object* v_as_2738_, lean_object* v_i_2739_, lean_object* v_stop_2740_){
_start:
{
uint64_t v_a_2506__boxed_2741_; size_t v_i_boxed_2742_; size_t v_stop_boxed_2743_; uint8_t v_res_2744_; lean_object* v_r_2745_; 
v_a_2506__boxed_2741_ = lean_unbox_uint64(v_a_2737_);
lean_dec_ref(v_a_2737_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2739_);
lean_dec(v_i_2739_);
v_stop_boxed_2743_ = lean_unbox_usize(v_stop_2740_);
lean_dec(v_stop_2740_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2506__boxed_2741_, v_as_2738_, v_i_boxed_2742_, v_stop_boxed_2743_);
lean_dec_ref(v_as_2738_);
v_r_2745_ = lean_box(v_res_2744_);
return v_r_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2748_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2801_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2801_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2801_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
if (lean_obj_tag(v_a_2758_) == 1)
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
lean_del_object(v___x_2760_);
v_val_2762_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_val_2762_);
lean_dec_ref_known(v_a_2758_, 1);
v___x_2763_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2787_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2787_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2787_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = lean_array_get_size(v_val_2762_);
v___x_2770_ = lean_nat_dec_lt(v___x_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
lean_dec(v_a_2764_);
lean_dec(v_val_2762_);
v___x_2771_ = lean_box(v___x_2770_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2771_);
v___x_2773_ = v___x_2766_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
else
{
if (v___x_2770_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_dec(v_a_2764_);
lean_dec(v_val_2762_);
v___x_2775_ = lean_box(v___x_2770_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2775_);
v___x_2777_ = v___x_2766_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
size_t v___x_2779_; size_t v___x_2780_; uint64_t v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2779_ = ((size_t)0ULL);
v___x_2780_ = lean_usize_of_nat(v___x_2769_);
v___x_2781_ = lean_unbox_uint64(v_a_2764_);
lean_dec(v_a_2764_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2781_, v_val_2762_, v___x_2779_, v___x_2780_);
lean_dec(v_val_2762_);
v___x_2783_ = lean_box(v___x_2782_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2783_);
v___x_2785_ = v___x_2766_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_val_2762_);
v_a_2788_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2763_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2763_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_dec(v_a_2758_);
v___x_2796_ = 1;
v___x_2797_ = lean_box(v___x_2796_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2797_);
v___x_2799_ = v___x_2760_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2757_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2757_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_c_2810_);
return v_res_2821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2825_, lean_object* v_c_x3f_2826_, lean_object* v_cs_x27_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
if (lean_obj_tag(v_cs_2825_) == 0)
{
lean_object* v___x_2839_; lean_object* v_toGoalState_2840_; lean_object* v_split_2841_; lean_object* v_mvarId_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2950_; 
v___x_2839_ = lean_st_ref_take(v_a_2828_);
v_toGoalState_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc_ref(v_toGoalState_2840_);
v_split_2841_ = lean_ctor_get(v_toGoalState_2840_, 14);
lean_inc_ref(v_split_2841_);
v_mvarId_2842_ = lean_ctor_get(v___x_2839_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2839_, 0);
lean_dec(v_unused_2951_);
v___x_2844_ = v___x_2839_;
v_isShared_2845_ = v_isSharedCheck_2950_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_mvarId_2842_);
lean_dec(v___x_2839_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2950_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_nextDeclIdx_2846_; lean_object* v_enodeMap_2847_; lean_object* v_exprs_2848_; lean_object* v_parents_2849_; lean_object* v_congrTable_2850_; lean_object* v_appMap_2851_; lean_object* v_indicesFound_2852_; lean_object* v_newFacts_2853_; uint8_t v_inconsistent_2854_; lean_object* v_nextIdx_2855_; lean_object* v_newRawFacts_2856_; lean_object* v_facts_2857_; lean_object* v_extThms_2858_; lean_object* v_ematch_2859_; lean_object* v_inj_2860_; lean_object* v_clean_2861_; lean_object* v_sstates_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2948_; 
v_nextDeclIdx_2846_ = lean_ctor_get(v_toGoalState_2840_, 0);
v_enodeMap_2847_ = lean_ctor_get(v_toGoalState_2840_, 1);
v_exprs_2848_ = lean_ctor_get(v_toGoalState_2840_, 2);
v_parents_2849_ = lean_ctor_get(v_toGoalState_2840_, 3);
v_congrTable_2850_ = lean_ctor_get(v_toGoalState_2840_, 4);
v_appMap_2851_ = lean_ctor_get(v_toGoalState_2840_, 5);
v_indicesFound_2852_ = lean_ctor_get(v_toGoalState_2840_, 6);
v_newFacts_2853_ = lean_ctor_get(v_toGoalState_2840_, 7);
v_inconsistent_2854_ = lean_ctor_get_uint8(v_toGoalState_2840_, sizeof(void*)*17);
v_nextIdx_2855_ = lean_ctor_get(v_toGoalState_2840_, 8);
v_newRawFacts_2856_ = lean_ctor_get(v_toGoalState_2840_, 9);
v_facts_2857_ = lean_ctor_get(v_toGoalState_2840_, 10);
v_extThms_2858_ = lean_ctor_get(v_toGoalState_2840_, 11);
v_ematch_2859_ = lean_ctor_get(v_toGoalState_2840_, 12);
v_inj_2860_ = lean_ctor_get(v_toGoalState_2840_, 13);
v_clean_2861_ = lean_ctor_get(v_toGoalState_2840_, 15);
v_sstates_2862_ = lean_ctor_get(v_toGoalState_2840_, 16);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_toGoalState_2840_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v_toGoalState_2840_, 14);
lean_dec(v_unused_2949_);
v___x_2864_ = v_toGoalState_2840_;
v_isShared_2865_ = v_isSharedCheck_2948_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_sstates_2862_);
lean_inc(v_clean_2861_);
lean_inc(v_inj_2860_);
lean_inc(v_ematch_2859_);
lean_inc(v_extThms_2858_);
lean_inc(v_facts_2857_);
lean_inc(v_newRawFacts_2856_);
lean_inc(v_nextIdx_2855_);
lean_inc(v_newFacts_2853_);
lean_inc(v_indicesFound_2852_);
lean_inc(v_appMap_2851_);
lean_inc(v_congrTable_2850_);
lean_inc(v_parents_2849_);
lean_inc(v_exprs_2848_);
lean_inc(v_enodeMap_2847_);
lean_inc(v_nextDeclIdx_2846_);
lean_dec(v_toGoalState_2840_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2948_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_num_2866_; lean_object* v_added_2867_; lean_object* v_resolved_2868_; lean_object* v_trace_2869_; lean_object* v_lookaheads_2870_; lean_object* v_argPosMap_2871_; lean_object* v_argsAt_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2946_; 
v_num_2866_ = lean_ctor_get(v_split_2841_, 0);
v_added_2867_ = lean_ctor_get(v_split_2841_, 2);
v_resolved_2868_ = lean_ctor_get(v_split_2841_, 3);
v_trace_2869_ = lean_ctor_get(v_split_2841_, 4);
v_lookaheads_2870_ = lean_ctor_get(v_split_2841_, 5);
v_argPosMap_2871_ = lean_ctor_get(v_split_2841_, 6);
v_argsAt_2872_ = lean_ctor_get(v_split_2841_, 7);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_split_2841_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v_split_2841_, 1);
lean_dec(v_unused_2947_);
v___x_2874_ = v_split_2841_;
v_isShared_2875_ = v_isSharedCheck_2946_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_argsAt_2872_);
lean_inc(v_argPosMap_2871_);
lean_inc(v_lookaheads_2870_);
lean_inc(v_trace_2869_);
lean_inc(v_resolved_2868_);
lean_inc(v_added_2867_);
lean_inc(v_num_2866_);
lean_dec(v_split_2841_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2946_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = l_List_reverse___redArg(v_cs_x27_2827_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2876_);
v___x_2878_ = v___x_2874_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_num_2866_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_added_2867_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_resolved_2868_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_trace_2869_);
lean_ctor_set(v_reuseFailAlloc_2945_, 5, v_lookaheads_2870_);
lean_ctor_set(v_reuseFailAlloc_2945_, 6, v_argPosMap_2871_);
lean_ctor_set(v_reuseFailAlloc_2945_, 7, v_argsAt_2872_);
v___x_2878_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 14, v___x_2878_);
v___x_2880_ = v___x_2864_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_nextDeclIdx_2846_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_enodeMap_2847_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_exprs_2848_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v_parents_2849_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v_congrTable_2850_);
lean_ctor_set(v_reuseFailAlloc_2944_, 5, v_appMap_2851_);
lean_ctor_set(v_reuseFailAlloc_2944_, 6, v_indicesFound_2852_);
lean_ctor_set(v_reuseFailAlloc_2944_, 7, v_newFacts_2853_);
lean_ctor_set(v_reuseFailAlloc_2944_, 8, v_nextIdx_2855_);
lean_ctor_set(v_reuseFailAlloc_2944_, 9, v_newRawFacts_2856_);
lean_ctor_set(v_reuseFailAlloc_2944_, 10, v_facts_2857_);
lean_ctor_set(v_reuseFailAlloc_2944_, 11, v_extThms_2858_);
lean_ctor_set(v_reuseFailAlloc_2944_, 12, v_ematch_2859_);
lean_ctor_set(v_reuseFailAlloc_2944_, 13, v_inj_2860_);
lean_ctor_set(v_reuseFailAlloc_2944_, 14, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2944_, 15, v_clean_2861_);
lean_ctor_set(v_reuseFailAlloc_2944_, 16, v_sstates_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_2944_, sizeof(void*)*17, v_inconsistent_2854_);
v___x_2880_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2880_);
v___x_2882_ = v___x_2844_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_mvarId_2842_);
v___x_2882_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_st_ref_put(v_a_2828_, v___x_2882_);
if (lean_obj_tag(v_c_x3f_2826_) == 1)
{
lean_object* v___x_2884_; lean_object* v_toGoalState_2885_; lean_object* v_ematch_2886_; lean_object* v_mvarId_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2940_; 
v___x_2884_ = lean_st_ref_take(v_a_2828_);
v_toGoalState_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_toGoalState_2885_);
v_ematch_2886_ = lean_ctor_get(v_toGoalState_2885_, 12);
lean_inc_ref(v_ematch_2886_);
v_mvarId_2887_ = lean_ctor_get(v___x_2884_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2941_);
v___x_2889_ = v___x_2884_;
v_isShared_2890_ = v_isSharedCheck_2940_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_mvarId_2887_);
lean_dec(v___x_2884_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2940_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v_nextDeclIdx_2891_; lean_object* v_enodeMap_2892_; lean_object* v_exprs_2893_; lean_object* v_parents_2894_; lean_object* v_congrTable_2895_; lean_object* v_appMap_2896_; lean_object* v_indicesFound_2897_; lean_object* v_newFacts_2898_; uint8_t v_inconsistent_2899_; lean_object* v_nextIdx_2900_; lean_object* v_newRawFacts_2901_; lean_object* v_facts_2902_; lean_object* v_extThms_2903_; lean_object* v_inj_2904_; lean_object* v_split_2905_; lean_object* v_clean_2906_; lean_object* v_sstates_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2938_; 
v_nextDeclIdx_2891_ = lean_ctor_get(v_toGoalState_2885_, 0);
v_enodeMap_2892_ = lean_ctor_get(v_toGoalState_2885_, 1);
v_exprs_2893_ = lean_ctor_get(v_toGoalState_2885_, 2);
v_parents_2894_ = lean_ctor_get(v_toGoalState_2885_, 3);
v_congrTable_2895_ = lean_ctor_get(v_toGoalState_2885_, 4);
v_appMap_2896_ = lean_ctor_get(v_toGoalState_2885_, 5);
v_indicesFound_2897_ = lean_ctor_get(v_toGoalState_2885_, 6);
v_newFacts_2898_ = lean_ctor_get(v_toGoalState_2885_, 7);
v_inconsistent_2899_ = lean_ctor_get_uint8(v_toGoalState_2885_, sizeof(void*)*17);
v_nextIdx_2900_ = lean_ctor_get(v_toGoalState_2885_, 8);
v_newRawFacts_2901_ = lean_ctor_get(v_toGoalState_2885_, 9);
v_facts_2902_ = lean_ctor_get(v_toGoalState_2885_, 10);
v_extThms_2903_ = lean_ctor_get(v_toGoalState_2885_, 11);
v_inj_2904_ = lean_ctor_get(v_toGoalState_2885_, 13);
v_split_2905_ = lean_ctor_get(v_toGoalState_2885_, 14);
v_clean_2906_ = lean_ctor_get(v_toGoalState_2885_, 15);
v_sstates_2907_ = lean_ctor_get(v_toGoalState_2885_, 16);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_toGoalState_2885_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_toGoalState_2885_, 12);
lean_dec(v_unused_2939_);
v___x_2909_ = v_toGoalState_2885_;
v_isShared_2910_ = v_isSharedCheck_2938_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_sstates_2907_);
lean_inc(v_clean_2906_);
lean_inc(v_split_2905_);
lean_inc(v_inj_2904_);
lean_inc(v_extThms_2903_);
lean_inc(v_facts_2902_);
lean_inc(v_newRawFacts_2901_);
lean_inc(v_nextIdx_2900_);
lean_inc(v_newFacts_2898_);
lean_inc(v_indicesFound_2897_);
lean_inc(v_appMap_2896_);
lean_inc(v_congrTable_2895_);
lean_inc(v_parents_2894_);
lean_inc(v_exprs_2893_);
lean_inc(v_enodeMap_2892_);
lean_inc(v_nextDeclIdx_2891_);
lean_dec(v_toGoalState_2885_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2938_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_thmMap_2911_; lean_object* v_gmt_2912_; lean_object* v_thms_2913_; lean_object* v_newThms_2914_; lean_object* v_numInstances_2915_; lean_object* v_numDelayedInstances_2916_; lean_object* v_preInstances_2917_; lean_object* v_nextThmIdx_2918_; lean_object* v_matchEqNames_2919_; lean_object* v_delayedThmInsts_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2936_; 
v_thmMap_2911_ = lean_ctor_get(v_ematch_2886_, 0);
v_gmt_2912_ = lean_ctor_get(v_ematch_2886_, 1);
v_thms_2913_ = lean_ctor_get(v_ematch_2886_, 2);
v_newThms_2914_ = lean_ctor_get(v_ematch_2886_, 3);
v_numInstances_2915_ = lean_ctor_get(v_ematch_2886_, 4);
v_numDelayedInstances_2916_ = lean_ctor_get(v_ematch_2886_, 5);
v_preInstances_2917_ = lean_ctor_get(v_ematch_2886_, 7);
v_nextThmIdx_2918_ = lean_ctor_get(v_ematch_2886_, 8);
v_matchEqNames_2919_ = lean_ctor_get(v_ematch_2886_, 9);
v_delayedThmInsts_2920_ = lean_ctor_get(v_ematch_2886_, 10);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_ematch_2886_);
if (v_isSharedCheck_2936_ == 0)
{
lean_object* v_unused_2937_; 
v_unused_2937_ = lean_ctor_get(v_ematch_2886_, 6);
lean_dec(v_unused_2937_);
v___x_2922_ = v_ematch_2886_;
v_isShared_2923_ = v_isSharedCheck_2936_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_delayedThmInsts_2920_);
lean_inc(v_matchEqNames_2919_);
lean_inc(v_nextThmIdx_2918_);
lean_inc(v_preInstances_2917_);
lean_inc(v_numDelayedInstances_2916_);
lean_inc(v_numInstances_2915_);
lean_inc(v_newThms_2914_);
lean_inc(v_thms_2913_);
lean_inc(v_gmt_2912_);
lean_inc(v_thmMap_2911_);
lean_dec(v_ematch_2886_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2936_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 6, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_thmMap_2911_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_gmt_2912_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_thms_2913_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_newThms_2914_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v_numInstances_2915_);
lean_ctor_set(v_reuseFailAlloc_2935_, 5, v_numDelayedInstances_2916_);
lean_ctor_set(v_reuseFailAlloc_2935_, 6, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2935_, 7, v_preInstances_2917_);
lean_ctor_set(v_reuseFailAlloc_2935_, 8, v_nextThmIdx_2918_);
lean_ctor_set(v_reuseFailAlloc_2935_, 9, v_matchEqNames_2919_);
lean_ctor_set(v_reuseFailAlloc_2935_, 10, v_delayedThmInsts_2920_);
v___x_2926_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2928_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 12, v___x_2926_);
v___x_2928_ = v___x_2909_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_nextDeclIdx_2891_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_enodeMap_2892_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_exprs_2893_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_parents_2894_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_congrTable_2895_);
lean_ctor_set(v_reuseFailAlloc_2934_, 5, v_appMap_2896_);
lean_ctor_set(v_reuseFailAlloc_2934_, 6, v_indicesFound_2897_);
lean_ctor_set(v_reuseFailAlloc_2934_, 7, v_newFacts_2898_);
lean_ctor_set(v_reuseFailAlloc_2934_, 8, v_nextIdx_2900_);
lean_ctor_set(v_reuseFailAlloc_2934_, 9, v_newRawFacts_2901_);
lean_ctor_set(v_reuseFailAlloc_2934_, 10, v_facts_2902_);
lean_ctor_set(v_reuseFailAlloc_2934_, 11, v_extThms_2903_);
lean_ctor_set(v_reuseFailAlloc_2934_, 12, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2934_, 13, v_inj_2904_);
lean_ctor_set(v_reuseFailAlloc_2934_, 14, v_split_2905_);
lean_ctor_set(v_reuseFailAlloc_2934_, 15, v_clean_2906_);
lean_ctor_set(v_reuseFailAlloc_2934_, 16, v_sstates_2907_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*17, v_inconsistent_2899_);
v___x_2928_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v___x_2928_);
v___x_2930_ = v___x_2889_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_mvarId_2887_);
v___x_2930_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_st_ref_put(v_a_2828_, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_c_x3f_2826_);
return v___x_2932_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_c_x3f_2826_);
return v___x_2942_;
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
lean_object* v_head_2952_; lean_object* v_tail_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3171_; 
v_head_2952_ = lean_ctor_get(v_cs_2825_, 0);
v_tail_2953_ = lean_ctor_get(v_cs_2825_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_cs_2825_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_2955_ = v_cs_2825_;
v_isShared_2956_ = v_isSharedCheck_3171_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_tail_2953_);
lean_inc(v_head_2952_);
lean_dec(v_cs_2825_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3171_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; uint8_t v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2991_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3028_; lean_object* v___y_3029_; uint8_t v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3054_; lean_object* v___y_3055_; uint8_t v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; uint8_t v___y_3063_; lean_object* v___x_3066_; 
v___x_3066_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2952_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; uint8_t v___x_3068_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
v___x_3068_ = lean_unbox(v_a_3067_);
lean_dec(v_a_3067_);
if (v___x_3068_ == 0)
{
lean_del_object(v___x_2955_);
lean_dec(v_head_2952_);
v_cs_2825_ = v_tail_2953_;
goto _start;
}
else
{
lean_object* v_toCold_3070_; lean_object* v_options_3071_; lean_object* v_inheritedTraceOptions_3072_; uint8_t v_hasTrace_3073_; uint8_t v___x_3074_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; uint8_t v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; 
v_toCold_3070_ = lean_ctor_get(v_a_2836_, 0);
v_options_3071_ = lean_ctor_get(v_toCold_3070_, 2);
v_inheritedTraceOptions_3072_ = lean_ctor_get(v_toCold_3070_, 11);
v_hasTrace_3073_ = lean_ctor_get_uint8(v_options_3071_, sizeof(void*)*1);
v___x_3074_ = 0;
if (v_hasTrace_3073_ == 0)
{
v___y_3097_ = v_a_2828_;
v___y_3098_ = v_a_2829_;
v___y_3099_ = v_a_2830_;
v___y_3100_ = v_a_2831_;
v___y_3101_ = v_a_2832_;
v___y_3102_ = v_a_2833_;
v___y_3103_ = v_a_2834_;
v___y_3104_ = v_a_2835_;
v___y_3105_ = v_a_2836_;
v___y_3106_ = v_a_2837_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3072_, v_options_3071_, v___x_3139_);
if (v___x_3140_ == 0)
{
v___y_3097_ = v_a_2828_;
v___y_3098_ = v_a_2829_;
v___y_3099_ = v_a_2830_;
v___y_3100_ = v_a_2831_;
v___y_3101_ = v_a_2832_;
v___y_3102_ = v_a_2833_;
v___y_3103_ = v_a_2834_;
v___y_3104_ = v_a_2835_;
v___y_3105_ = v_a_2836_;
v___y_3106_ = v_a_2837_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Meta_Grind_updateLastTag(v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec_ref_known(v___x_3141_, 1);
v___x_3142_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3143_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2952_);
v___x_3144_ = l_Lean_MessageData_ofExpr(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3142_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3138_, v___x_3145_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_dec_ref_known(v___x_3146_, 1);
v___y_3097_ = v_a_2828_;
v___y_3098_ = v_a_2829_;
v___y_3099_ = v_a_2830_;
v___y_3100_ = v_a_2831_;
v___y_3101_ = v_a_2832_;
v___y_3102_ = v_a_2833_;
v___y_3103_ = v_a_2834_;
v___y_3104_ = v_a_2835_;
v___y_3105_ = v_a_2836_;
v___y_3106_ = v_a_2837_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3155_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3141_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3141_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
v___jp_3075_:
{
if (lean_obj_tag(v_c_x3f_2826_) == 0)
{
lean_object* v___x_3090_; 
lean_del_object(v___x_2955_);
v___x_3090_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3090_, 0, v_head_2952_);
lean_ctor_set(v___x_3090_, 1, v___y_3088_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*2, v___y_3083_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*2 + 1, v___y_3078_);
v_cs_2825_ = v_tail_2953_;
v_c_x3f_2826_ = v___x_3090_;
v_a_2828_ = v___y_3077_;
v_a_2829_ = v___y_3080_;
v_a_2830_ = v___y_3085_;
v_a_2831_ = v___y_3086_;
v_a_2832_ = v___y_3081_;
v_a_2833_ = v___y_3076_;
v_a_2834_ = v___y_3082_;
v_a_2835_ = v___y_3084_;
v_a_2836_ = v___y_3079_;
v_a_2837_ = v___y_3087_;
goto _start;
}
else
{
lean_object* v_c_3092_; lean_object* v_numCases_3093_; uint8_t v_tryPostpone_3094_; uint8_t v___x_3095_; 
v_c_3092_ = lean_ctor_get(v_c_x3f_2826_, 0);
v_numCases_3093_ = lean_ctor_get(v_c_x3f_2826_, 1);
v_tryPostpone_3094_ = lean_ctor_get_uint8(v_c_x3f_2826_, sizeof(void*)*2 + 1);
v___x_3095_ = lean_nat_dec_lt(v___y_3088_, v_numCases_3093_);
if (v_tryPostpone_3094_ == 0)
{
if (v___y_3078_ == 0)
{
lean_inc_ref(v_c_3092_);
lean_inc(v_numCases_3093_);
v___y_3047_ = v___y_3076_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3079_;
v___y_3051_ = v___y_3080_;
v___y_3052_ = v_numCases_3093_;
v___y_3053_ = v___y_3081_;
v___y_3054_ = v___x_3095_;
v___y_3055_ = v___y_3082_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3084_;
v___y_3058_ = v___y_3085_;
v___y_3059_ = v_c_3092_;
v___y_3060_ = v___y_3086_;
v___y_3061_ = v___y_3087_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___x_3074_;
goto v___jp_3046_;
}
else
{
lean_dec(v___y_3088_);
v___y_2958_ = v___y_3076_;
v___y_2959_ = v___y_3081_;
v___y_2960_ = v___y_3077_;
v___y_2961_ = v___y_3082_;
v___y_2962_ = v___y_3079_;
v___y_2963_ = v___y_3084_;
v___y_2964_ = v___y_3085_;
v___y_2965_ = v___y_3087_;
v___y_2966_ = v___y_3086_;
v___y_2967_ = v___y_3080_;
goto v___jp_2957_;
}
}
else
{
if (v___y_3078_ == 0)
{
lean_inc_ref(v_c_3092_);
lean_dec_ref_known(v_c_x3f_2826_, 2);
lean_del_object(v___x_2955_);
v___y_2973_ = v___y_3076_;
v___y_2974_ = v___y_3077_;
v___y_2975_ = v___y_3078_;
v___y_2976_ = v___y_3079_;
v___y_2977_ = v___y_3080_;
v___y_2978_ = v___y_3081_;
v___y_2979_ = v___y_3082_;
v___y_2980_ = v___y_3083_;
v___y_2981_ = v___y_3084_;
v___y_2982_ = v___y_3085_;
v___y_2983_ = v_c_3092_;
v___y_2984_ = v___y_3087_;
v___y_2985_ = v___y_3086_;
v___y_2986_ = v___y_3088_;
goto v___jp_2972_;
}
else
{
if (v___y_3089_ == 0)
{
lean_inc_ref(v_c_3092_);
lean_inc(v_numCases_3093_);
v___y_3047_ = v___y_3076_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3079_;
v___y_3051_ = v___y_3080_;
v___y_3052_ = v_numCases_3093_;
v___y_3053_ = v___y_3081_;
v___y_3054_ = v___x_3095_;
v___y_3055_ = v___y_3082_;
v___y_3056_ = v___y_3083_;
v___y_3057_ = v___y_3084_;
v___y_3058_ = v___y_3085_;
v___y_3059_ = v_c_3092_;
v___y_3060_ = v___y_3086_;
v___y_3061_ = v___y_3087_;
v___y_3062_ = v___y_3088_;
v___y_3063_ = v___y_3089_;
goto v___jp_3046_;
}
else
{
lean_inc_ref(v_c_3092_);
lean_dec_ref_known(v_c_x3f_2826_, 2);
lean_del_object(v___x_2955_);
v___y_2973_ = v___y_3076_;
v___y_2974_ = v___y_3077_;
v___y_2975_ = v___y_3078_;
v___y_2976_ = v___y_3079_;
v___y_2977_ = v___y_3080_;
v___y_2978_ = v___y_3081_;
v___y_2979_ = v___y_3082_;
v___y_2980_ = v___y_3083_;
v___y_2981_ = v___y_3084_;
v___y_2982_ = v___y_3085_;
v___y_2983_ = v_c_3092_;
v___y_2984_ = v___y_3087_;
v___y_2985_ = v___y_3086_;
v___y_2986_ = v___y_3088_;
goto v___jp_2972_;
}
}
}
}
}
v___jp_3096_:
{
lean_object* v___x_3107_; 
lean_inc(v_head_2952_);
v___x_3107_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2952_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
switch(lean_obj_tag(v_a_3108_))
{
case 0:
{
lean_del_object(v___x_2955_);
lean_dec(v_head_2952_);
v_cs_2825_ = v_tail_2953_;
v_a_2828_ = v___y_3097_;
v_a_2829_ = v___y_3098_;
v_a_2830_ = v___y_3099_;
v_a_2831_ = v___y_3100_;
v_a_2832_ = v___y_3101_;
v_a_2833_ = v___y_3102_;
v_a_2834_ = v___y_3103_;
v_a_2835_ = v___y_3104_;
v_a_2836_ = v___y_3105_;
v_a_2837_ = v___y_3106_;
goto _start;
}
case 1:
{
lean_object* v___x_3110_; 
lean_del_object(v___x_2955_);
v___x_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_head_2952_);
lean_ctor_set(v___x_3110_, 1, v_cs_x27_2827_);
v_cs_2825_ = v_tail_2953_;
v_cs_x27_2827_ = v___x_3110_;
v_a_2828_ = v___y_3097_;
v_a_2829_ = v___y_3098_;
v_a_2830_ = v___y_3099_;
v_a_2831_ = v___y_3100_;
v_a_2832_ = v___y_3101_;
v_a_2833_ = v___y_3102_;
v_a_2834_ = v___y_3103_;
v_a_2835_ = v___y_3104_;
v_a_2836_ = v___y_3105_;
v_a_2837_ = v___y_3106_;
goto _start;
}
default: 
{
lean_object* v_numCases_3112_; uint8_t v_isRec_3113_; uint8_t v_tryPostpone_3114_; lean_object* v___x_3115_; 
v_numCases_3112_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_numCases_3112_);
v_isRec_3113_ = lean_ctor_get_uint8(v_a_3108_, sizeof(void*)*1);
v_tryPostpone_3114_ = lean_ctor_get_uint8(v_a_3108_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3108_, 1);
v___x_3115_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3099_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; uint8_t v___x_3117_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3117_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
if (v___x_3117_ == 0)
{
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v_tryPostpone_3114_;
v___y_3079_ = v___y_3105_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3101_;
v___y_3082_ = v___y_3103_;
v___y_3083_ = v_isRec_3113_;
v___y_3084_ = v___y_3104_;
v___y_3085_ = v___y_3099_;
v___y_3086_ = v___y_3100_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v_numCases_3112_;
v___y_3089_ = v___x_3074_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_dec_lt(v___x_3118_, v_numCases_3112_);
if (v___x_3119_ == 0)
{
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v_tryPostpone_3114_;
v___y_3079_ = v___y_3105_;
v___y_3080_ = v___y_3098_;
v___y_3081_ = v___y_3101_;
v___y_3082_ = v___y_3103_;
v___y_3083_ = v_isRec_3113_;
v___y_3084_ = v___y_3104_;
v___y_3085_ = v___y_3099_;
v___y_3086_ = v___y_3100_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v_numCases_3112_;
v___y_3089_ = v___x_3119_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3120_; 
lean_dec(v_numCases_3112_);
lean_del_object(v___x_2955_);
v___x_3120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3120_, 0, v_head_2952_);
lean_ctor_set(v___x_3120_, 1, v_cs_x27_2827_);
v_cs_2825_ = v_tail_2953_;
v_cs_x27_2827_ = v___x_3120_;
v_a_2828_ = v___y_3097_;
v_a_2829_ = v___y_3098_;
v_a_2830_ = v___y_3099_;
v_a_2831_ = v___y_3100_;
v_a_2832_ = v___y_3101_;
v_a_2833_ = v___y_3102_;
v_a_2834_ = v___y_3103_;
v_a_2835_ = v___y_3104_;
v_a_2836_ = v___y_3105_;
v_a_2837_ = v___y_3106_;
goto _start;
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_numCases_3112_);
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3122_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3115_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3115_);
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
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3130_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3107_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3107_);
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
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3163_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3066_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3066_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
v___jp_2957_:
{
lean_object* v___x_2969_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v_cs_x27_2827_);
v___x_2969_ = v___x_2955_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_head_2952_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_cs_x27_2827_);
v___x_2969_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v_cs_2825_ = v_tail_2953_;
v_cs_x27_2827_ = v___x_2969_;
v_a_2828_ = v___y_2960_;
v_a_2829_ = v___y_2967_;
v_a_2830_ = v___y_2964_;
v_a_2831_ = v___y_2966_;
v_a_2832_ = v___y_2959_;
v_a_2833_ = v___y_2958_;
v_a_2834_ = v___y_2961_;
v_a_2835_ = v___y_2963_;
v_a_2836_ = v___y_2962_;
v_a_2837_ = v___y_2965_;
goto _start;
}
}
v___jp_2972_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2987_, 0, v_head_2952_);
lean_ctor_set(v___x_2987_, 1, v___y_2986_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*2, v___y_2980_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*2 + 1, v___y_2975_);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___y_2983_);
lean_ctor_set(v___x_2988_, 1, v_cs_x27_2827_);
v_cs_2825_ = v_tail_2953_;
v_c_x3f_2826_ = v___x_2987_;
v_cs_x27_2827_ = v___x_2988_;
v_a_2828_ = v___y_2974_;
v_a_2829_ = v___y_2977_;
v_a_2830_ = v___y_2982_;
v_a_2831_ = v___y_2985_;
v_a_2832_ = v___y_2978_;
v_a_2833_ = v___y_2973_;
v_a_2834_ = v___y_2979_;
v_a_2835_ = v___y_2981_;
v_a_2836_ = v___y_2976_;
v_a_2837_ = v___y_2984_;
goto _start;
}
v___jp_2990_:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2952_, v___y_2992_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3002_, v___y_2992_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; uint8_t v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = lean_nat_dec_lt(v_a_3007_, v_a_3009_);
lean_dec(v_a_3009_);
lean_dec(v_a_3007_);
if (v___x_3010_ == 0)
{
if (v___y_2997_ == 0)
{
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3002_);
v___y_2958_ = v___y_2991_;
v___y_2959_ = v___y_2996_;
v___y_2960_ = v___y_2992_;
v___y_2961_ = v___y_2998_;
v___y_2962_ = v___y_2994_;
v___y_2963_ = v___y_3000_;
v___y_2964_ = v___y_3001_;
v___y_2965_ = v___y_3003_;
v___y_2966_ = v___y_3004_;
v___y_2967_ = v___y_2995_;
goto v___jp_2957_;
}
else
{
lean_del_object(v___x_2955_);
lean_dec(v_c_x3f_2826_);
v___y_2973_ = v___y_2991_;
v___y_2974_ = v___y_2992_;
v___y_2975_ = v___y_2993_;
v___y_2976_ = v___y_2994_;
v___y_2977_ = v___y_2995_;
v___y_2978_ = v___y_2996_;
v___y_2979_ = v___y_2998_;
v___y_2980_ = v___y_2999_;
v___y_2981_ = v___y_3000_;
v___y_2982_ = v___y_3001_;
v___y_2983_ = v___y_3002_;
v___y_2984_ = v___y_3003_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
goto v___jp_2972_;
}
}
else
{
lean_del_object(v___x_2955_);
lean_dec(v_c_x3f_2826_);
v___y_2973_ = v___y_2991_;
v___y_2974_ = v___y_2992_;
v___y_2975_ = v___y_2993_;
v___y_2976_ = v___y_2994_;
v___y_2977_ = v___y_2995_;
v___y_2978_ = v___y_2996_;
v___y_2979_ = v___y_2998_;
v___y_2980_ = v___y_2999_;
v___y_2981_ = v___y_3000_;
v___y_2982_ = v___y_3001_;
v___y_2983_ = v___y_3002_;
v___y_2984_ = v___y_3003_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
goto v___jp_2972_;
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_a_3007_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3002_);
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3011_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3008_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3008_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3002_);
lean_del_object(v___x_2955_);
lean_dec(v_tail_2953_);
lean_dec(v_head_2952_);
lean_dec(v_cs_x27_2827_);
lean_dec(v_c_x3f_2826_);
v_a_3019_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3006_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3006_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
v___jp_3027_:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_dec_lt(v___x_3044_, v___y_3033_);
lean_dec(v___y_3033_);
if (v___x_3045_ == 0)
{
v___y_2991_ = v___y_3028_;
v___y_2992_ = v___y_3029_;
v___y_2993_ = v___y_3030_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3034_;
v___y_2997_ = v___y_3035_;
v___y_2998_ = v___y_3036_;
v___y_2999_ = v___y_3037_;
v___y_3000_ = v___y_3038_;
v___y_3001_ = v___y_3039_;
v___y_3002_ = v___y_3040_;
v___y_3003_ = v___y_3042_;
v___y_3004_ = v___y_3041_;
v___y_3005_ = v___y_3043_;
goto v___jp_2990_;
}
else
{
lean_del_object(v___x_2955_);
lean_dec(v_c_x3f_2826_);
v___y_2973_ = v___y_3028_;
v___y_2974_ = v___y_3029_;
v___y_2975_ = v___y_3030_;
v___y_2976_ = v___y_3031_;
v___y_2977_ = v___y_3032_;
v___y_2978_ = v___y_3034_;
v___y_2979_ = v___y_3036_;
v___y_2980_ = v___y_3037_;
v___y_2981_ = v___y_3038_;
v___y_2982_ = v___y_3039_;
v___y_2983_ = v___y_3040_;
v___y_2984_ = v___y_3042_;
v___y_2985_ = v___y_3041_;
v___y_2986_ = v___y_3043_;
goto v___jp_2972_;
}
}
v___jp_3046_:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_nat_dec_eq(v___y_3062_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_dec(v___y_3052_);
v___y_2991_ = v___y_3047_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3053_;
v___y_2997_ = v___y_3054_;
v___y_2998_ = v___y_3055_;
v___y_2999_ = v___y_3056_;
v___y_3000_ = v___y_3057_;
v___y_3001_ = v___y_3058_;
v___y_3002_ = v___y_3059_;
v___y_3003_ = v___y_3061_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3062_;
goto v___jp_2990_;
}
else
{
if (v___y_3056_ == 0)
{
v___y_3028_ = v___y_3047_;
v___y_3029_ = v___y_3048_;
v___y_3030_ = v___y_3049_;
v___y_3031_ = v___y_3050_;
v___y_3032_ = v___y_3051_;
v___y_3033_ = v___y_3052_;
v___y_3034_ = v___y_3053_;
v___y_3035_ = v___y_3054_;
v___y_3036_ = v___y_3055_;
v___y_3037_ = v___y_3056_;
v___y_3038_ = v___y_3057_;
v___y_3039_ = v___y_3058_;
v___y_3040_ = v___y_3059_;
v___y_3041_ = v___y_3060_;
v___y_3042_ = v___y_3061_;
v___y_3043_ = v___y_3062_;
goto v___jp_3027_;
}
else
{
if (v___y_3063_ == 0)
{
lean_dec(v___y_3052_);
v___y_2991_ = v___y_3047_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3053_;
v___y_2997_ = v___y_3054_;
v___y_2998_ = v___y_3055_;
v___y_2999_ = v___y_3056_;
v___y_3000_ = v___y_3057_;
v___y_3001_ = v___y_3058_;
v___y_3002_ = v___y_3059_;
v___y_3003_ = v___y_3061_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3062_;
goto v___jp_2990_;
}
else
{
v___y_3028_ = v___y_3047_;
v___y_3029_ = v___y_3048_;
v___y_3030_ = v___y_3049_;
v___y_3031_ = v___y_3050_;
v___y_3032_ = v___y_3051_;
v___y_3033_ = v___y_3052_;
v___y_3034_ = v___y_3053_;
v___y_3035_ = v___y_3054_;
v___y_3036_ = v___y_3055_;
v___y_3037_ = v___y_3056_;
v___y_3038_ = v___y_3057_;
v___y_3039_ = v___y_3058_;
v___y_3040_ = v___y_3059_;
v___y_3041_ = v___y_3060_;
v___y_3042_ = v___y_3061_;
v___y_3043_ = v___y_3062_;
goto v___jp_3027_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3172_, lean_object* v_c_x3f_3173_, lean_object* v_cs_x27_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3172_, v_c_x3f_3173_, v_cs_x27_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec(v_a_3175_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3187_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3234_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3234_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3234_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_unbox(v_a_3199_);
lean_dec(v_a_3199_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
lean_del_object(v___x_3201_);
v___x_3204_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3187_, v_a_3189_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3221_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3207_ = v___x_3204_;
v_isShared_3208_ = v_isSharedCheck_3221_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3221_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_unbox(v_a_3205_);
lean_dec(v_a_3205_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v_toGoalState_3211_; lean_object* v_split_3212_; lean_object* v_candidates_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_del_object(v___x_3207_);
v___x_3210_ = lean_st_ref_get(v_a_3187_);
v_toGoalState_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_ref(v_toGoalState_3211_);
lean_dec(v___x_3210_);
v_split_3212_ = lean_ctor_get(v_toGoalState_3211_, 14);
lean_inc_ref(v_split_3212_);
lean_dec_ref(v_toGoalState_3211_);
v_candidates_3213_ = lean_ctor_get(v_split_3212_, 1);
lean_inc(v_candidates_3213_);
lean_dec_ref(v_split_3212_);
v___x_3214_ = lean_box(0);
v___x_3215_ = lean_box(0);
v___x_3216_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3213_, v___x_3214_, v___x_3215_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_box(0);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3217_);
v___x_3219_ = v___x_3207_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
v_a_3222_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3204_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3204_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_box(0);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3230_);
v___x_3232_ = v___x_3201_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
v_a_3235_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3198_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3198_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec(v_a_3243_);
return v_res_3254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = lean_box(0);
v___x_3263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3264_ = l_Lean_mkConst(v___x_3263_, v___x_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3265_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3267_ = l_Lean_Expr_app___override(v___x_3266_, v_c_3265_);
return v___x_3267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3278_ = l_Lean_mkConst(v___x_3277_, v___x_3276_);
return v___x_3278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_box(0);
v___x_3285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3286_ = l_Lean_mkConst(v___x_3285_, v___x_3284_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_box(0);
v___x_3293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3294_ = l_Lean_mkConst(v___x_3293_, v___x_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___x_3354_; 
lean_inc_ref(v_c_3295_);
v___x_3354_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3295_, v_a_3303_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3440_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3440_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3440_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = l_Lean_Expr_cleanupAnnotations(v_a_3355_);
v___x_3373_ = l_Lean_Expr_isApp(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v___x_3372_);
lean_del_object(v___x_3357_);
v___y_3360_ = v_a_3296_;
v___y_3361_ = v_a_3297_;
v___y_3362_ = v_a_3298_;
v___y_3363_ = v_a_3299_;
v___y_3364_ = v_a_3300_;
v___y_3365_ = v_a_3301_;
v___y_3366_ = v_a_3302_;
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
goto v___jp_3359_;
}
else
{
lean_object* v_arg_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_arg_3374_ = lean_ctor_get(v___x_3372_, 1);
lean_inc_ref(v_arg_3374_);
v___x_3375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3372_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3377_ = l_Lean_Expr_isConstOf(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
uint8_t v___x_3378_; 
v___x_3378_ = l_Lean_Expr_isApp(v___x_3375_);
if (v___x_3378_ == 0)
{
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_arg_3374_);
lean_del_object(v___x_3357_);
v___y_3360_ = v_a_3296_;
v___y_3361_ = v_a_3297_;
v___y_3362_ = v_a_3298_;
v___y_3363_ = v_a_3299_;
v___y_3364_ = v_a_3300_;
v___y_3365_ = v_a_3301_;
v___y_3366_ = v_a_3302_;
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
goto v___jp_3359_;
}
else
{
lean_object* v_arg_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v_arg_3379_ = lean_ctor_get(v___x_3375_, 1);
lean_inc_ref(v_arg_3379_);
v___x_3380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3375_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3382_ = l_Lean_Expr_isConstOf(v___x_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Lean_Expr_isApp(v___x_3380_);
if (v___x_3383_ == 0)
{
lean_dec_ref(v___x_3380_);
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
lean_del_object(v___x_3357_);
v___y_3360_ = v_a_3296_;
v___y_3361_ = v_a_3297_;
v___y_3362_ = v_a_3298_;
v___y_3363_ = v_a_3299_;
v___y_3364_ = v_a_3300_;
v___y_3365_ = v_a_3301_;
v___y_3366_ = v_a_3302_;
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3380_);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3386_ = l_Lean_Expr_isConstOf(v___x_3384_, v___x_3385_);
lean_dec_ref(v___x_3384_);
if (v___x_3386_ == 0)
{
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
lean_del_object(v___x_3357_);
v___y_3360_ = v_a_3296_;
v___y_3361_ = v_a_3297_;
v___y_3362_ = v_a_3298_;
v___y_3363_ = v_a_3299_;
v___y_3364_ = v_a_3300_;
v___y_3365_ = v_a_3301_;
v___y_3366_ = v_a_3302_;
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
goto v___jp_3359_;
}
else
{
uint8_t v___x_3387_; 
lean_inc_ref(v_c_3295_);
v___x_3387_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3295_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
v___x_3388_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3295_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3388_);
v___x_3390_ = v___x_3357_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
else
{
lean_object* v___x_3392_; 
lean_del_object(v___x_3357_);
lean_inc_ref(v_c_3295_);
v___x_3392_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3295_, v_a_3296_, v_a_3300_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; uint8_t v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = lean_unbox(v_a_3393_);
lean_dec(v_a_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3405_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3401_ = l_Lean_mkApp3(v___x_3400_, v_arg_3379_, v_arg_3374_, v_a_3396_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3401_);
v___x_3403_ = v___x_3398_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
else
{
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3416_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3416_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3416_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3412_ = l_Lean_mkApp3(v___x_3411_, v_arg_3379_, v_arg_3374_, v_a_3407_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3412_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
else
{
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
return v___x_3406_;
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_c_3295_);
v_a_3417_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3392_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3392_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3425_; 
lean_dec_ref(v___x_3380_);
lean_del_object(v___x_3357_);
v___x_3425_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3435_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3431_ = l_Lean_mkApp3(v___x_3430_, v_arg_3379_, v_arg_3374_, v_a_3426_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3431_);
v___x_3433_ = v___x_3428_;
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
else
{
lean_dec_ref(v_arg_3379_);
lean_dec_ref(v_arg_3374_);
return v___x_3425_;
}
}
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_c_3295_);
v___x_3436_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3374_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3436_);
v___x_3438_ = v___x_3357_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
v___jp_3359_:
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Meta_Grind_isIte(v_c_3295_);
if (v___x_3370_ == 0)
{
uint8_t v___x_3371_; 
v___x_3371_ = l_Lean_Meta_Grind_isDIte(v_c_3295_);
v___y_3308_ = v___y_3368_;
v___y_3309_ = v___y_3366_;
v___y_3310_ = v___y_3369_;
v___y_3311_ = v___y_3364_;
v___y_3312_ = v___y_3363_;
v___y_3313_ = v___y_3367_;
v___y_3314_ = v___y_3365_;
v___y_3315_ = v___y_3361_;
v___y_3316_ = v___y_3360_;
v___y_3317_ = v___y_3362_;
v___y_3318_ = v___x_3371_;
goto v___jp_3307_;
}
else
{
v___y_3308_ = v___y_3368_;
v___y_3309_ = v___y_3366_;
v___y_3310_ = v___y_3369_;
v___y_3311_ = v___y_3364_;
v___y_3312_ = v___y_3363_;
v___y_3313_ = v___y_3367_;
v___y_3314_ = v___y_3365_;
v___y_3315_ = v___y_3361_;
v___y_3316_ = v___y_3360_;
v___y_3317_ = v___y_3362_;
v___y_3318_ = v___x_3370_;
goto v___jp_3307_;
}
}
}
}
else
{
lean_dec_ref(v_c_3295_);
return v___x_3354_;
}
v___jp_3307_:
{
if (v___y_3318_ == 0)
{
lean_object* v___x_3319_; 
lean_inc_ref(v_c_3295_);
v___x_3319_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3295_, v___y_3316_, v___y_3311_, v___y_3309_, v___y_3313_, v___y_3308_, v___y_3310_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3338_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3338_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3338_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_unbox(v_a_3320_);
lean_dec(v_a_3320_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3326_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_c_3295_);
v___x_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_c_3295_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
else
{
lean_object* v___x_3328_; 
lean_del_object(v___x_3322_);
lean_inc_ref(v_c_3295_);
v___x_3328_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3295_, v___y_3316_, v___y_3315_, v___y_3317_, v___y_3312_, v___y_3311_, v___y_3314_, v___y_3309_, v___y_3313_, v___y_3308_, v___y_3310_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3295_, v_a_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
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
lean_dec_ref(v_c_3295_);
return v___x_3328_;
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v_c_3295_);
v_a_3339_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3319_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3319_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3347_ = lean_unsigned_to_nat(1u);
v___x_3348_ = l_Lean_Expr_getAppNumArgs(v_c_3295_);
v___x_3349_ = lean_nat_sub(v___x_3348_, v___x_3347_);
lean_dec(v___x_3348_);
v___x_3350_ = lean_nat_sub(v___x_3349_, v___x_3347_);
lean_dec(v___x_3349_);
v___x_3351_ = l_Lean_Expr_getRevArg_x21(v_c_3295_, v___x_3350_);
lean_dec_ref(v_c_3295_);
v___x_3352_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3351_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec(v_a_3442_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3454_, lean_object* v_major_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3456_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; uint8_t v_trace_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v_trace_3465_ = lean_ctor_get_uint8(v_a_3464_, sizeof(void*)*14);
lean_dec(v_a_3464_);
if (v_trace_3465_ == 0)
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Meta_Grind_cases(v_mvarId_3454_, v_major_3455_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; 
lean_inc(v_a_3461_);
lean_inc_ref(v_a_3460_);
lean_inc(v_a_3459_);
lean_inc_ref(v_a_3458_);
lean_inc_ref(v_major_3455_);
v___x_3467_ = lean_infer_type(v_major_3455_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_Meta_whnfD(v_a_3468_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = l_Lean_Expr_getAppFn(v_a_3470_);
lean_dec(v_a_3470_);
if (lean_obj_tag(v___x_3471_) == 4)
{
lean_object* v_declName_3472_; lean_object* v___x_3473_; 
v_declName_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_declName_3472_);
lean_dec_ref_known(v___x_3471_, 2);
v___x_3473_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3472_, v_a_3457_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = l_Lean_Meta_Grind_cases(v_mvarId_3454_, v_major_3455_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3474_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v_major_3455_);
lean_dec(v_mvarId_3454_);
v_a_3475_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v___x_3483_; 
lean_dec_ref(v___x_3471_);
v___x_3483_ = l_Lean_Meta_Grind_cases(v_mvarId_3454_, v_major_3455_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3483_;
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v_major_3455_);
lean_dec(v_mvarId_3454_);
v_a_3484_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3469_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3469_);
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
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec_ref(v_major_3455_);
lean_dec(v_mvarId_3454_);
v_a_3492_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3467_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3467_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v_major_3455_);
lean_dec(v_mvarId_3454_);
v_a_3500_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3463_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3463_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3508_, lean_object* v_major_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3508_, v_major_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3518_, lean_object* v_major_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3518_, v_major_3519_, v_a_3522_, v_a_3523_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3532_, lean_object* v_major_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3532_, v_major_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec(v_a_3534_);
return v_res_3545_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3546_){
_start:
{
uint64_t v_anchor_3547_; 
v_anchor_3547_ = lean_ctor_get_uint64(v_e_3546_, sizeof(void*)*3);
return v_anchor_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3548_){
_start:
{
uint64_t v_res_3549_; lean_object* v_r_3550_; 
v_res_3549_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3548_);
lean_dec_ref(v_e_3548_);
v_r_3550_ = lean_box_uint64(v_res_3549_);
return v_r_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3553_, lean_object* v_x_3554_){
_start:
{
if (lean_obj_tag(v_x_3554_) == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_box(0);
return v___x_3555_;
}
else
{
lean_object* v_key_3556_; lean_object* v_value_3557_; lean_object* v_tail_3558_; uint64_t v___x_3559_; uint8_t v___x_3560_; 
v_key_3556_ = lean_ctor_get(v_x_3554_, 0);
v_value_3557_ = lean_ctor_get(v_x_3554_, 1);
v_tail_3558_ = lean_ctor_get(v_x_3554_, 2);
v___x_3559_ = lean_unbox_uint64(v_key_3556_);
v___x_3560_ = lean_uint64_dec_eq(v___x_3559_, v_a_3553_);
if (v___x_3560_ == 0)
{
v_x_3554_ = v_tail_3558_;
goto _start;
}
else
{
lean_object* v___x_3562_; 
lean_inc(v_value_3557_);
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_value_3557_);
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3563_, lean_object* v_x_3564_){
_start:
{
uint64_t v_a_boxed_3565_; lean_object* v_res_3566_; 
v_a_boxed_3565_ = lean_unbox_uint64(v_a_3563_);
lean_dec_ref(v_a_3563_);
v_res_3566_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3565_, v_x_3564_);
lean_dec(v_x_3564_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3567_, uint64_t v_a_3568_){
_start:
{
lean_object* v_buckets_3569_; lean_object* v___x_3570_; uint64_t v___x_3571_; uint64_t v___x_3572_; uint64_t v_fold_3573_; uint64_t v___x_3574_; uint64_t v___x_3575_; uint64_t v___x_3576_; size_t v___x_3577_; size_t v___x_3578_; size_t v___x_3579_; size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_buckets_3569_ = lean_ctor_get(v_m_3567_, 1);
v___x_3570_ = lean_array_get_size(v_buckets_3569_);
v___x_3571_ = 32ULL;
v___x_3572_ = lean_uint64_shift_right(v_a_3568_, v___x_3571_);
v_fold_3573_ = lean_uint64_xor(v_a_3568_, v___x_3572_);
v___x_3574_ = 16ULL;
v___x_3575_ = lean_uint64_shift_right(v_fold_3573_, v___x_3574_);
v___x_3576_ = lean_uint64_xor(v_fold_3573_, v___x_3575_);
v___x_3577_ = lean_uint64_to_usize(v___x_3576_);
v___x_3578_ = lean_usize_of_nat(v___x_3570_);
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_sub(v___x_3578_, v___x_3579_);
v___x_3581_ = lean_usize_land(v___x_3577_, v___x_3580_);
v___x_3582_ = lean_array_uget_borrowed(v_buckets_3569_, v___x_3581_);
v___x_3583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3568_, v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3584_, lean_object* v_a_3585_){
_start:
{
uint64_t v_a_boxed_3586_; lean_object* v_res_3587_; 
v_a_boxed_3586_ = lean_unbox_uint64(v_a_3585_);
lean_dec_ref(v_a_3585_);
v_res_3587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3584_, v_a_boxed_3586_);
lean_dec_ref(v_m_3584_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3589_) == 0)
{
return v_x_3588_;
}
else
{
lean_object* v_key_3590_; lean_object* v_value_3591_; lean_object* v_tail_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3616_; 
v_key_3590_ = lean_ctor_get(v_x_3589_, 0);
v_value_3591_ = lean_ctor_get(v_x_3589_, 1);
v_tail_3592_ = lean_ctor_get(v_x_3589_, 2);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_x_3589_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3594_ = v_x_3589_;
v_isShared_3595_ = v_isSharedCheck_3616_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_tail_3592_);
lean_inc(v_value_3591_);
lean_inc(v_key_3590_);
lean_dec(v_x_3589_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3616_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; uint64_t v___x_3597_; uint64_t v___x_3598_; uint64_t v___x_3599_; uint64_t v___x_3600_; uint64_t v_fold_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3596_ = lean_array_get_size(v_x_3588_);
v___x_3597_ = 32ULL;
v___x_3598_ = lean_unbox_uint64(v_key_3590_);
v___x_3599_ = lean_uint64_shift_right(v___x_3598_, v___x_3597_);
v___x_3600_ = lean_unbox_uint64(v_key_3590_);
v_fold_3601_ = lean_uint64_xor(v___x_3600_, v___x_3599_);
v___x_3602_ = 16ULL;
v___x_3603_ = lean_uint64_shift_right(v_fold_3601_, v___x_3602_);
v___x_3604_ = lean_uint64_xor(v_fold_3601_, v___x_3603_);
v___x_3605_ = lean_uint64_to_usize(v___x_3604_);
v___x_3606_ = lean_usize_of_nat(v___x_3596_);
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_sub(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_usize_land(v___x_3605_, v___x_3608_);
v___x_3610_ = lean_array_uget_borrowed(v_x_3588_, v___x_3609_);
lean_inc(v___x_3610_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 2, v___x_3610_);
v___x_3612_ = v___x_3594_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_key_3590_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_value_3591_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; 
v___x_3613_ = lean_array_uset(v_x_3588_, v___x_3609_, v___x_3612_);
v_x_3588_ = v___x_3613_;
v_x_3589_ = v_tail_3592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3617_, lean_object* v_source_3618_, lean_object* v_target_3619_){
_start:
{
lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3620_ = lean_array_get_size(v_source_3618_);
v___x_3621_ = lean_nat_dec_lt(v_i_3617_, v___x_3620_);
if (v___x_3621_ == 0)
{
lean_dec_ref(v_source_3618_);
lean_dec(v_i_3617_);
return v_target_3619_;
}
else
{
lean_object* v_es_3622_; lean_object* v___x_3623_; lean_object* v_source_3624_; lean_object* v_target_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_es_3622_ = lean_array_fget(v_source_3618_, v_i_3617_);
v___x_3623_ = lean_box(0);
v_source_3624_ = lean_array_fset(v_source_3618_, v_i_3617_, v___x_3623_);
v_target_3625_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3619_, v_es_3622_);
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = lean_nat_add(v_i_3617_, v___x_3626_);
lean_dec(v_i_3617_);
v_i_3617_ = v___x_3627_;
v_source_3618_ = v_source_3624_;
v_target_3619_ = v_target_3625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_nbuckets_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3630_ = lean_array_get_size(v_data_3629_);
v___x_3631_ = lean_unsigned_to_nat(2u);
v_nbuckets_3632_ = lean_nat_mul(v___x_3630_, v___x_3631_);
v___x_3633_ = lean_unsigned_to_nat(0u);
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_mk_array(v_nbuckets_3632_, v___x_3634_);
v___x_3636_ = lean_array_propagate_mark(v_data_3629_, v___x_3635_);
v___x_3637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3633_, v_data_3629_, v___x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3638_, lean_object* v_b_3639_, lean_object* v_x_3640_){
_start:
{
if (lean_obj_tag(v_x_3640_) == 0)
{
lean_dec(v_b_3639_);
return v_x_3640_;
}
else
{
lean_object* v_key_3641_; lean_object* v_value_3642_; lean_object* v_tail_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3657_; 
v_key_3641_ = lean_ctor_get(v_x_3640_, 0);
v_value_3642_ = lean_ctor_get(v_x_3640_, 1);
v_tail_3643_ = lean_ctor_get(v_x_3640_, 2);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_x_3640_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3645_ = v_x_3640_;
v_isShared_3646_ = v_isSharedCheck_3657_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_tail_3643_);
lean_inc(v_value_3642_);
lean_inc(v_key_3641_);
lean_dec(v_x_3640_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3657_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
uint64_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_unbox_uint64(v_key_3641_);
v___x_3648_ = lean_uint64_dec_eq(v___x_3647_, v_a_3638_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3638_, v_b_3639_, v_tail_3643_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 2, v___x_3649_);
v___x_3651_ = v___x_3645_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_key_3641_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_value_3642_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
lean_dec(v_value_3642_);
lean_dec(v_key_3641_);
v___x_3653_ = lean_box_uint64(v_a_3638_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 1, v_b_3639_);
lean_ctor_set(v___x_3645_, 0, v___x_3653_);
v___x_3655_ = v___x_3645_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_b_3639_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_tail_3643_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3658_, lean_object* v_b_3659_, lean_object* v_x_3660_){
_start:
{
uint64_t v_a_boxed_3661_; lean_object* v_res_3662_; 
v_a_boxed_3661_ = lean_unbox_uint64(v_a_3658_);
lean_dec_ref(v_a_3658_);
v_res_3662_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3661_, v_b_3659_, v_x_3660_);
return v_res_3662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3663_, lean_object* v_x_3664_){
_start:
{
if (lean_obj_tag(v_x_3664_) == 0)
{
uint8_t v___x_3665_; 
v___x_3665_ = 0;
return v___x_3665_;
}
else
{
lean_object* v_key_3666_; lean_object* v_tail_3667_; uint64_t v___x_3668_; uint8_t v___x_3669_; 
v_key_3666_ = lean_ctor_get(v_x_3664_, 0);
v_tail_3667_ = lean_ctor_get(v_x_3664_, 2);
v___x_3668_ = lean_unbox_uint64(v_key_3666_);
v___x_3669_ = lean_uint64_dec_eq(v___x_3668_, v_a_3663_);
if (v___x_3669_ == 0)
{
v_x_3664_ = v_tail_3667_;
goto _start;
}
else
{
return v___x_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3671_, lean_object* v_x_3672_){
_start:
{
uint64_t v_a_boxed_3673_; uint8_t v_res_3674_; lean_object* v_r_3675_; 
v_a_boxed_3673_ = lean_unbox_uint64(v_a_3671_);
lean_dec_ref(v_a_3671_);
v_res_3674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3673_, v_x_3672_);
lean_dec(v_x_3672_);
v_r_3675_ = lean_box(v_res_3674_);
return v_r_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3676_, uint64_t v_a_3677_, lean_object* v_b_3678_){
_start:
{
lean_object* v_size_3679_; lean_object* v_buckets_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3723_; 
v_size_3679_ = lean_ctor_get(v_m_3676_, 0);
v_buckets_3680_ = lean_ctor_get(v_m_3676_, 1);
v_isSharedCheck_3723_ = !lean_is_exclusive(v_m_3676_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3682_ = v_m_3676_;
v_isShared_3683_ = v_isSharedCheck_3723_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_buckets_3680_);
lean_inc(v_size_3679_);
lean_dec(v_m_3676_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3723_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; uint64_t v___x_3685_; uint64_t v___x_3686_; uint64_t v_fold_3687_; uint64_t v___x_3688_; uint64_t v___x_3689_; uint64_t v___x_3690_; size_t v___x_3691_; size_t v___x_3692_; size_t v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; lean_object* v_bkt_3696_; uint8_t v___x_3697_; 
v___x_3684_ = lean_array_get_size(v_buckets_3680_);
v___x_3685_ = 32ULL;
v___x_3686_ = lean_uint64_shift_right(v_a_3677_, v___x_3685_);
v_fold_3687_ = lean_uint64_xor(v_a_3677_, v___x_3686_);
v___x_3688_ = 16ULL;
v___x_3689_ = lean_uint64_shift_right(v_fold_3687_, v___x_3688_);
v___x_3690_ = lean_uint64_xor(v_fold_3687_, v___x_3689_);
v___x_3691_ = lean_uint64_to_usize(v___x_3690_);
v___x_3692_ = lean_usize_of_nat(v___x_3684_);
v___x_3693_ = ((size_t)1ULL);
v___x_3694_ = lean_usize_sub(v___x_3692_, v___x_3693_);
v___x_3695_ = lean_usize_land(v___x_3691_, v___x_3694_);
v_bkt_3696_ = lean_array_uget_borrowed(v_buckets_3680_, v___x_3695_);
v___x_3697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3677_, v_bkt_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v_size_x27_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v_buckets_x27_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3698_ = lean_unsigned_to_nat(1u);
v_size_x27_3699_ = lean_nat_add(v_size_3679_, v___x_3698_);
lean_dec(v_size_3679_);
v___x_3700_ = lean_box_uint64(v_a_3677_);
lean_inc(v_bkt_3696_);
v___x_3701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
lean_ctor_set(v___x_3701_, 1, v_b_3678_);
lean_ctor_set(v___x_3701_, 2, v_bkt_3696_);
v_buckets_x27_3702_ = lean_array_uset(v_buckets_3680_, v___x_3695_, v___x_3701_);
v___x_3703_ = lean_unsigned_to_nat(4u);
v___x_3704_ = lean_nat_mul(v_size_x27_3699_, v___x_3703_);
v___x_3705_ = lean_unsigned_to_nat(3u);
v___x_3706_ = lean_nat_div(v___x_3704_, v___x_3705_);
lean_dec(v___x_3704_);
v___x_3707_ = lean_array_get_size(v_buckets_x27_3702_);
v___x_3708_ = lean_nat_dec_le(v___x_3706_, v___x_3707_);
lean_dec(v___x_3706_);
if (v___x_3708_ == 0)
{
lean_object* v_val_3709_; lean_object* v___x_3711_; 
v_val_3709_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3702_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 1, v_val_3709_);
lean_ctor_set(v___x_3682_, 0, v_size_x27_3699_);
v___x_3711_ = v___x_3682_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_size_x27_3699_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_val_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
else
{
lean_object* v___x_3714_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 1, v_buckets_x27_3702_);
lean_ctor_set(v___x_3682_, 0, v_size_x27_3699_);
v___x_3714_ = v___x_3682_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_size_x27_3699_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_buckets_x27_3702_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
else
{
lean_object* v___x_3716_; lean_object* v_buckets_x27_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_inc(v_bkt_3696_);
v___x_3716_ = lean_box(0);
v_buckets_x27_3717_ = lean_array_uset(v_buckets_3680_, v___x_3695_, v___x_3716_);
v___x_3718_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3677_, v_b_3678_, v_bkt_3696_);
v___x_3719_ = lean_array_uset(v_buckets_x27_3717_, v___x_3695_, v___x_3718_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 1, v___x_3719_);
v___x_3721_ = v___x_3682_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_size_3679_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3724_, lean_object* v_a_3725_, lean_object* v_b_3726_){
_start:
{
uint64_t v_a_boxed_3727_; lean_object* v_res_3728_; 
v_a_boxed_3727_ = lean_unbox_uint64(v_a_3725_);
lean_dec_ref(v_a_3725_);
v_res_3728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3724_, v_a_boxed_3727_, v_b_3726_);
return v_res_3728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_unsigned_to_nat(16u);
v___x_3731_ = lean_mk_array(v___x_3730_, v___x_3729_);
return v___x_3731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v_found_3734_; 
v___x_3732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3733_ = lean_unsigned_to_nat(0u);
v_found_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3734_, 0, v___x_3733_);
lean_ctor_set(v_found_3734_, 1, v___x_3732_);
return v_found_3734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_found_3735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v_found_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3738_, lean_object* v_numDigits_3739_, lean_object* v_es_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_){
_start:
{
lean_object* v_a_3746_; uint8_t v___x_3750_; 
v___x_3750_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3750_ == 0)
{
return v_b_3744_;
}
else
{
lean_object* v_snd_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3785_; 
v_snd_3751_ = lean_ctor_get(v_b_3744_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_b_3744_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; 
v_unused_3786_ = lean_ctor_get(v_b_3744_, 0);
lean_dec(v_unused_3786_);
v___x_3753_ = v_b_3744_;
v_isShared_3754_ = v_isSharedCheck_3785_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_snd_3751_);
lean_dec(v_b_3744_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3785_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_a_3755_; uint64_t v_anchor_3756_; lean_object* v___x_3757_; uint64_t v___x_3758_; uint64_t v___x_3759_; lean_object* v___x_3760_; 
v_a_3755_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
v_anchor_3756_ = lean_ctor_get_uint64(v_a_3755_, sizeof(void*)*3);
v___x_3757_ = lean_box(0);
v___x_3758_ = lean_uint64_of_nat(v_shift_3738_);
v___x_3759_ = lean_uint64_shift_right(v_anchor_3756_, v___x_3758_);
v___x_3760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3751_, v___x_3759_);
if (lean_obj_tag(v___x_3760_) == 1)
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3779_; 
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint64_t v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = lean_unbox_uint64(v_val_3761_);
lean_dec(v_val_3761_);
v___x_3766_ = lean_uint64_dec_eq(v___x_3765_, v_anchor_3756_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3767_ = lean_unsigned_to_nat(1u);
v___x_3768_ = lean_nat_add(v_numDigits_3739_, v___x_3767_);
v___x_3769_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3740_, v___x_3768_);
lean_dec(v___x_3768_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3769_);
v___x_3771_ = v___x_3763_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3771_);
v___x_3773_ = v___x_3753_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_snd_3751_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
lean_object* v___x_3777_; 
lean_del_object(v___x_3763_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3757_);
v___x_3777_ = v___x_3753_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_snd_3751_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
v_a_3746_ = v___x_3777_;
goto v___jp_3745_;
}
}
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
lean_dec(v___x_3760_);
v___x_3780_ = lean_box_uint64(v_anchor_3756_);
v___x_3781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3751_, v___x_3759_, v___x_3780_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 1, v___x_3781_);
lean_ctor_set(v___x_3753_, 0, v___x_3757_);
v___x_3783_ = v___x_3753_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v_a_3746_ = v___x_3783_;
goto v___jp_3745_;
}
}
}
}
v___jp_3745_:
{
size_t v___x_3747_; size_t v___x_3748_; 
v___x_3747_ = ((size_t)1ULL);
v___x_3748_ = lean_usize_add(v_i_3743_, v___x_3747_);
v_i_3743_ = v___x_3748_;
v_b_3744_ = v_a_3746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3787_, lean_object* v_numDigits_3788_){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3789_ = lean_unsigned_to_nat(4u);
v___x_3790_ = lean_nat_mul(v___x_3789_, v_numDigits_3788_);
v___x_3791_ = lean_unsigned_to_nat(64u);
v___x_3792_ = lean_nat_dec_lt(v___x_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_dec(v___x_3790_);
lean_inc(v_numDigits_3788_);
return v_numDigits_3788_;
}
else
{
lean_object* v_shift_3793_; lean_object* v___x_3794_; size_t v_sz_3795_; size_t v___x_3796_; lean_object* v___x_3797_; lean_object* v_fst_3798_; 
v_shift_3793_ = lean_nat_sub(v___x_3791_, v___x_3790_);
lean_dec(v___x_3790_);
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3795_ = lean_array_size(v_es_3787_);
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3793_, v_numDigits_3788_, v_es_3787_, v_es_3787_, v_sz_3795_, v___x_3796_, v___x_3794_);
lean_dec(v_shift_3793_);
v_fst_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_fst_3798_);
lean_dec_ref(v___x_3797_);
if (lean_obj_tag(v_fst_3798_) == 0)
{
lean_inc(v_numDigits_3788_);
return v_numDigits_3788_;
}
else
{
lean_object* v_val_3799_; 
v_val_3799_ = lean_ctor_get(v_fst_3798_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v_fst_3798_, 1);
return v_val_3799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3800_, lean_object* v_numDigits_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3800_, v_numDigits_3801_);
lean_dec(v_numDigits_3801_);
lean_dec_ref(v_es_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3803_, lean_object* v_numDigits_3804_, lean_object* v_es_3805_, lean_object* v_as_3806_, lean_object* v_sz_3807_, lean_object* v_i_3808_, lean_object* v_b_3809_){
_start:
{
size_t v_sz_boxed_3810_; size_t v_i_boxed_3811_; lean_object* v_res_3812_; 
v_sz_boxed_3810_ = lean_unbox_usize(v_sz_3807_);
lean_dec(v_sz_3807_);
v_i_boxed_3811_ = lean_unbox_usize(v_i_3808_);
lean_dec(v_i_3808_);
v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3803_, v_numDigits_3804_, v_es_3805_, v_as_3806_, v_sz_boxed_3810_, v_i_boxed_3811_, v_b_3809_);
lean_dec_ref(v_as_3806_);
lean_dec_ref(v_es_3805_);
lean_dec(v_numDigits_3804_);
lean_dec(v_shift_3803_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3813_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_unsigned_to_nat(4u);
v___x_3815_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3813_, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3816_);
lean_dec_ref(v_es_3816_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3818_, lean_object* v_as_3819_, size_t v_i_3820_, size_t v_stop_3821_, lean_object* v_b_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_a_3835_; uint8_t v___x_3839_; 
v___x_3839_ = lean_usize_dec_eq(v_i_3820_, v_stop_3821_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_array_uget_borrowed(v_as_3819_, v_i_3820_);
v___x_3841_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3840_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v_e_3843_; lean_object* v___x_3844_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v_e_3843_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3840_);
lean_inc(v___x_3840_);
v___x_3844_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3840_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
if (lean_obj_tag(v_a_3845_) == 2)
{
lean_object* v_numCases_3846_; uint8_t v_isRec_3847_; lean_object* v___x_3848_; 
v_numCases_3846_ = lean_ctor_get(v_a_3845_, 0);
lean_inc(v_numCases_3846_);
v_isRec_3847_ = lean_ctor_get_uint8(v_a_3845_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3845_, 1);
lean_inc_ref(v_filter_3818_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3827_);
lean_inc(v___y_3826_);
lean_inc_ref(v___y_3825_);
lean_inc(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v_e_3843_);
v___x_3848_ = lean_apply_12(v_filter_3818_, v_e_3843_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, lean_box(0));
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; uint8_t v___x_3850_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3850_ = lean_unbox(v_a_3849_);
lean_dec(v_a_3849_);
if (v___x_3850_ == 0)
{
lean_dec(v_numCases_3846_);
lean_dec_ref(v_e_3843_);
lean_dec(v_a_3842_);
v_a_3835_ = v_b_3822_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3851_; uint64_t v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v___x_3840_);
v___x_3851_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3851_, 0, v___x_3840_);
lean_ctor_set(v___x_3851_, 1, v_numCases_3846_);
lean_ctor_set(v___x_3851_, 2, v_e_3843_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*3 + 8, v_isRec_3847_);
v___x_3852_ = lean_unbox_uint64(v_a_3842_);
lean_dec(v_a_3842_);
lean_ctor_set_uint64(v___x_3851_, sizeof(void*)*3, v___x_3852_);
v___x_3853_ = lean_array_push(v_b_3822_, v___x_3851_);
v_a_3835_ = v___x_3853_;
goto v___jp_3834_;
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_numCases_3846_);
lean_dec_ref(v_e_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_b_3822_);
lean_dec_ref(v_filter_3818_);
v_a_3854_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3848_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3848_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_dec(v_a_3845_);
lean_dec_ref(v_e_3843_);
lean_dec(v_a_3842_);
v_a_3835_ = v_b_3822_;
goto v___jp_3834_;
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_e_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_b_3822_);
lean_dec_ref(v_filter_3818_);
v_a_3862_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3844_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3844_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec_ref(v_b_3822_);
lean_dec_ref(v_filter_3818_);
v_a_3870_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3841_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3841_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v___x_3878_; 
lean_dec_ref(v_filter_3818_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_b_3822_);
return v___x_3878_;
}
v___jp_3834_:
{
size_t v___x_3836_; size_t v___x_3837_; 
v___x_3836_ = ((size_t)1ULL);
v___x_3837_ = lean_usize_add(v_i_3820_, v___x_3836_);
v_i_3820_ = v___x_3837_;
v_b_3822_ = v_a_3835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3879_, lean_object* v_as_3880_, lean_object* v_i_3881_, lean_object* v_stop_3882_, lean_object* v_b_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
size_t v_i_boxed_3895_; size_t v_stop_boxed_3896_; lean_object* v_res_3897_; 
v_i_boxed_3895_ = lean_unbox_usize(v_i_3881_);
lean_dec(v_i_3881_);
v_stop_boxed_3896_ = lean_unbox_usize(v_stop_3882_);
lean_dec(v_stop_3882_);
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3879_, v_as_3880_, v_i_boxed_3895_, v_stop_boxed_3896_, v_b_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v_as_3880_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3900_, lean_object* v_as_3901_, lean_object* v_start_3902_, lean_object* v_stop_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3916_ = lean_nat_dec_lt(v_start_3902_, v_stop_3903_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; 
lean_dec_ref(v_filter_3900_);
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; uint8_t v___x_3919_; 
v___x_3918_ = lean_array_get_size(v_as_3901_);
v___x_3919_ = lean_nat_dec_le(v_stop_3903_, v___x_3918_);
if (v___x_3919_ == 0)
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_lt(v_start_3902_, v___x_3918_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
lean_dec_ref(v_filter_3900_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3915_);
return v___x_3921_;
}
else
{
size_t v___x_3922_; size_t v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_usize_of_nat(v_start_3902_);
v___x_3923_ = lean_usize_of_nat(v___x_3918_);
v___x_3924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3900_, v_as_3901_, v___x_3922_, v___x_3923_, v___x_3915_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
return v___x_3924_;
}
}
else
{
size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_usize_of_nat(v_start_3902_);
v___x_3926_ = lean_usize_of_nat(v_stop_3903_);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3900_, v_as_3901_, v___x_3925_, v___x_3926_, v___x_3915_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
return v___x_3927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3928_, lean_object* v_as_3929_, lean_object* v_start_3930_, lean_object* v_stop_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3928_, v_as_3929_, v_start_3930_, v_stop_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v_stop_3931_);
lean_dec(v_start_3930_);
lean_dec_ref(v_as_3929_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3944_, lean_object* v_candidates_x3f_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v_candidates_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; 
if (lean_obj_tag(v_candidates_x3f_3945_) == 0)
{
lean_object* v___x_3991_; lean_object* v_toGoalState_3992_; lean_object* v_split_3993_; lean_object* v_candidates_3994_; 
v___x_3991_ = lean_st_ref_get(v_a_3946_);
v_toGoalState_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_ref(v_toGoalState_3992_);
lean_dec(v___x_3991_);
v_split_3993_ = lean_ctor_get(v_toGoalState_3992_, 14);
lean_inc_ref(v_split_3993_);
lean_dec_ref(v_toGoalState_3992_);
v_candidates_3994_ = lean_ctor_get(v_split_3993_, 1);
lean_inc(v_candidates_3994_);
lean_dec_ref(v_split_3993_);
v_candidates_3958_ = v_candidates_3994_;
v___y_3959_ = v_a_3946_;
v___y_3960_ = v_a_3947_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
goto v___jp_3957_;
}
else
{
lean_object* v_val_3995_; 
v_val_3995_ = lean_ctor_get(v_candidates_x3f_3945_, 0);
lean_inc(v_val_3995_);
lean_dec_ref_known(v_candidates_x3f_3945_, 1);
v_candidates_3958_ = v_val_3995_;
v___y_3959_ = v_a_3946_;
v___y_3960_ = v_a_3947_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
goto v___jp_3957_;
}
v___jp_3957_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3969_ = lean_array_mk(v_candidates_3958_);
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = lean_array_get_size(v___x_3969_);
v___x_3972_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3944_, v___x_3969_, v___x_3970_, v___x_3971_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec_ref(v___x_3969_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3982_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3982_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3977_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3973_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_a_3973_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_3978_);
v___x_3980_ = v___x_3975_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
v_a_3983_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3972_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3972_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_3996_, lean_object* v_candidates_x3f_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_3996_, v_candidates_x3f_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec(v_a_3998_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4010_, lean_object* v_m_4011_, uint64_t v_a_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4011_, v_a_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4014_, lean_object* v_m_4015_, lean_object* v_a_4016_){
_start:
{
uint64_t v_a_boxed_4017_; lean_object* v_res_4018_; 
v_a_boxed_4017_ = lean_unbox_uint64(v_a_4016_);
lean_dec_ref(v_a_4016_);
v_res_4018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4014_, v_m_4015_, v_a_boxed_4017_);
lean_dec_ref(v_m_4015_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4019_, lean_object* v_m_4020_, uint64_t v_a_4021_, lean_object* v_b_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4020_, v_a_4021_, v_b_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4024_, lean_object* v_m_4025_, lean_object* v_a_4026_, lean_object* v_b_4027_){
_start:
{
uint64_t v_a_boxed_4028_; lean_object* v_res_4029_; 
v_a_boxed_4028_ = lean_unbox_uint64(v_a_4026_);
lean_dec_ref(v_a_4026_);
v_res_4029_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4024_, v_m_4025_, v_a_boxed_4028_, v_b_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4030_, uint64_t v_a_4031_, lean_object* v_x_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4031_, v_x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_x_4036_){
_start:
{
uint64_t v_a_boxed_4037_; lean_object* v_res_4038_; 
v_a_boxed_4037_ = lean_unbox_uint64(v_a_4035_);
lean_dec_ref(v_a_4035_);
v_res_4038_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4034_, v_a_boxed_4037_, v_x_4036_);
lean_dec(v_x_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4039_, uint64_t v_a_4040_, lean_object* v_x_4041_){
_start:
{
uint8_t v___x_4042_; 
v___x_4042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4040_, v_x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4043_, lean_object* v_a_4044_, lean_object* v_x_4045_){
_start:
{
uint64_t v_a_boxed_4046_; uint8_t v_res_4047_; lean_object* v_r_4048_; 
v_a_boxed_4046_ = lean_unbox_uint64(v_a_4044_);
lean_dec_ref(v_a_4044_);
v_res_4047_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4043_, v_a_boxed_4046_, v_x_4045_);
lean_dec(v_x_4045_);
v_r_4048_ = lean_box(v_res_4047_);
return v_r_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4049_, lean_object* v_data_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4052_, uint64_t v_a_4053_, lean_object* v_b_4054_, lean_object* v_x_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4053_, v_b_4054_, v_x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_a_4058_, lean_object* v_b_4059_, lean_object* v_x_4060_){
_start:
{
uint64_t v_a_boxed_4061_; lean_object* v_res_4062_; 
v_a_boxed_4061_ = lean_unbox_uint64(v_a_4058_);
lean_dec_ref(v_a_4058_);
v_res_4062_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4057_, v_a_boxed_4061_, v_b_4059_, v_x_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4063_, lean_object* v_i_4064_, lean_object* v_source_4065_, lean_object* v_target_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4064_, v_source_4065_, v_target_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4068_, lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4069_, v_x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = 1;
v___x_4085_ = lean_box(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v_x_4087_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4100_, uint64_t v_a_4101_, lean_object* v_c_4102_, lean_object* v_numDigits_4103_, lean_object* v_as_4104_, size_t v_sz_4105_, size_t v_i_4106_, lean_object* v_b_4107_){
_start:
{
lean_object* v_a_4110_; uint8_t v___x_4114_; 
v___x_4114_ = lean_usize_dec_lt(v_i_4106_, v_sz_4105_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; 
lean_dec(v_numDigits_4103_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_b_4107_);
return v___x_4115_;
}
else
{
lean_object* v_snd_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4142_; 
v_snd_4116_ = lean_ctor_get(v_b_4107_, 1);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_b_4107_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; 
v_unused_4143_ = lean_ctor_get(v_b_4107_, 0);
lean_dec(v_unused_4143_);
v___x_4118_ = v_b_4107_;
v_isShared_4119_ = v_isSharedCheck_4142_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_snd_4116_);
lean_dec(v_b_4107_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4142_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v_a_4120_; lean_object* v_c_4121_; uint64_t v_anchor_4122_; lean_object* v___x_4123_; uint64_t v___x_4124_; uint64_t v___x_4125_; uint8_t v___x_4126_; 
v_a_4120_ = lean_array_uget_borrowed(v_as_4104_, v_i_4106_);
v_c_4121_ = lean_ctor_get(v_a_4120_, 0);
v_anchor_4122_ = lean_ctor_get_uint64(v_a_4120_, sizeof(void*)*3);
v___x_4123_ = lean_box(0);
v___x_4124_ = lean_uint64_shift_right(v_anchor_4122_, v___x_4100_);
v___x_4125_ = lean_uint64_shift_right(v_a_4101_, v___x_4100_);
v___x_4126_ = lean_uint64_dec_eq(v___x_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4128_; 
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4123_);
v___x_4128_ = v___x_4118_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_snd_4116_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
v_a_4110_ = v___x_4128_;
goto v___jp_4109_;
}
}
else
{
uint8_t v___x_4130_; 
v___x_4130_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4121_, v_c_4102_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4131_ = lean_unsigned_to_nat(1u);
v___x_4132_ = lean_nat_add(v_snd_4116_, v___x_4131_);
lean_dec(v_snd_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 1, v___x_4132_);
lean_ctor_set(v___x_4118_, 0, v___x_4123_);
v___x_4134_ = v___x_4118_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v_a_4110_ = v___x_4134_;
goto v___jp_4109_;
}
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
lean_inc(v_snd_4116_);
v___x_4136_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4136_, 0, v_numDigits_4103_);
lean_ctor_set(v___x_4136_, 1, v_snd_4116_);
lean_ctor_set_uint64(v___x_4136_, sizeof(void*)*2, v_a_4101_);
v___x_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4137_);
v___x_4139_ = v___x_4118_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v_snd_4116_);
v___x_4139_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
return v___x_4140_;
}
}
}
}
}
v___jp_4109_:
{
size_t v___x_4111_; size_t v___x_4112_; 
v___x_4111_ = ((size_t)1ULL);
v___x_4112_ = lean_usize_add(v_i_4106_, v___x_4111_);
v_i_4106_ = v___x_4112_;
v_b_4107_ = v_a_4110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4144_, lean_object* v_a_4145_, lean_object* v_c_4146_, lean_object* v_numDigits_4147_, lean_object* v_as_4148_, lean_object* v_sz_4149_, lean_object* v_i_4150_, lean_object* v_b_4151_, lean_object* v___y_4152_){
_start:
{
uint64_t v___x_7681__boxed_4153_; uint64_t v_a_7682__boxed_4154_; size_t v_sz_boxed_4155_; size_t v_i_boxed_4156_; lean_object* v_res_4157_; 
v___x_7681__boxed_4153_ = lean_unbox_uint64(v___x_4144_);
lean_dec_ref(v___x_4144_);
v_a_7682__boxed_4154_ = lean_unbox_uint64(v_a_4145_);
lean_dec_ref(v_a_4145_);
v_sz_boxed_4155_ = lean_unbox_usize(v_sz_4149_);
lean_dec(v_sz_4149_);
v_i_boxed_4156_ = lean_unbox_usize(v_i_4150_);
lean_dec(v_i_4150_);
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7681__boxed_4153_, v_a_7682__boxed_4154_, v_c_4146_, v_numDigits_4147_, v_as_4148_, v_sz_boxed_4155_, v_i_boxed_4156_, v_b_4151_);
lean_dec_ref(v_as_4148_);
lean_dec_ref(v_c_4146_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4162_, lean_object* v_candidates_x3f_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___f_4175_; lean_object* v___x_4176_; 
v___f_4175_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4176_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4175_, v_candidates_x3f_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v_candidates_4178_; lean_object* v_numDigits_4179_; lean_object* v___x_4180_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4176_, 1);
v_candidates_4178_ = lean_ctor_get(v_a_4177_, 0);
lean_inc_ref(v_candidates_4178_);
v_numDigits_4179_ = lean_ctor_get(v_a_4177_, 1);
lean_inc(v_numDigits_4179_);
lean_dec(v_a_4177_);
v___x_4180_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4162_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint64_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; size_t v_sz_4189_; size_t v___x_4190_; uint64_t v___x_4191_; lean_object* v___x_4192_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v___x_4182_ = lean_unsigned_to_nat(64u);
v___x_4183_ = lean_unsigned_to_nat(4u);
v___x_4184_ = lean_nat_mul(v___x_4183_, v_numDigits_4179_);
v___x_4185_ = lean_nat_sub(v___x_4182_, v___x_4184_);
lean_dec(v___x_4184_);
v___x_4186_ = lean_uint64_of_nat(v___x_4185_);
lean_dec(v___x_4185_);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4189_ = lean_array_size(v_candidates_4178_);
v___x_4190_ = ((size_t)0ULL);
v___x_4191_ = lean_unbox_uint64(v_a_4181_);
lean_inc(v_numDigits_4179_);
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4186_, v___x_4191_, v_c_4162_, v_numDigits_4179_, v_candidates_4178_, v_sz_4189_, v___x_4190_, v___x_4188_);
lean_dec_ref(v_candidates_4178_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4207_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4207_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4207_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v_fst_4197_; 
v_fst_4197_ = lean_ctor_get(v_a_4193_, 0);
lean_inc(v_fst_4197_);
lean_dec(v_a_4193_);
if (lean_obj_tag(v_fst_4197_) == 0)
{
lean_object* v___x_4198_; uint64_t v___x_4199_; lean_object* v___x_4201_; 
v___x_4198_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4198_, 0, v_numDigits_4179_);
lean_ctor_set(v___x_4198_, 1, v___x_4187_);
v___x_4199_ = lean_unbox_uint64(v_a_4181_);
lean_dec(v_a_4181_);
lean_ctor_set_uint64(v___x_4198_, sizeof(void*)*2, v___x_4199_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v___x_4198_);
v___x_4201_ = v___x_4195_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4198_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
else
{
lean_object* v_val_4203_; lean_object* v___x_4205_; 
lean_dec(v_a_4181_);
lean_dec(v_numDigits_4179_);
v_val_4203_ = lean_ctor_get(v_fst_4197_, 0);
lean_inc(v_val_4203_);
lean_dec_ref_known(v_fst_4197_, 1);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v_val_4203_);
v___x_4205_ = v___x_4195_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_val_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v_a_4181_);
lean_dec(v_numDigits_4179_);
v_a_4208_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4192_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4192_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_numDigits_4179_);
lean_dec_ref(v_candidates_4178_);
v_a_4216_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4180_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4180_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4176_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4176_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4232_, lean_object* v_candidates_x3f_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4232_, v_candidates_x3f_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec_ref(v_c_4232_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4246_, uint64_t v_a_4247_, lean_object* v_c_4248_, lean_object* v_numDigits_4249_, lean_object* v_as_4250_, size_t v_sz_4251_, size_t v_i_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4246_, v_a_4247_, v_c_4248_, v_numDigits_4249_, v_as_4250_, v_sz_4251_, v_i_4252_, v_b_4253_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4266_ = _args[0];
lean_object* v_a_4267_ = _args[1];
lean_object* v_c_4268_ = _args[2];
lean_object* v_numDigits_4269_ = _args[3];
lean_object* v_as_4270_ = _args[4];
lean_object* v_sz_4271_ = _args[5];
lean_object* v_i_4272_ = _args[6];
lean_object* v_b_4273_ = _args[7];
lean_object* v___y_4274_ = _args[8];
lean_object* v___y_4275_ = _args[9];
lean_object* v___y_4276_ = _args[10];
lean_object* v___y_4277_ = _args[11];
lean_object* v___y_4278_ = _args[12];
lean_object* v___y_4279_ = _args[13];
lean_object* v___y_4280_ = _args[14];
lean_object* v___y_4281_ = _args[15];
lean_object* v___y_4282_ = _args[16];
lean_object* v___y_4283_ = _args[17];
lean_object* v___y_4284_ = _args[18];
_start:
{
uint64_t v___x_7880__boxed_4285_; uint64_t v_a_7881__boxed_4286_; size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v___x_7880__boxed_4285_ = lean_unbox_uint64(v___x_4266_);
lean_dec_ref(v___x_4266_);
v_a_7881__boxed_4286_ = lean_unbox_uint64(v_a_4267_);
lean_dec_ref(v_a_4267_);
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4271_);
lean_dec(v_sz_4271_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7880__boxed_4285_, v_a_7881__boxed_4286_, v_c_4268_, v_numDigits_4269_, v_as_4270_, v_sz_boxed_4287_, v_i_boxed_4288_, v_b_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v_as_4270_);
lean_dec_ref(v_c_4268_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_numDigits_4317_; uint64_t v_anchor_4318_; lean_object* v_ordinal_4319_; lean_object* v___x_4320_; 
v_numDigits_4317_ = lean_ctor_get(v_info_4314_, 0);
v_anchor_4318_ = lean_ctor_get_uint64(v_info_4314_, sizeof(void*)*2);
v_ordinal_4319_ = lean_ctor_get(v_info_4314_, 1);
v___x_4320_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4317_, v_anchor_4318_, v_a_4315_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4357_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4323_ = v___x_4320_;
v_isShared_4324_ = v_isSharedCheck_4357_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4320_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4357_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_nat_dec_eq(v_ordinal_4319_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v_ref_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
v_ref_4327_ = lean_ctor_get(v_a_4315_, 2);
v___x_4328_ = l_Lean_SourceInfo_fromRef(v_ref_4327_, v___x_4326_);
v___x_4329_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4330_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4328_, 3);
v___x_4331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4328_);
lean_ctor_set(v___x_4331_, 1, v___x_4329_);
v___x_4332_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4333_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4328_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = lean_unsigned_to_nat(1u);
v___x_4336_ = lean_nat_add(v_ordinal_4319_, v___x_4335_);
v___x_4337_ = l_Nat_reprFast(v___x_4336_);
v___x_4338_ = lean_box(2);
v___x_4339_ = l_Lean_Syntax_mkNumLit(v___x_4337_, v___x_4338_);
v___x_4340_ = l_Lean_Syntax_node3(v___x_4328_, v___x_4332_, v_a_4321_, v___x_4334_, v___x_4339_);
v___x_4341_ = l_Lean_Syntax_node2(v___x_4328_, v___x_4330_, v___x_4331_, v___x_4340_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4341_);
v___x_4343_ = v___x_4323_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
else
{
lean_object* v_ref_4345_; uint8_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
v_ref_4345_ = lean_ctor_get(v_a_4315_, 2);
v___x_4346_ = 0;
v___x_4347_ = l_Lean_SourceInfo_fromRef(v_ref_4345_, v___x_4346_);
v___x_4348_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4349_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4347_, 2);
v___x_4350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4347_);
lean_ctor_set(v___x_4350_, 1, v___x_4348_);
v___x_4351_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4352_ = l_Lean_Syntax_node1(v___x_4347_, v___x_4351_, v_a_4321_);
v___x_4353_ = l_Lean_Syntax_node2(v___x_4347_, v___x_4349_, v___x_4350_, v___x_4352_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4353_);
v___x_4355_ = v___x_4323_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4353_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
return v___x_4320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4358_, v_a_4359_);
lean_dec_ref(v_a_4359_);
lean_dec_ref(v_info_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4362_, v_a_4363_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4367_, v_a_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec_ref(v_info_4367_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v_p_4391_; lean_object* v___x_4394_; 
lean_inc_ref(v_proof_4384_);
v___x_4394_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4384_, v_a_4386_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4433_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4433_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4433_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4415_ = l_Lean_Expr_cleanupAnnotations(v_a_4395_);
v___x_4416_ = l_Lean_Expr_isApp(v___x_4415_);
if (v___x_4416_ == 0)
{
lean_dec_ref(v___x_4415_);
v___y_4400_ = v_a_4385_;
v___y_4401_ = v_a_4386_;
v___y_4402_ = v_a_4387_;
v___y_4403_ = v_a_4388_;
goto v___jp_4399_;
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
v___y_4400_ = v_a_4385_;
v___y_4401_ = v_a_4386_;
v___y_4402_ = v_a_4387_;
v___y_4403_ = v_a_4388_;
goto v___jp_4399_;
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
v___y_4400_ = v_a_4385_;
v___y_4401_ = v_a_4386_;
v___y_4402_ = v_a_4387_;
v___y_4403_ = v_a_4388_;
goto v___jp_4399_;
}
else
{
lean_del_object(v___x_4397_);
lean_dec_ref(v_proof_4384_);
v_p_4391_ = v_arg_4417_;
goto v___jp_4390_;
}
}
else
{
lean_dec_ref(v___x_4421_);
lean_del_object(v___x_4397_);
lean_dec_ref(v_proof_4384_);
v_p_4391_ = v_arg_4417_;
goto v___jp_4390_;
}
}
else
{
uint8_t v___x_4428_; 
lean_dec_ref(v___x_4421_);
lean_del_object(v___x_4397_);
lean_dec_ref(v_proof_4384_);
v___x_4428_ = l_Lean_Expr_isFalse(v_arg_4420_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref(v_arg_4417_);
v___x_4429_ = lean_box(0);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4431_, 0, v_arg_4417_);
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
}
}
v___jp_4399_:
{
if (lean_obj_tag(v_proof_4384_) == 6)
{
lean_object* v_body_4404_; uint8_t v___x_4405_; 
v_body_4404_ = lean_ctor_get(v_proof_4384_, 2);
lean_inc_ref(v_body_4404_);
lean_dec_ref_known(v_proof_4384_, 3);
v___x_4405_ = l_Lean_Expr_hasLooseBVars(v_body_4404_);
if (v___x_4405_ == 0)
{
lean_del_object(v___x_4397_);
v_proof_4384_ = v_body_4404_;
v_a_4385_ = v___y_4400_;
v_a_4386_ = v___y_4401_;
v_a_4387_ = v___y_4402_;
v_a_4388_ = v___y_4403_;
goto _start;
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4409_; 
lean_dec_ref(v_body_4404_);
v___x_4407_ = lean_box(0);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4407_);
v___x_4409_ = v___x_4397_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4413_; 
lean_dec_ref(v_proof_4384_);
v___x_4411_ = lean_box(0);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4411_);
v___x_4413_ = v___x_4397_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v_proof_4384_);
v_a_4434_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4394_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4394_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
v___jp_4390_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4392_, 0, v_p_4391_);
v___x_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
return v___x_4393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v___x_4452_; 
v___x_4452_ = l_Lean_Expr_hasMVar(v_e_4449_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v_e_4449_);
return v___x_4453_;
}
else
{
lean_object* v___x_4454_; lean_object* v_mctx_4455_; lean_object* v___x_4456_; lean_object* v_fst_4457_; lean_object* v_snd_4458_; lean_object* v___x_4459_; lean_object* v_cache_4460_; lean_object* v_zetaDeltaFVarIds_4461_; lean_object* v_postponed_4462_; lean_object* v_diag_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4472_; 
v___x_4454_ = lean_st_ref_get(v___y_4450_);
v_mctx_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc_ref(v_mctx_4455_);
lean_dec(v___x_4454_);
v___x_4456_ = l_Lean_instantiateMVarsCore(v_mctx_4455_, v_e_4449_);
v_fst_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_fst_4457_);
v_snd_4458_ = lean_ctor_get(v___x_4456_, 1);
lean_inc(v_snd_4458_);
lean_dec_ref(v___x_4456_);
v___x_4459_ = lean_st_ref_take(v___y_4450_);
v_cache_4460_ = lean_ctor_get(v___x_4459_, 1);
v_zetaDeltaFVarIds_4461_ = lean_ctor_get(v___x_4459_, 2);
v_postponed_4462_ = lean_ctor_get(v___x_4459_, 3);
v_diag_4463_ = lean_ctor_get(v___x_4459_, 4);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v___x_4459_, 0);
lean_dec(v_unused_4473_);
v___x_4465_ = v___x_4459_;
v_isShared_4466_ = v_isSharedCheck_4472_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_diag_4463_);
lean_inc(v_postponed_4462_);
lean_inc(v_zetaDeltaFVarIds_4461_);
lean_inc(v_cache_4460_);
lean_dec(v___x_4459_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4472_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v_snd_4458_);
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_snd_4458_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_cache_4460_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_zetaDeltaFVarIds_4461_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_postponed_4462_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_diag_4463_);
v___x_4468_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_st_ref_put(v___y_4450_, v___x_4468_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v_fst_4457_);
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4474_, v___y_4475_);
lean_dec(v___y_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4478_, v___y_4480_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4492_, lean_object* v_x_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4492_, v_x_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_a_4508_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4499_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4499_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4516_, lean_object* v_x_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4516_, v_x_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4524_, lean_object* v_mvarId_4525_, lean_object* v_x_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4525_, v_x_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4533_, lean_object* v_mvarId_4534_, lean_object* v_x_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4533_, v_mvarId_4534_, v_x_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4559_; 
v___x_4548_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4542_, v___y_4544_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4559_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4559_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
uint8_t v___x_4553_; 
v___x_4553_ = l_Lean_Expr_hasSyntheticSorry(v_a_4549_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; 
lean_del_object(v___x_4551_);
v___x_4554_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4549_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4554_;
}
else
{
lean_object* v___x_4555_; lean_object* v___x_4557_; 
lean_dec(v_a_4549_);
v___x_4555_ = lean_box(0);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4555_);
v___x_4557_ = v___x_4551_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v___x_4573_; lean_object* v___f_4574_; lean_object* v___x_4575_; 
lean_inc(v_mvarId_4567_);
v___x_4573_ = l_Lean_mkMVar(v_mvarId_4567_);
v___f_4574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4574_, 0, v___x_4573_);
v___x_4575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4567_, v___f_4574_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
return v_res_4582_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4604_){
_start:
{
if (lean_obj_tag(v_x_4604_) == 0)
{
uint8_t v___x_4605_; 
v___x_4605_ = 1;
return v___x_4605_;
}
else
{
lean_object* v_head_4606_; lean_object* v_tail_4607_; uint8_t v___y_4609_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v_head_4606_ = lean_ctor_get(v_x_4604_, 0);
lean_inc_n(v_head_4606_, 2);
v_tail_4607_ = lean_ctor_get(v_x_4604_, 1);
lean_inc(v_tail_4607_);
lean_dec_ref_known(v_x_4604_, 2);
v___x_4611_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4612_ = l_Lean_Syntax_isOfKind(v_head_4606_, v___x_4611_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4606_);
v___x_4614_ = l_Lean_Syntax_isOfKind(v_head_4606_, v___x_4613_);
if (v___x_4614_ == 0)
{
lean_dec(v_head_4606_);
v_x_4604_ = v_tail_4607_;
goto _start;
}
else
{
if (v___x_4612_ == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4616_ = lean_unsigned_to_nat(1u);
v___x_4617_ = l_Lean_Syntax_getArg(v_head_4606_, v___x_4616_);
lean_dec(v_head_4606_);
v___x_4618_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4619_ = l_Lean_Syntax_isOfKind(v___x_4617_, v___x_4618_);
if (v___x_4619_ == 0)
{
v_x_4604_ = v_tail_4607_;
goto _start;
}
else
{
v___y_4609_ = v___x_4612_;
goto v___jp_4608_;
}
}
else
{
lean_dec(v_head_4606_);
v___y_4609_ = v___x_4612_;
goto v___jp_4608_;
}
}
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4621_ = lean_unsigned_to_nat(3u);
v___x_4622_ = l_Lean_Syntax_getArg(v_head_4606_, v___x_4621_);
lean_dec(v_head_4606_);
v___x_4623_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4624_ = l_Lean_Syntax_isOfKind(v___x_4622_, v___x_4623_);
if (v___x_4624_ == 0)
{
v_x_4604_ = v_tail_4607_;
goto _start;
}
else
{
uint8_t v___x_4626_; 
lean_dec(v_tail_4607_);
v___x_4626_ = 0;
return v___x_4626_;
}
}
v___jp_4608_:
{
if (v___y_4609_ == 0)
{
lean_dec(v_tail_4607_);
return v___y_4609_;
}
else
{
v_x_4604_ = v_tail_4607_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4627_){
_start:
{
uint8_t v_res_4628_; lean_object* v_r_4629_; 
v_res_4628_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4627_);
v_r_4629_ = lean_box(v_res_4628_);
return v_r_4629_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4630_){
_start:
{
uint8_t v___x_4631_; 
v___x_4631_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4632_){
_start:
{
uint8_t v_res_4633_; lean_object* v_r_4634_; 
v_res_4633_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4632_);
v_r_4634_ = lean_box(v_res_4633_);
return v_r_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4650_, lean_object* v_a_4651_){
_start:
{
if (lean_obj_tag(v_seq_4650_) == 0)
{
lean_object* v_ref_4653_; uint8_t v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v_ref_4653_ = lean_ctor_get(v_a_4651_, 2);
v___x_4654_ = 0;
v___x_4655_ = l_Lean_SourceInfo_fromRef(v_ref_4653_, v___x_4654_);
v___x_4656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4655_);
v___x_4658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4655_);
lean_ctor_set(v___x_4658_, 1, v___x_4656_);
v___x_4659_ = l_Lean_Syntax_node1(v___x_4655_, v___x_4657_, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
else
{
lean_object* v_tail_4661_; 
v_tail_4661_ = lean_ctor_get(v_seq_4650_, 1);
if (lean_obj_tag(v_tail_4661_) == 0)
{
lean_object* v_head_4662_; lean_object* v___x_4663_; 
v_head_4662_ = lean_ctor_get(v_seq_4650_, 0);
lean_inc(v_head_4662_);
lean_dec_ref_known(v_seq_4650_, 2);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_head_4662_);
return v___x_4663_;
}
else
{
lean_object* v_head_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4686_; 
lean_inc(v_tail_4661_);
v_head_4664_ = lean_ctor_get(v_seq_4650_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_seq_4650_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; 
v_unused_4687_ = lean_ctor_get(v_seq_4650_, 1);
lean_dec(v_unused_4687_);
v___x_4666_ = v_seq_4650_;
v_isShared_4667_ = v_isSharedCheck_4686_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_head_4664_);
lean_dec(v_seq_4650_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4686_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4685_; 
v___x_4668_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4661_, v_a_4651_);
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4671_ = v___x_4668_;
v_isShared_4672_ = v_isSharedCheck_4685_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4685_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v_ref_4673_; uint8_t v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v_ref_4673_ = lean_ctor_get(v_a_4651_, 2);
v___x_4674_ = 0;
v___x_4675_ = l_Lean_SourceInfo_fromRef(v_ref_4673_, v___x_4674_);
v___x_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4675_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set_tag(v___x_4666_, 2);
lean_ctor_set(v___x_4666_, 1, v___x_4677_);
lean_ctor_set(v___x_4666_, 0, v___x_4675_);
v___x_4679_ = v___x_4666_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4680_ = l_Lean_Syntax_node3(v___x_4675_, v___x_4676_, v_head_4664_, v___x_4679_, v_a_4669_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4680_);
v___x_4682_ = v___x_4671_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4688_, v_a_4689_);
lean_dec_ref(v_a_4689_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4692_, v_a_4693_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4702_, lean_object* v_seq_4703_, lean_object* v_a_4704_){
_start:
{
if (lean_obj_tag(v_seq_4703_) == 0)
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4706_, 0, v_cases_4702_);
return v___x_4706_;
}
else
{
lean_object* v___x_4707_; lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4722_; 
v___x_4707_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4703_, v_a_4704_);
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4722_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4722_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v_ref_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4720_; 
v_ref_4712_ = lean_ctor_get(v_a_4704_, 2);
v___x_4713_ = 0;
v___x_4714_ = l_Lean_SourceInfo_fromRef(v_ref_4712_, v___x_4713_);
v___x_4715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4714_);
v___x_4717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4714_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_Syntax_node3(v___x_4714_, v___x_4715_, v_cases_4702_, v___x_4717_, v_a_4708_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 0, v___x_4718_);
v___x_4720_ = v___x_4710_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4718_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4723_, lean_object* v_seq_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4723_, v_seq_4724_, v_a_4725_);
lean_dec_ref(v_a_4725_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4728_, lean_object* v_seq_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4728_, v_seq_4729_, v_a_4730_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4734_, lean_object* v_seq_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4734_, v_seq_4735_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4739_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4740_, lean_object* v_x_4741_){
_start:
{
if (lean_obj_tag(v_x_4740_) == 0)
{
if (lean_obj_tag(v_x_4741_) == 0)
{
uint8_t v___x_4742_; 
v___x_4742_ = 1;
return v___x_4742_;
}
else
{
uint8_t v___x_4743_; 
v___x_4743_ = 0;
return v___x_4743_;
}
}
else
{
if (lean_obj_tag(v_x_4741_) == 0)
{
uint8_t v___x_4744_; 
v___x_4744_ = 0;
return v___x_4744_;
}
else
{
lean_object* v_head_4745_; lean_object* v_tail_4746_; lean_object* v_head_4747_; lean_object* v_tail_4748_; uint8_t v___x_4749_; 
v_head_4745_ = lean_ctor_get(v_x_4740_, 0);
v_tail_4746_ = lean_ctor_get(v_x_4740_, 1);
v_head_4747_ = lean_ctor_get(v_x_4741_, 0);
v_tail_4748_ = lean_ctor_get(v_x_4741_, 1);
v___x_4749_ = l_Lean_Syntax_structEq(v_head_4745_, v_head_4747_);
if (v___x_4749_ == 0)
{
return v___x_4749_;
}
else
{
v_x_4740_ = v_tail_4746_;
v_x_4741_ = v_tail_4748_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4751_, lean_object* v_x_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4751_, v_x_4752_);
lean_dec(v_x_4752_);
lean_dec(v_x_4751_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4755_, lean_object* v___x_4756_, lean_object* v_as_4757_, size_t v_i_4758_, size_t v_stop_4759_){
_start:
{
uint8_t v___x_4764_; 
v___x_4764_ = lean_usize_dec_eq(v_i_4758_, v_stop_4759_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_array_uget_borrowed(v_as_4757_, v_i_4758_);
v___x_4766_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4765_, v_alt_4755_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = lean_nat_dec_lt(v___x_4767_, v___x_4756_);
if (v___x_4768_ == 0)
{
goto v___jp_4760_;
}
else
{
return v___x_4768_;
}
}
else
{
goto v___jp_4760_;
}
}
else
{
uint8_t v___x_4769_; 
v___x_4769_ = 0;
return v___x_4769_;
}
v___jp_4760_:
{
size_t v___x_4761_; size_t v___x_4762_; 
v___x_4761_ = ((size_t)1ULL);
v___x_4762_ = lean_usize_add(v_i_4758_, v___x_4761_);
v_i_4758_ = v___x_4762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4770_, lean_object* v___x_4771_, lean_object* v_as_4772_, lean_object* v_i_4773_, lean_object* v_stop_4774_){
_start:
{
size_t v_i_boxed_4775_; size_t v_stop_boxed_4776_; uint8_t v_res_4777_; lean_object* v_r_4778_; 
v_i_boxed_4775_ = lean_unbox_usize(v_i_4773_);
lean_dec(v_i_4773_);
v_stop_boxed_4776_ = lean_unbox_usize(v_stop_4774_);
lean_dec(v_stop_4774_);
v_res_4777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4770_, v___x_4771_, v_as_4772_, v_i_boxed_4775_, v_stop_boxed_4776_);
lean_dec_ref(v_as_4772_);
lean_dec(v___x_4771_);
lean_dec(v_alt_4770_);
v_r_4778_ = lean_box(v_res_4777_);
return v_r_4778_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4779_){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = lean_array_get_size(v_alts_4779_);
v___x_4782_ = lean_nat_dec_lt(v___x_4780_, v___x_4781_);
if (v___x_4782_ == 0)
{
uint8_t v___x_4783_; 
v___x_4783_ = 1;
return v___x_4783_;
}
else
{
lean_object* v_alt_4784_; uint8_t v___x_4785_; 
v_alt_4784_ = lean_array_fget_borrowed(v_alts_4779_, v___x_4780_);
lean_inc(v_alt_4784_);
v___x_4785_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4784_);
if (v___x_4785_ == 0)
{
return v___x_4785_;
}
else
{
if (v___x_4782_ == 0)
{
return v___x_4782_;
}
else
{
if (v___x_4782_ == 0)
{
return v___x_4782_;
}
else
{
size_t v___x_4786_; size_t v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = lean_usize_of_nat(v___x_4781_);
v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4784_, v___x_4781_, v_alts_4779_, v___x_4786_, v___x_4787_);
if (v___x_4788_ == 0)
{
return v___x_4782_;
}
else
{
uint8_t v___x_4789_; 
v___x_4789_ = 0;
return v___x_4789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4790_){
_start:
{
uint8_t v_res_4791_; lean_object* v_r_4792_; 
v_res_4791_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4790_);
lean_dec_ref(v_alts_4790_);
v_r_4792_ = lean_box(v_res_4791_);
return v_r_4792_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4800_){
_start:
{
if (lean_obj_tag(v_alt_4800_) == 1)
{
lean_object* v_tail_4801_; 
v_tail_4801_ = lean_ctor_get(v_alt_4800_, 1);
if (lean_obj_tag(v_tail_4801_) == 0)
{
lean_object* v_head_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; 
v_head_4802_ = lean_ctor_get(v_alt_4800_, 0);
lean_inc(v_head_4802_);
lean_dec_ref_known(v_alt_4800_, 2);
v___x_4803_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4804_ = l_Lean_Syntax_isOfKind(v_head_4802_, v___x_4803_);
return v___x_4804_;
}
else
{
uint8_t v___x_4805_; 
lean_dec_ref_known(v_alt_4800_, 2);
v___x_4805_ = 0;
return v___x_4805_;
}
}
else
{
uint8_t v___x_4806_; 
lean_dec(v_alt_4800_);
v___x_4806_ = 0;
return v___x_4806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4807_){
_start:
{
uint8_t v_res_4808_; lean_object* v_r_4809_; 
v_res_4808_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4807_);
v_r_4809_ = lean_box(v_res_4808_);
return v_r_4809_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4810_, lean_object* v_x_4811_, lean_object* v___y_4812_){
_start:
{
if (lean_obj_tag(v_x_4810_) == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = l_List_reverse___redArg(v_x_4811_);
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
else
{
lean_object* v_head_4816_; lean_object* v_tail_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4835_; 
v_head_4816_ = lean_ctor_get(v_x_4810_, 0);
v_tail_4817_ = lean_ctor_get(v_x_4810_, 1);
v_isSharedCheck_4835_ = !lean_is_exclusive(v_x_4810_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4819_ = v_x_4810_;
v_isShared_4820_ = v_isSharedCheck_4835_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_tail_4817_);
lean_inc(v_head_4816_);
lean_dec(v_x_4810_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4835_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4816_, v___y_4812_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v_x_4811_);
lean_ctor_set(v___x_4819_, 0, v_a_4822_);
v___x_4824_ = v___x_4819_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4822_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_x_4811_);
v___x_4824_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
v_x_4810_ = v_tail_4817_;
v_x_4811_ = v___x_4824_;
goto _start;
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_del_object(v___x_4819_);
lean_dec(v_tail_4817_);
lean_dec(v_x_4811_);
v_a_4827_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4821_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4821_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4836_, lean_object* v_x_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4836_, v_x_4837_, v___y_4838_);
lean_dec_ref(v___y_4838_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4841_, lean_object* v_alts_4842_, uint8_t v_compress_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_seq_4848_; 
if (v_compress_4843_ == 0)
{
goto v___jp_4851_;
}
else
{
uint8_t v___x_4861_; 
v___x_4861_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4842_);
if (v___x_4861_ == 0)
{
goto v___jp_4851_;
}
else
{
lean_object* v___x_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4862_ = lean_unsigned_to_nat(0u);
v___x_4863_ = lean_array_get_size(v_alts_4842_);
v___x_4864_ = lean_nat_dec_lt(v___x_4862_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
lean_dec_ref(v_alts_4842_);
v___x_4865_ = lean_box(0);
v___x_4866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4866_, 0, v_cases_4841_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
return v___x_4867_;
}
else
{
lean_object* v___x_4868_; lean_object* v_firstAlt_4869_; uint8_t v___x_4870_; 
v___x_4868_ = lean_box(0);
v_firstAlt_4869_ = lean_array_get(v___x_4868_, v_alts_4842_, v___x_4862_);
lean_dec_ref(v_alts_4842_);
lean_inc(v_firstAlt_4869_);
v___x_4870_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4880_; 
v___x_4871_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4841_, v_firstAlt_4869_, v_a_4844_);
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4880_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4880_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4876_, 0, v_a_4872_);
lean_ctor_set(v___x_4876_, 1, v___x_4868_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v___x_4876_);
v___x_4878_ = v___x_4874_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
else
{
lean_object* v___x_4881_; 
lean_dec(v_cases_4841_);
v___x_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_firstAlt_4869_);
return v___x_4881_;
}
}
}
}
v___jp_4847_:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4849_, 0, v_cases_4841_);
lean_ctor_set(v___x_4849_, 1, v_seq_4848_);
v___x_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4849_);
return v___x_4850_;
}
v___jp_4851_:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4852_ = lean_array_get_size(v_alts_4842_);
v___x_4853_ = lean_unsigned_to_nat(1u);
v___x_4854_ = lean_nat_dec_eq(v___x_4852_, v___x_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4855_ = lean_array_to_list(v_alts_4842_);
v___x_4856_ = lean_box(0);
v___x_4857_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4855_, v___x_4856_, v_a_4844_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v_seq_4848_ = v_a_4858_;
goto v___jp_4847_;
}
else
{
lean_dec(v_cases_4841_);
return v___x_4857_;
}
}
else
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = lean_array_fget(v_alts_4842_, v___x_4859_);
lean_dec_ref(v_alts_4842_);
v_seq_4848_ = v___x_4860_;
goto v___jp_4847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4882_, lean_object* v_alts_4883_, lean_object* v_compress_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
uint8_t v_compress_boxed_4888_; lean_object* v_res_4889_; 
v_compress_boxed_4888_ = lean_unbox(v_compress_4884_);
v_res_4889_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4882_, v_alts_4883_, v_compress_boxed_4888_, v_a_4885_, v_a_4886_);
lean_dec(v_a_4886_);
lean_dec_ref(v_a_4885_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4890_, lean_object* v_x_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4890_, v_x_4891_, v___y_4892_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4896_, lean_object* v_x_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4896_, v_x_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v___x_4905_; lean_object* v_env_4906_; uint8_t v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4905_ = lean_st_ref_get(v___y_4903_);
v_env_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc_ref(v_env_4906_);
lean_dec(v___x_4905_);
v___x_4907_ = l_Lean_Meta_isMatcherAppCore(v_env_4906_, v_e_4902_);
v___x_4908_ = lean_box(v___x_4907_);
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4910_, v___y_4911_);
lean_dec(v___y_4911_);
lean_dec_ref(v_e_4910_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4914_, v___y_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v_e_4927_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v___x_4951_; 
lean_inc(v___y_4945_);
lean_inc_ref(v___y_4944_);
lean_inc(v___y_4943_);
lean_inc_ref(v___y_4942_);
lean_inc(v___y_4941_);
v___x_4951_ = lean_apply_10(v_x_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, lean_box(0));
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec(v___y_4953_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4964_, lean_object* v_x_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v___f_4976_; lean_object* v___x_4977_; 
lean_inc(v___y_4970_);
lean_inc_ref(v___y_4969_);
lean_inc(v___y_4968_);
lean_inc_ref(v___y_4967_);
lean_inc(v___y_4966_);
v___f_4976_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4976_, 0, v_x_4965_);
lean_closure_set(v___f_4976_, 1, v___y_4966_);
lean_closure_set(v___f_4976_, 2, v___y_4967_);
lean_closure_set(v___f_4976_, 3, v___y_4968_);
lean_closure_set(v___f_4976_, 4, v___y_4969_);
lean_closure_set(v___f_4976_, 5, v___y_4970_);
v___x_4977_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4964_, v___f_4976_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
if (lean_obj_tag(v___x_4977_) == 0)
{
return v___x_4977_;
}
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4977_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4977_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4986_, lean_object* v_x_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4986_, v_x_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_4999_, lean_object* v_mvarId_5000_, lean_object* v_x_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5000_, v_x_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5013_, lean_object* v_mvarId_5014_, lean_object* v_x_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5013_, v_mvarId_5014_, v_x_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5027_, lean_object* v___y_5028_){
_start:
{
uint8_t v___x_5030_; 
v___x_5030_ = l_Lean_Expr_hasMVar(v_e_5027_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; 
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v_e_5027_);
return v___x_5031_;
}
else
{
lean_object* v___x_5032_; lean_object* v_mctx_5033_; lean_object* v___x_5034_; lean_object* v_fst_5035_; lean_object* v_snd_5036_; lean_object* v___x_5037_; lean_object* v_cache_5038_; lean_object* v_zetaDeltaFVarIds_5039_; lean_object* v_postponed_5040_; lean_object* v_diag_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5050_; 
v___x_5032_ = lean_st_ref_get(v___y_5028_);
v_mctx_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc_ref(v_mctx_5033_);
lean_dec(v___x_5032_);
v___x_5034_ = l_Lean_instantiateMVarsCore(v_mctx_5033_, v_e_5027_);
v_fst_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_fst_5035_);
v_snd_5036_ = lean_ctor_get(v___x_5034_, 1);
lean_inc(v_snd_5036_);
lean_dec_ref(v___x_5034_);
v___x_5037_ = lean_st_ref_take(v___y_5028_);
v_cache_5038_ = lean_ctor_get(v___x_5037_, 1);
v_zetaDeltaFVarIds_5039_ = lean_ctor_get(v___x_5037_, 2);
v_postponed_5040_ = lean_ctor_get(v___x_5037_, 3);
v_diag_5041_ = lean_ctor_get(v___x_5037_, 4);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5050_ == 0)
{
lean_object* v_unused_5051_; 
v_unused_5051_ = lean_ctor_get(v___x_5037_, 0);
lean_dec(v_unused_5051_);
v___x_5043_ = v___x_5037_;
v_isShared_5044_ = v_isSharedCheck_5050_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_diag_5041_);
lean_inc(v_postponed_5040_);
lean_inc(v_zetaDeltaFVarIds_5039_);
lean_inc(v_cache_5038_);
lean_dec(v___x_5037_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5050_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
lean_ctor_set(v___x_5043_, 0, v_snd_5036_);
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_snd_5036_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v_cache_5038_);
lean_ctor_set(v_reuseFailAlloc_5049_, 2, v_zetaDeltaFVarIds_5039_);
lean_ctor_set(v_reuseFailAlloc_5049_, 3, v_postponed_5040_);
lean_ctor_set(v_reuseFailAlloc_5049_, 4, v_diag_5041_);
v___x_5046_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = lean_st_ref_put(v___y_5028_, v___x_5046_);
v___x_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5048_, 0, v_fst_5035_);
return v___x_5048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5052_, v___y_5053_);
lean_dec(v___y_5053_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5056_, v___y_5063_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
return v_res_5079_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5082_ = l_Lean_stringToMessageData(v___x_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5083_, lean_object* v_c_5084_, lean_object* v_a_5085_, lean_object* v_numCases_5086_, uint8_t v_isRec_5087_, lean_object* v_anchorInfo_x3f_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_mvarIds_5101_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___x_5161_; 
v___x_5161_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5083_, v___y_5089_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v___y_5164_; lean_object* v___x_5216_; uint8_t v___x_5219_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5216_ = lean_unsigned_to_nat(1u);
v___x_5219_ = lean_nat_dec_lt(v___x_5216_, v_numCases_5086_);
if (v___x_5219_ == 0)
{
if (v_isRec_5087_ == 0)
{
lean_inc(v_a_5162_);
v___y_5164_ = v_a_5162_;
goto v___jp_5163_;
}
else
{
goto v___jp_5217_;
}
}
else
{
goto v___jp_5217_;
}
v___jp_5163_:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5084_);
lean_inc_ref(v___x_5083_);
v___x_5166_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5083_, v___y_5164_, v_numCases_5086_, v___x_5165_, v___y_5092_, v___y_5095_, v___y_5097_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v___x_5167_; 
lean_dec_ref_known(v___x_5166_, 1);
lean_inc_ref(v___x_5083_);
v___x_5167_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5083_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_toCold_5168_; lean_object* v_options_5169_; uint8_t v_hasTrace_5170_; 
lean_dec_ref_known(v___x_5167_, 1);
v_toCold_5168_ = lean_ctor_get(v___y_5097_, 0);
v_options_5169_ = lean_ctor_get(v_toCold_5168_, 2);
v_hasTrace_5170_ = lean_ctor_get_uint8(v_options_5169_, sizeof(void*)*1);
if (v_hasTrace_5170_ == 0)
{
lean_dec(v_a_5162_);
v___y_5105_ = v___y_5089_;
v___y_5106_ = v___y_5090_;
v___y_5107_ = v___y_5091_;
v___y_5108_ = v___y_5092_;
v___y_5109_ = v___y_5093_;
v___y_5110_ = v___y_5094_;
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
goto v___jp_5104_;
}
else
{
lean_object* v_inheritedTraceOptions_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; uint8_t v___x_5174_; 
v_inheritedTraceOptions_5171_ = lean_ctor_get(v_toCold_5168_, 11);
v___x_5172_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5173_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5171_, v_options_5169_, v___x_5173_);
if (v___x_5174_ == 0)
{
lean_dec(v_a_5162_);
v___y_5105_ = v___y_5089_;
v___y_5106_ = v___y_5090_;
v___y_5107_ = v___y_5091_;
v___y_5108_ = v___y_5092_;
v___y_5109_ = v___y_5093_;
v___y_5110_ = v___y_5094_;
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
goto v___jp_5104_;
}
else
{
lean_object* v___x_5175_; 
v___x_5175_ = l_Lean_Meta_Grind_updateLastTag(v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec_ref_known(v___x_5175_, 1);
lean_inc_ref(v___x_5083_);
v___x_5176_ = l_Lean_MessageData_ofExpr(v___x_5083_);
v___x_5177_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5176_);
lean_ctor_set(v___x_5178_, 1, v___x_5177_);
v___x_5179_ = l_Nat_reprFast(v_a_5162_);
v___x_5180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
v___x_5181_ = l_Lean_MessageData_ofFormat(v___x_5180_);
v___x_5182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5178_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
v___x_5183_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5172_, v___x_5182_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_dec_ref_known(v___x_5183_, 1);
v___y_5105_ = v___y_5089_;
v___y_5106_ = v___y_5090_;
v___y_5107_ = v___y_5091_;
v___y_5108_ = v___y_5092_;
v___y_5109_ = v___y_5093_;
v___y_5110_ = v___y_5094_;
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
goto v___jp_5104_;
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_a_5085_);
lean_dec_ref(v_c_5084_);
lean_dec_ref(v___x_5083_);
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5183_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5183_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
lean_dec(v_a_5162_);
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_a_5085_);
lean_dec_ref(v_c_5084_);
lean_dec_ref(v___x_5083_);
v_a_5192_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_5175_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5175_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
return v___x_5197_;
}
}
}
}
}
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
lean_dec(v_a_5162_);
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_a_5085_);
lean_dec_ref(v_c_5084_);
lean_dec_ref(v___x_5083_);
v_a_5200_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_5167_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5167_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5205_; 
if (v_isShared_5203_ == 0)
{
v___x_5205_ = v___x_5202_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
lean_dec(v_a_5162_);
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_a_5085_);
lean_dec_ref(v_c_5084_);
lean_dec_ref(v___x_5083_);
v_a_5208_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5166_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5166_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
v___jp_5217_:
{
lean_object* v___x_5218_; 
v___x_5218_ = lean_nat_add(v_a_5162_, v___x_5216_);
v___y_5164_ = v___x_5218_;
goto v___jp_5163_;
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_numCases_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v_c_5084_);
lean_dec_ref(v___x_5083_);
v_a_5220_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5161_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5161_);
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
v___jp_5100_:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5102_, 0, v_mvarIds_5101_);
lean_ctor_set(v___x_5102_, 1, v_anchorInfo_x3f_5088_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
v___jp_5104_:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5083_, v___y_5114_);
if (lean_obj_tag(v_c_5084_) == 1)
{
lean_object* v_e_5116_; lean_object* v_binderType_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
lean_dec_ref(v___x_5115_);
lean_dec_ref(v___x_5083_);
v_e_5116_ = lean_ctor_get(v_c_5084_, 0);
lean_inc_ref(v_e_5116_);
lean_dec_ref_known(v_c_5084_, 2);
v_binderType_5117_ = lean_ctor_get(v_e_5116_, 1);
lean_inc_ref(v_binderType_5117_);
lean_dec_ref(v_e_5116_);
v___x_5118_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5117_);
v___x_5119_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5085_, v___x_5118_, v___y_5107_, v___y_5108_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
v_mvarIds_5101_ = v_a_5120_;
goto v___jp_5100_;
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_anchorInfo_x3f_5088_);
v_a_5121_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5119_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5119_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
else
{
lean_object* v_a_5129_; uint8_t v___x_5130_; 
lean_dec_ref(v_c_5084_);
v_a_5129_ = lean_ctor_get(v___x_5115_, 0);
lean_inc(v_a_5129_);
lean_dec_ref(v___x_5115_);
v___x_5130_ = lean_unbox(v_a_5129_);
lean_dec(v_a_5129_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; 
v___x_5131_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5083_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5133_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5131_, 1);
v___x_5133_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5085_, v_a_5132_, v___y_5107_, v___y_5108_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_a_5134_);
lean_dec_ref_known(v___x_5133_, 1);
v_mvarIds_5101_ = v_a_5134_;
goto v___jp_5100_;
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_dec(v_anchorInfo_x3f_5088_);
v_a_5135_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5133_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5133_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_anchorInfo_x3f_5088_);
lean_dec(v_a_5085_);
v_a_5143_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5131_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5131_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_object* v___x_5151_; 
v___x_5151_ = l_Lean_Meta_Grind_casesMatch(v_a_5085_, v___x_5083_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5151_, 1);
v_mvarIds_5101_ = v_a_5152_;
goto v___jp_5100_;
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
lean_dec(v_anchorInfo_x3f_5088_);
v_a_5153_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5151_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5151_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5228_ = _args[0];
lean_object* v_c_5229_ = _args[1];
lean_object* v_a_5230_ = _args[2];
lean_object* v_numCases_5231_ = _args[3];
lean_object* v_isRec_5232_ = _args[4];
lean_object* v_anchorInfo_x3f_5233_ = _args[5];
lean_object* v___y_5234_ = _args[6];
lean_object* v___y_5235_ = _args[7];
lean_object* v___y_5236_ = _args[8];
lean_object* v___y_5237_ = _args[9];
lean_object* v___y_5238_ = _args[10];
lean_object* v___y_5239_ = _args[11];
lean_object* v___y_5240_ = _args[12];
lean_object* v___y_5241_ = _args[13];
lean_object* v___y_5242_ = _args[14];
lean_object* v___y_5243_ = _args[15];
lean_object* v___y_5244_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5245_; lean_object* v_res_5246_; 
v_isRec_boxed_5245_ = lean_unbox(v_isRec_5232_);
v_res_5246_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5228_, v_c_5229_, v_a_5230_, v_numCases_5231_, v_isRec_boxed_5245_, v_anchorInfo_x3f_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec(v___y_5234_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5247_, uint8_t v_trace_5248_, lean_object* v___f_5249_, lean_object* v_c_5250_, lean_object* v_candidates_x3f_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v___x_5262_; lean_object* v___y_5264_; 
v___x_5262_ = lean_st_mk_ref(v_goal_5247_);
if (v_trace_5248_ == 0)
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
lean_dec(v_candidates_x3f_5251_);
v___x_5283_ = lean_box(0);
lean_inc(v___x_5262_);
v___x_5284_ = lean_apply_12(v___f_5249_, v___x_5283_, v___x_5262_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, lean_box(0));
v___y_5264_ = v___x_5284_;
goto v___jp_5263_;
}
else
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5250_, v_candidates_x3f_5251_, v___x_5262_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v___x_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5287_, 0, v_a_5286_);
lean_inc(v___x_5262_);
v___x_5288_ = lean_apply_12(v___f_5249_, v___x_5287_, v___x_5262_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, lean_box(0));
v___y_5264_ = v___x_5288_;
goto v___jp_5263_;
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_dec(v___x_5262_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___f_5249_);
v_a_5289_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5285_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5285_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
v___jp_5263_:
{
if (lean_obj_tag(v___y_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5274_; 
v_a_5265_ = lean_ctor_get(v___y_5264_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___y_5264_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5267_ = v___y_5264_;
v_isShared_5268_ = v_isSharedCheck_5274_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___y_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5274_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5272_; 
v___x_5269_ = lean_st_ref_get(v___x_5262_);
lean_dec(v___x_5262_);
v___x_5270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5270_, 0, v_a_5265_);
lean_ctor_set(v___x_5270_, 1, v___x_5269_);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 0, v___x_5270_);
v___x_5272_ = v___x_5267_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
lean_dec(v___x_5262_);
v_a_5275_ = lean_ctor_get(v___y_5264_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___y_5264_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___y_5264_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___y_5264_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5297_, lean_object* v_trace_5298_, lean_object* v___f_5299_, lean_object* v_c_5300_, lean_object* v_candidates_x3f_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
uint8_t v_trace_boxed_5312_; lean_object* v_res_5313_; 
v_trace_boxed_5312_ = lean_unbox(v_trace_5298_);
v_res_5313_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5297_, v_trace_boxed_5312_, v___f_5299_, v_c_5300_, v_candidates_x3f_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
lean_dec_ref(v_c_5300_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5314_, lean_object* v_x_5315_, lean_object* v_x_5316_, lean_object* v_x_5317_){
_start:
{
lean_object* v_ks_5318_; lean_object* v_vs_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5343_; 
v_ks_5318_ = lean_ctor_get(v_x_5314_, 0);
v_vs_5319_ = lean_ctor_get(v_x_5314_, 1);
v_isSharedCheck_5343_ = !lean_is_exclusive(v_x_5314_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5321_ = v_x_5314_;
v_isShared_5322_ = v_isSharedCheck_5343_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_vs_5319_);
lean_inc(v_ks_5318_);
lean_dec(v_x_5314_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5343_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5323_; uint8_t v___x_5324_; 
v___x_5323_ = lean_array_get_size(v_ks_5318_);
v___x_5324_ = lean_nat_dec_lt(v_x_5315_, v___x_5323_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5328_; 
lean_dec(v_x_5315_);
v___x_5325_ = lean_array_push(v_ks_5318_, v_x_5316_);
v___x_5326_ = lean_array_push(v_vs_5319_, v_x_5317_);
if (v_isShared_5322_ == 0)
{
lean_ctor_set(v___x_5321_, 1, v___x_5326_);
lean_ctor_set(v___x_5321_, 0, v___x_5325_);
v___x_5328_ = v___x_5321_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5325_);
lean_ctor_set(v_reuseFailAlloc_5329_, 1, v___x_5326_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
else
{
lean_object* v_k_x27_5330_; uint8_t v___x_5331_; 
v_k_x27_5330_ = lean_array_fget_borrowed(v_ks_5318_, v_x_5315_);
v___x_5331_ = l_Lean_instBEqMVarId_beq(v_x_5316_, v_k_x27_5330_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5333_; 
if (v_isShared_5322_ == 0)
{
v___x_5333_ = v___x_5321_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_ks_5318_);
lean_ctor_set(v_reuseFailAlloc_5337_, 1, v_vs_5319_);
v___x_5333_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5334_ = lean_unsigned_to_nat(1u);
v___x_5335_ = lean_nat_add(v_x_5315_, v___x_5334_);
lean_dec(v_x_5315_);
v_x_5314_ = v___x_5333_;
v_x_5315_ = v___x_5335_;
goto _start;
}
}
else
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
v___x_5338_ = lean_array_fset(v_ks_5318_, v_x_5315_, v_x_5316_);
v___x_5339_ = lean_array_fset(v_vs_5319_, v_x_5315_, v_x_5317_);
lean_dec(v_x_5315_);
if (v_isShared_5322_ == 0)
{
lean_ctor_set(v___x_5321_, 1, v___x_5339_);
lean_ctor_set(v___x_5321_, 0, v___x_5338_);
v___x_5341_ = v___x_5321_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5338_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v___x_5339_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5344_, lean_object* v_k_5345_, lean_object* v_v_5346_){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = lean_unsigned_to_nat(0u);
v___x_5348_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5344_, v___x_5347_, v_k_5345_, v_v_5346_);
return v___x_5348_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5350_, size_t v_x_5351_, size_t v_x_5352_, lean_object* v_x_5353_, lean_object* v_x_5354_){
_start:
{
if (lean_obj_tag(v_x_5350_) == 0)
{
lean_object* v_es_5355_; size_t v___x_5356_; size_t v___x_5357_; lean_object* v_j_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v_es_5355_ = lean_ctor_get(v_x_5350_, 0);
v___x_5356_ = ((size_t)31ULL);
v___x_5357_ = lean_usize_land(v_x_5351_, v___x_5356_);
v_j_5358_ = lean_usize_to_nat(v___x_5357_);
v___x_5359_ = lean_array_get_size(v_es_5355_);
v___x_5360_ = lean_nat_dec_lt(v_j_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_dec(v_j_5358_);
lean_dec(v_x_5354_);
lean_dec(v_x_5353_);
return v_x_5350_;
}
else
{
lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5399_; 
lean_inc_ref(v_es_5355_);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_x_5350_);
if (v_isSharedCheck_5399_ == 0)
{
lean_object* v_unused_5400_; 
v_unused_5400_ = lean_ctor_get(v_x_5350_, 0);
lean_dec(v_unused_5400_);
v___x_5362_ = v_x_5350_;
v_isShared_5363_ = v_isSharedCheck_5399_;
goto v_resetjp_5361_;
}
else
{
lean_dec(v_x_5350_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5399_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v_v_5364_; lean_object* v___x_5365_; lean_object* v_xs_x27_5366_; lean_object* v___y_5368_; 
v_v_5364_ = lean_array_fget(v_es_5355_, v_j_5358_);
v___x_5365_ = lean_box(0);
v_xs_x27_5366_ = lean_array_fset(v_es_5355_, v_j_5358_, v___x_5365_);
switch(lean_obj_tag(v_v_5364_))
{
case 0:
{
lean_object* v_key_5373_; lean_object* v_val_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5384_; 
v_key_5373_ = lean_ctor_get(v_v_5364_, 0);
v_val_5374_ = lean_ctor_get(v_v_5364_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_v_5364_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5376_ = v_v_5364_;
v_isShared_5377_ = v_isSharedCheck_5384_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_val_5374_);
lean_inc(v_key_5373_);
lean_dec(v_v_5364_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5384_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
uint8_t v___x_5378_; 
v___x_5378_ = l_Lean_instBEqMVarId_beq(v_x_5353_, v_key_5373_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; lean_object* v___x_5380_; 
lean_del_object(v___x_5376_);
v___x_5379_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5373_, v_val_5374_, v_x_5353_, v_x_5354_);
v___x_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5379_);
v___y_5368_ = v___x_5380_;
goto v___jp_5367_;
}
else
{
lean_object* v___x_5382_; 
lean_dec(v_val_5374_);
lean_dec(v_key_5373_);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v_x_5354_);
lean_ctor_set(v___x_5376_, 0, v_x_5353_);
v___x_5382_ = v___x_5376_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_x_5353_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_x_5354_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
v___y_5368_ = v___x_5382_;
goto v___jp_5367_;
}
}
}
}
case 1:
{
lean_object* v_node_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5397_; 
v_node_5385_ = lean_ctor_get(v_v_5364_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v_v_5364_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5387_ = v_v_5364_;
v_isShared_5388_ = v_isSharedCheck_5397_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_node_5385_);
lean_dec(v_v_5364_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5397_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
size_t v___x_5389_; size_t v___x_5390_; size_t v___x_5391_; size_t v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5395_; 
v___x_5389_ = ((size_t)5ULL);
v___x_5390_ = lean_usize_shift_right(v_x_5351_, v___x_5389_);
v___x_5391_ = ((size_t)1ULL);
v___x_5392_ = lean_usize_add(v_x_5352_, v___x_5391_);
v___x_5393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5385_, v___x_5390_, v___x_5392_, v_x_5353_, v_x_5354_);
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 0, v___x_5393_);
v___x_5395_ = v___x_5387_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5393_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
v___y_5368_ = v___x_5395_;
goto v___jp_5367_;
}
}
}
default: 
{
lean_object* v___x_5398_; 
v___x_5398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5398_, 0, v_x_5353_);
lean_ctor_set(v___x_5398_, 1, v_x_5354_);
v___y_5368_ = v___x_5398_;
goto v___jp_5367_;
}
}
v___jp_5367_:
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
v___x_5369_ = lean_array_fset(v_xs_x27_5366_, v_j_5358_, v___y_5368_);
lean_dec(v_j_5358_);
if (v_isShared_5363_ == 0)
{
lean_ctor_set(v___x_5362_, 0, v___x_5369_);
v___x_5371_ = v___x_5362_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
else
{
lean_object* v_ks_5401_; lean_object* v_vs_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5420_; 
v_ks_5401_ = lean_ctor_get(v_x_5350_, 0);
v_vs_5402_ = lean_ctor_get(v_x_5350_, 1);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_x_5350_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5404_ = v_x_5350_;
v_isShared_5405_ = v_isSharedCheck_5420_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_vs_5402_);
lean_inc(v_ks_5401_);
lean_dec(v_x_5350_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5420_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_ks_5401_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_vs_5402_);
v___x_5407_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v_newNode_5408_; size_t v___x_5409_; uint8_t v___x_5410_; 
v_newNode_5408_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5407_, v_x_5353_, v_x_5354_);
v___x_5409_ = ((size_t)7ULL);
v___x_5410_ = lean_usize_dec_le(v___x_5409_, v_x_5352_);
if (v___x_5410_ == 0)
{
lean_object* v___x_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; 
v___x_5411_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5408_);
v___x_5412_ = lean_unsigned_to_nat(4u);
v___x_5413_ = lean_nat_dec_lt(v___x_5411_, v___x_5412_);
lean_dec(v___x_5411_);
if (v___x_5413_ == 0)
{
lean_object* v_ks_5414_; lean_object* v_vs_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v_ks_5414_ = lean_ctor_get(v_newNode_5408_, 0);
lean_inc_ref(v_ks_5414_);
v_vs_5415_ = lean_ctor_get(v_newNode_5408_, 1);
lean_inc_ref(v_vs_5415_);
lean_dec_ref(v_newNode_5408_);
v___x_5416_ = lean_unsigned_to_nat(0u);
v___x_5417_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5418_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5352_, v_ks_5414_, v_vs_5415_, v___x_5416_, v___x_5417_);
lean_dec_ref(v_vs_5415_);
lean_dec_ref(v_ks_5414_);
return v___x_5418_;
}
else
{
return v_newNode_5408_;
}
}
else
{
return v_newNode_5408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5421_, lean_object* v_keys_5422_, lean_object* v_vals_5423_, lean_object* v_i_5424_, lean_object* v_entries_5425_){
_start:
{
lean_object* v___x_5426_; uint8_t v___x_5427_; 
v___x_5426_ = lean_array_get_size(v_keys_5422_);
v___x_5427_ = lean_nat_dec_lt(v_i_5424_, v___x_5426_);
if (v___x_5427_ == 0)
{
lean_dec(v_i_5424_);
return v_entries_5425_;
}
else
{
lean_object* v_k_5428_; lean_object* v_v_5429_; uint64_t v___x_5430_; size_t v_h_5431_; size_t v___x_5432_; lean_object* v___x_5433_; size_t v___x_5434_; size_t v___x_5435_; size_t v___x_5436_; size_t v_h_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v_k_5428_ = lean_array_fget_borrowed(v_keys_5422_, v_i_5424_);
v_v_5429_ = lean_array_fget_borrowed(v_vals_5423_, v_i_5424_);
v___x_5430_ = l_Lean_instHashableMVarId_hash(v_k_5428_);
v_h_5431_ = lean_uint64_to_usize(v___x_5430_);
v___x_5432_ = ((size_t)5ULL);
v___x_5433_ = lean_unsigned_to_nat(1u);
v___x_5434_ = ((size_t)1ULL);
v___x_5435_ = lean_usize_sub(v_depth_5421_, v___x_5434_);
v___x_5436_ = lean_usize_mul(v___x_5432_, v___x_5435_);
v_h_5437_ = lean_usize_shift_right(v_h_5431_, v___x_5436_);
v___x_5438_ = lean_nat_add(v_i_5424_, v___x_5433_);
lean_dec(v_i_5424_);
lean_inc(v_v_5429_);
lean_inc(v_k_5428_);
v___x_5439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5425_, v_h_5437_, v_depth_5421_, v_k_5428_, v_v_5429_);
v_i_5424_ = v___x_5438_;
v_entries_5425_ = v___x_5439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5441_, lean_object* v_keys_5442_, lean_object* v_vals_5443_, lean_object* v_i_5444_, lean_object* v_entries_5445_){
_start:
{
size_t v_depth_boxed_5446_; lean_object* v_res_5447_; 
v_depth_boxed_5446_ = lean_unbox_usize(v_depth_5441_);
lean_dec(v_depth_5441_);
v_res_5447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5446_, v_keys_5442_, v_vals_5443_, v_i_5444_, v_entries_5445_);
lean_dec_ref(v_vals_5443_);
lean_dec_ref(v_keys_5442_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5448_, lean_object* v_x_5449_, lean_object* v_x_5450_, lean_object* v_x_5451_, lean_object* v_x_5452_){
_start:
{
size_t v_x_66894__boxed_5453_; size_t v_x_66895__boxed_5454_; lean_object* v_res_5455_; 
v_x_66894__boxed_5453_ = lean_unbox_usize(v_x_5449_);
lean_dec(v_x_5449_);
v_x_66895__boxed_5454_ = lean_unbox_usize(v_x_5450_);
lean_dec(v_x_5450_);
v_res_5455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5448_, v_x_66894__boxed_5453_, v_x_66895__boxed_5454_, v_x_5451_, v_x_5452_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5456_, lean_object* v_x_5457_, lean_object* v_x_5458_){
_start:
{
uint64_t v___x_5459_; size_t v___x_5460_; size_t v___x_5461_; lean_object* v___x_5462_; 
v___x_5459_ = l_Lean_instHashableMVarId_hash(v_x_5457_);
v___x_5460_ = lean_uint64_to_usize(v___x_5459_);
v___x_5461_ = ((size_t)1ULL);
v___x_5462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5456_, v___x_5460_, v___x_5461_, v_x_5457_, v_x_5458_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5463_, lean_object* v_val_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v___x_5467_; lean_object* v_mctx_5468_; lean_object* v_cache_5469_; lean_object* v_zetaDeltaFVarIds_5470_; lean_object* v_postponed_5471_; lean_object* v_diag_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5501_; 
v___x_5467_ = lean_st_ref_take(v___y_5465_);
v_mctx_5468_ = lean_ctor_get(v___x_5467_, 0);
v_cache_5469_ = lean_ctor_get(v___x_5467_, 1);
v_zetaDeltaFVarIds_5470_ = lean_ctor_get(v___x_5467_, 2);
v_postponed_5471_ = lean_ctor_get(v___x_5467_, 3);
v_diag_5472_ = lean_ctor_get(v___x_5467_, 4);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5474_ = v___x_5467_;
v_isShared_5475_ = v_isSharedCheck_5501_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_diag_5472_);
lean_inc(v_postponed_5471_);
lean_inc(v_zetaDeltaFVarIds_5470_);
lean_inc(v_cache_5469_);
lean_inc(v_mctx_5468_);
lean_dec(v___x_5467_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5501_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v_depth_5476_; lean_object* v_levelAssignDepth_5477_; lean_object* v_lmvarCounter_5478_; lean_object* v_mvarCounter_5479_; lean_object* v_lDecls_5480_; lean_object* v_decls_5481_; lean_object* v_userNames_5482_; lean_object* v_lAssignment_5483_; lean_object* v_eAssignment_5484_; lean_object* v_dAssignment_5485_; lean_object* v_instanceTypedMVars_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5500_; 
v_depth_5476_ = lean_ctor_get(v_mctx_5468_, 0);
v_levelAssignDepth_5477_ = lean_ctor_get(v_mctx_5468_, 1);
v_lmvarCounter_5478_ = lean_ctor_get(v_mctx_5468_, 2);
v_mvarCounter_5479_ = lean_ctor_get(v_mctx_5468_, 3);
v_lDecls_5480_ = lean_ctor_get(v_mctx_5468_, 4);
v_decls_5481_ = lean_ctor_get(v_mctx_5468_, 5);
v_userNames_5482_ = lean_ctor_get(v_mctx_5468_, 6);
v_lAssignment_5483_ = lean_ctor_get(v_mctx_5468_, 7);
v_eAssignment_5484_ = lean_ctor_get(v_mctx_5468_, 8);
v_dAssignment_5485_ = lean_ctor_get(v_mctx_5468_, 9);
v_instanceTypedMVars_5486_ = lean_ctor_get(v_mctx_5468_, 10);
v_isSharedCheck_5500_ = !lean_is_exclusive(v_mctx_5468_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5488_ = v_mctx_5468_;
v_isShared_5489_ = v_isSharedCheck_5500_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_instanceTypedMVars_5486_);
lean_inc(v_dAssignment_5485_);
lean_inc(v_eAssignment_5484_);
lean_inc(v_lAssignment_5483_);
lean_inc(v_userNames_5482_);
lean_inc(v_decls_5481_);
lean_inc(v_lDecls_5480_);
lean_inc(v_mvarCounter_5479_);
lean_inc(v_lmvarCounter_5478_);
lean_inc(v_levelAssignDepth_5477_);
lean_inc(v_depth_5476_);
lean_dec(v_mctx_5468_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5500_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5490_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5484_, v_mvarId_5463_, v_val_5464_);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 8, v___x_5490_);
v___x_5492_ = v___x_5488_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_depth_5476_);
lean_ctor_set(v_reuseFailAlloc_5499_, 1, v_levelAssignDepth_5477_);
lean_ctor_set(v_reuseFailAlloc_5499_, 2, v_lmvarCounter_5478_);
lean_ctor_set(v_reuseFailAlloc_5499_, 3, v_mvarCounter_5479_);
lean_ctor_set(v_reuseFailAlloc_5499_, 4, v_lDecls_5480_);
lean_ctor_set(v_reuseFailAlloc_5499_, 5, v_decls_5481_);
lean_ctor_set(v_reuseFailAlloc_5499_, 6, v_userNames_5482_);
lean_ctor_set(v_reuseFailAlloc_5499_, 7, v_lAssignment_5483_);
lean_ctor_set(v_reuseFailAlloc_5499_, 8, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5499_, 9, v_dAssignment_5485_);
lean_ctor_set(v_reuseFailAlloc_5499_, 10, v_instanceTypedMVars_5486_);
v___x_5492_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 0, v___x_5492_);
v___x_5494_ = v___x_5474_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5492_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v_cache_5469_);
lean_ctor_set(v_reuseFailAlloc_5498_, 2, v_zetaDeltaFVarIds_5470_);
lean_ctor_set(v_reuseFailAlloc_5498_, 3, v_postponed_5471_);
lean_ctor_set(v_reuseFailAlloc_5498_, 4, v_diag_5472_);
v___x_5494_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5495_ = lean_st_ref_put(v___y_5465_, v___x_5494_);
v___x_5496_ = lean_box(0);
v___x_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5496_);
return v___x_5497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5502_, lean_object* v_val_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_){
_start:
{
lean_object* v_res_5506_; 
v_res_5506_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5502_, v_val_5503_, v___y_5504_);
lean_dec(v___y_5504_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5507_, lean_object* v_snd_5508_, uint8_t v_stopAtFirstFailure_5509_, lean_object* v_as_x27_5510_, lean_object* v_b_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_){
_start:
{
if (lean_obj_tag(v_as_x27_5510_) == 0)
{
lean_object* v___x_5522_; 
lean_dec_ref(v_snd_5508_);
lean_dec_ref(v_kp_5507_);
v___x_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5522_, 0, v_b_5511_);
return v___x_5522_;
}
else
{
lean_object* v_head_5523_; lean_object* v_tail_5524_; lean_object* v___x_5525_; 
v_head_5523_ = lean_ctor_get(v_as_x27_5510_, 0);
v_tail_5524_ = lean_ctor_get(v_as_x27_5510_, 1);
lean_inc_ref(v_kp_5507_);
lean_inc(v___y_5520_);
lean_inc_ref(v___y_5519_);
lean_inc(v___y_5518_);
lean_inc_ref(v___y_5517_);
lean_inc(v___y_5516_);
lean_inc_ref(v___y_5515_);
lean_inc(v___y_5514_);
lean_inc_ref(v___y_5513_);
lean_inc(v___y_5512_);
lean_inc(v_head_5523_);
v___x_5525_ = lean_apply_11(v_kp_5507_, v_head_5523_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, lean_box(0));
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_object* v_snd_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5621_; 
v_snd_5526_ = lean_ctor_get(v_b_5511_, 1);
v_isSharedCheck_5621_ = !lean_is_exclusive(v_b_5511_);
if (v_isSharedCheck_5621_ == 0)
{
lean_object* v_unused_5622_; 
v_unused_5622_ = lean_ctor_get(v_b_5511_, 0);
lean_dec(v_unused_5622_);
v___x_5528_ = v_b_5511_;
v_isShared_5529_ = v_isSharedCheck_5621_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_snd_5526_);
lean_dec(v_b_5511_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5621_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5620_; 
v_a_5530_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5532_ = v___x_5525_;
v_isShared_5533_ = v_isSharedCheck_5620_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5525_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5620_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_fst_5534_; lean_object* v_snd_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5619_; 
v_fst_5534_ = lean_ctor_get(v_snd_5526_, 0);
v_snd_5535_ = lean_ctor_get(v_snd_5526_, 1);
v_isSharedCheck_5619_ = !lean_is_exclusive(v_snd_5526_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5537_ = v_snd_5526_;
v_isShared_5538_ = v_isSharedCheck_5619_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_snd_5535_);
lean_inc(v_fst_5534_);
lean_dec(v_snd_5526_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5619_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5539_; 
v___x_5539_ = lean_box(0);
if (lean_obj_tag(v_a_5530_) == 0)
{
lean_object* v_seq_5540_; lean_object* v_mvarId_5541_; lean_object* v___x_5542_; 
lean_del_object(v___x_5532_);
v_seq_5540_ = lean_ctor_get(v_a_5530_, 0);
v_mvarId_5541_ = lean_ctor_get(v_head_5523_, 1);
lean_inc(v_mvarId_5541_);
v___x_5542_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5541_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_a_5543_; 
v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_a_5543_);
lean_dec_ref_known(v___x_5542_, 1);
if (lean_obj_tag(v_a_5543_) == 1)
{
lean_object* v_val_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5575_; 
lean_dec_ref(v_kp_5507_);
v_val_5544_ = lean_ctor_get(v_a_5543_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_a_5543_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5546_ = v_a_5543_;
v_isShared_5547_ = v_isSharedCheck_5575_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_val_5544_);
lean_dec(v_a_5543_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5575_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v_mvarId_5548_; lean_object* v___x_5549_; 
v_mvarId_5548_ = lean_ctor_get(v_snd_5508_, 1);
lean_inc(v_mvarId_5548_);
lean_dec_ref(v_snd_5508_);
v___x_5549_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5548_, v_val_5544_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5565_; 
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v___x_5549_, 0);
lean_dec(v_unused_5566_);
v___x_5551_ = v___x_5549_;
v_isShared_5552_ = v_isSharedCheck_5565_;
goto v_resetjp_5550_;
}
else
{
lean_dec(v___x_5549_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5565_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v_a_5530_);
v___x_5554_ = v___x_5546_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5530_);
v___x_5554_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5556_; 
if (v_isShared_5538_ == 0)
{
v___x_5556_ = v___x_5537_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_fst_5534_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_snd_5535_);
v___x_5556_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
lean_object* v___x_5558_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5556_);
lean_ctor_set(v___x_5528_, 0, v___x_5554_);
v___x_5558_ = v___x_5528_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v___x_5554_);
lean_ctor_set(v_reuseFailAlloc_5562_, 1, v___x_5556_);
v___x_5558_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
lean_object* v___x_5560_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 0, v___x_5558_);
v___x_5560_ = v___x_5551_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_del_object(v___x_5546_);
lean_dec_ref_known(v_a_5530_, 1);
lean_del_object(v___x_5537_);
lean_dec(v_snd_5535_);
lean_dec(v_fst_5534_);
lean_del_object(v___x_5528_);
v_a_5567_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5549_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5549_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
}
else
{
uint8_t v___x_5576_; 
lean_inc(v_seq_5540_);
lean_dec(v_a_5543_);
lean_dec_ref_known(v_a_5530_, 1);
v___x_5576_ = l_List_isEmpty___redArg(v_seq_5540_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5577_ = lean_array_push(v_fst_5534_, v_seq_5540_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v___x_5577_);
v___x_5579_ = v___x_5537_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_snd_5535_);
v___x_5579_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5581_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5579_);
lean_ctor_set(v___x_5528_, 0, v___x_5539_);
v___x_5581_ = v___x_5528_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
v_as_x27_5510_ = v_tail_5524_;
v_b_5511_ = v___x_5581_;
goto _start;
}
}
}
else
{
lean_object* v___x_5586_; 
lean_dec(v_seq_5540_);
if (v_isShared_5538_ == 0)
{
v___x_5586_ = v___x_5537_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_fst_5534_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_snd_5535_);
v___x_5586_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5588_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5586_);
lean_ctor_set(v___x_5528_, 0, v___x_5539_);
v___x_5588_ = v___x_5528_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5586_);
v___x_5588_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
v_as_x27_5510_ = v_tail_5524_;
v_b_5511_ = v___x_5588_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec_ref_known(v_a_5530_, 1);
lean_del_object(v___x_5537_);
lean_dec(v_snd_5535_);
lean_dec(v_fst_5534_);
lean_del_object(v___x_5528_);
lean_dec_ref(v_snd_5508_);
lean_dec_ref(v_kp_5507_);
v_a_5592_ = lean_ctor_get(v___x_5542_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5542_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5542_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5509_ == 0)
{
lean_object* v_gs_5600_; lean_object* v___x_5601_; lean_object* v___x_5603_; 
lean_del_object(v___x_5532_);
v_gs_5600_ = lean_ctor_get(v_a_5530_, 0);
lean_inc(v_gs_5600_);
lean_dec_ref_known(v_a_5530_, 1);
v___x_5601_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5535_, v_gs_5600_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 1, v___x_5601_);
v___x_5603_ = v___x_5537_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_fst_5534_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v___x_5601_);
v___x_5603_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
lean_object* v___x_5605_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5603_);
lean_ctor_set(v___x_5528_, 0, v___x_5539_);
v___x_5605_ = v___x_5528_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___x_5603_);
v___x_5605_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
v_as_x27_5510_ = v_tail_5524_;
v_b_5511_ = v___x_5605_;
goto _start;
}
}
}
else
{
lean_object* v___x_5609_; lean_object* v___x_5611_; 
lean_dec_ref(v_snd_5508_);
lean_dec_ref(v_kp_5507_);
v___x_5609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5609_, 0, v_a_5530_);
if (v_isShared_5538_ == 0)
{
v___x_5611_ = v___x_5537_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_fst_5534_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_snd_5535_);
v___x_5611_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
lean_object* v___x_5613_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5611_);
lean_ctor_set(v___x_5528_, 0, v___x_5609_);
v___x_5613_ = v___x_5528_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5609_);
lean_ctor_set(v_reuseFailAlloc_5617_, 1, v___x_5611_);
v___x_5613_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
lean_object* v___x_5615_; 
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5613_);
v___x_5615_ = v___x_5532_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v___x_5613_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
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
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
lean_dec_ref(v_b_5511_);
lean_dec_ref(v_snd_5508_);
lean_dec_ref(v_kp_5507_);
v_a_5623_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5625_ = v___x_5525_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5525_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5628_; 
if (v_isShared_5626_ == 0)
{
v___x_5628_ = v___x_5625_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5631_, lean_object* v_snd_5632_, lean_object* v_stopAtFirstFailure_5633_, lean_object* v_as_x27_5634_, lean_object* v_b_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5646_; lean_object* v_res_5647_; 
v_stopAtFirstFailure_boxed_5646_ = lean_unbox(v_stopAtFirstFailure_5633_);
v_res_5647_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5631_, v_snd_5632_, v_stopAtFirstFailure_boxed_5646_, v_as_x27_5634_, v_b_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec(v_as_x27_5634_);
return v_res_5647_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5648_, lean_object* v_c_5649_, lean_object* v___x_5650_, lean_object* v___x_5651_, uint8_t v_isRec_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
if (lean_obj_tag(v_a_5653_) == 0)
{
lean_object* v___x_5655_; 
lean_dec(v___x_5651_);
lean_dec_ref(v___x_5650_);
lean_dec_ref(v_snd_5648_);
v___x_5655_ = lean_array_to_list(v_a_5654_);
return v___x_5655_;
}
else
{
lean_object* v_toGoalState_5656_; lean_object* v_split_5657_; lean_object* v_head_5658_; lean_object* v_tail_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5719_; 
v_toGoalState_5656_ = lean_ctor_get(v_snd_5648_, 0);
lean_inc_ref(v_toGoalState_5656_);
v_split_5657_ = lean_ctor_get(v_toGoalState_5656_, 14);
lean_inc_ref(v_split_5657_);
v_head_5658_ = lean_ctor_get(v_a_5653_, 0);
v_tail_5659_ = lean_ctor_get(v_a_5653_, 1);
v_isSharedCheck_5719_ = !lean_is_exclusive(v_a_5653_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5661_ = v_a_5653_;
v_isShared_5662_ = v_isSharedCheck_5719_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_tail_5659_);
lean_inc(v_head_5658_);
lean_dec(v_a_5653_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5719_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v_nextDeclIdx_5663_; lean_object* v_enodeMap_5664_; lean_object* v_exprs_5665_; lean_object* v_parents_5666_; lean_object* v_congrTable_5667_; lean_object* v_appMap_5668_; lean_object* v_indicesFound_5669_; lean_object* v_newFacts_5670_; uint8_t v_inconsistent_5671_; lean_object* v_nextIdx_5672_; lean_object* v_newRawFacts_5673_; lean_object* v_facts_5674_; lean_object* v_extThms_5675_; lean_object* v_ematch_5676_; lean_object* v_inj_5677_; lean_object* v_clean_5678_; lean_object* v_sstates_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5717_; 
v_nextDeclIdx_5663_ = lean_ctor_get(v_toGoalState_5656_, 0);
v_enodeMap_5664_ = lean_ctor_get(v_toGoalState_5656_, 1);
v_exprs_5665_ = lean_ctor_get(v_toGoalState_5656_, 2);
v_parents_5666_ = lean_ctor_get(v_toGoalState_5656_, 3);
v_congrTable_5667_ = lean_ctor_get(v_toGoalState_5656_, 4);
v_appMap_5668_ = lean_ctor_get(v_toGoalState_5656_, 5);
v_indicesFound_5669_ = lean_ctor_get(v_toGoalState_5656_, 6);
v_newFacts_5670_ = lean_ctor_get(v_toGoalState_5656_, 7);
v_inconsistent_5671_ = lean_ctor_get_uint8(v_toGoalState_5656_, sizeof(void*)*17);
v_nextIdx_5672_ = lean_ctor_get(v_toGoalState_5656_, 8);
v_newRawFacts_5673_ = lean_ctor_get(v_toGoalState_5656_, 9);
v_facts_5674_ = lean_ctor_get(v_toGoalState_5656_, 10);
v_extThms_5675_ = lean_ctor_get(v_toGoalState_5656_, 11);
v_ematch_5676_ = lean_ctor_get(v_toGoalState_5656_, 12);
v_inj_5677_ = lean_ctor_get(v_toGoalState_5656_, 13);
v_clean_5678_ = lean_ctor_get(v_toGoalState_5656_, 15);
v_sstates_5679_ = lean_ctor_get(v_toGoalState_5656_, 16);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_toGoalState_5656_);
if (v_isSharedCheck_5717_ == 0)
{
lean_object* v_unused_5718_; 
v_unused_5718_ = lean_ctor_get(v_toGoalState_5656_, 14);
lean_dec(v_unused_5718_);
v___x_5681_ = v_toGoalState_5656_;
v_isShared_5682_ = v_isSharedCheck_5717_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_sstates_5679_);
lean_inc(v_clean_5678_);
lean_inc(v_inj_5677_);
lean_inc(v_ematch_5676_);
lean_inc(v_extThms_5675_);
lean_inc(v_facts_5674_);
lean_inc(v_newRawFacts_5673_);
lean_inc(v_nextIdx_5672_);
lean_inc(v_newFacts_5670_);
lean_inc(v_indicesFound_5669_);
lean_inc(v_appMap_5668_);
lean_inc(v_congrTable_5667_);
lean_inc(v_parents_5666_);
lean_inc(v_exprs_5665_);
lean_inc(v_enodeMap_5664_);
lean_inc(v_nextDeclIdx_5663_);
lean_dec(v_toGoalState_5656_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5717_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v_num_5683_; lean_object* v_candidates_5684_; lean_object* v_added_5685_; lean_object* v_resolved_5686_; lean_object* v_trace_5687_; lean_object* v_lookaheads_5688_; lean_object* v_argPosMap_5689_; lean_object* v_argsAt_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5716_; 
v_num_5683_ = lean_ctor_get(v_split_5657_, 0);
v_candidates_5684_ = lean_ctor_get(v_split_5657_, 1);
v_added_5685_ = lean_ctor_get(v_split_5657_, 2);
v_resolved_5686_ = lean_ctor_get(v_split_5657_, 3);
v_trace_5687_ = lean_ctor_get(v_split_5657_, 4);
v_lookaheads_5688_ = lean_ctor_get(v_split_5657_, 5);
v_argPosMap_5689_ = lean_ctor_get(v_split_5657_, 6);
v_argsAt_5690_ = lean_ctor_get(v_split_5657_, 7);
v_isSharedCheck_5716_ = !lean_is_exclusive(v_split_5657_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5692_ = v_split_5657_;
v_isShared_5693_ = v_isSharedCheck_5716_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_argsAt_5690_);
lean_inc(v_argPosMap_5689_);
lean_inc(v_lookaheads_5688_);
lean_inc(v_trace_5687_);
lean_inc(v_resolved_5686_);
lean_inc(v_added_5685_);
lean_inc(v_candidates_5684_);
lean_inc(v_num_5683_);
lean_dec(v_split_5657_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5716_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5694_; lean_object* v___y_5696_; lean_object* v___x_5714_; uint8_t v___x_5715_; 
v___x_5694_ = lean_array_get_size(v_a_5654_);
v___x_5714_ = lean_unsigned_to_nat(0u);
v___x_5715_ = lean_nat_dec_lt(v___x_5714_, v___x_5694_);
if (v___x_5715_ == 0)
{
if (v_isRec_5652_ == 0)
{
v___y_5696_ = v_num_5683_;
goto v___jp_5695_;
}
else
{
goto v___jp_5711_;
}
}
else
{
goto v___jp_5711_;
}
v___jp_5695_:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5700_; 
v___x_5697_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5649_);
lean_inc(v___x_5651_);
lean_inc_ref(v___x_5650_);
v___x_5698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5650_);
lean_ctor_set(v___x_5698_, 1, v___x_5694_);
lean_ctor_set(v___x_5698_, 2, v___x_5651_);
lean_ctor_set(v___x_5698_, 3, v___x_5697_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 1, v_trace_5687_);
lean_ctor_set(v___x_5661_, 0, v___x_5698_);
v___x_5700_ = v___x_5661_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5698_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_trace_5687_);
v___x_5700_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
lean_object* v___x_5702_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v___x_5700_);
lean_ctor_set(v___x_5692_, 0, v___y_5696_);
v___x_5702_ = v___x_5692_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___y_5696_);
lean_ctor_set(v_reuseFailAlloc_5709_, 1, v_candidates_5684_);
lean_ctor_set(v_reuseFailAlloc_5709_, 2, v_added_5685_);
lean_ctor_set(v_reuseFailAlloc_5709_, 3, v_resolved_5686_);
lean_ctor_set(v_reuseFailAlloc_5709_, 4, v___x_5700_);
lean_ctor_set(v_reuseFailAlloc_5709_, 5, v_lookaheads_5688_);
lean_ctor_set(v_reuseFailAlloc_5709_, 6, v_argPosMap_5689_);
lean_ctor_set(v_reuseFailAlloc_5709_, 7, v_argsAt_5690_);
v___x_5702_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
lean_object* v___x_5704_; 
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 14, v___x_5702_);
v___x_5704_ = v___x_5681_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_nextDeclIdx_5663_);
lean_ctor_set(v_reuseFailAlloc_5708_, 1, v_enodeMap_5664_);
lean_ctor_set(v_reuseFailAlloc_5708_, 2, v_exprs_5665_);
lean_ctor_set(v_reuseFailAlloc_5708_, 3, v_parents_5666_);
lean_ctor_set(v_reuseFailAlloc_5708_, 4, v_congrTable_5667_);
lean_ctor_set(v_reuseFailAlloc_5708_, 5, v_appMap_5668_);
lean_ctor_set(v_reuseFailAlloc_5708_, 6, v_indicesFound_5669_);
lean_ctor_set(v_reuseFailAlloc_5708_, 7, v_newFacts_5670_);
lean_ctor_set(v_reuseFailAlloc_5708_, 8, v_nextIdx_5672_);
lean_ctor_set(v_reuseFailAlloc_5708_, 9, v_newRawFacts_5673_);
lean_ctor_set(v_reuseFailAlloc_5708_, 10, v_facts_5674_);
lean_ctor_set(v_reuseFailAlloc_5708_, 11, v_extThms_5675_);
lean_ctor_set(v_reuseFailAlloc_5708_, 12, v_ematch_5676_);
lean_ctor_set(v_reuseFailAlloc_5708_, 13, v_inj_5677_);
lean_ctor_set(v_reuseFailAlloc_5708_, 14, v___x_5702_);
lean_ctor_set(v_reuseFailAlloc_5708_, 15, v_clean_5678_);
lean_ctor_set(v_reuseFailAlloc_5708_, 16, v_sstates_5679_);
lean_ctor_set_uint8(v_reuseFailAlloc_5708_, sizeof(void*)*17, v_inconsistent_5671_);
v___x_5704_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v_head_5658_);
v___x_5706_ = lean_array_push(v_a_5654_, v___x_5705_);
v_a_5653_ = v_tail_5659_;
v_a_5654_ = v___x_5706_;
goto _start;
}
}
}
}
v___jp_5711_:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5712_ = lean_unsigned_to_nat(1u);
v___x_5713_ = lean_nat_add(v_num_5683_, v___x_5712_);
lean_dec(v_num_5683_);
v___y_5696_ = v___x_5713_;
goto v___jp_5695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5720_, lean_object* v_c_5721_, lean_object* v___x_5722_, lean_object* v___x_5723_, lean_object* v_isRec_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_){
_start:
{
uint8_t v_isRec_boxed_5727_; lean_object* v_res_5728_; 
v_isRec_boxed_5727_ = lean_unbox(v_isRec_5724_);
v_res_5728_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5720_, v_c_5721_, v___x_5722_, v___x_5723_, v_isRec_boxed_5727_, v_a_5725_, v_a_5726_);
lean_dec_ref(v_c_5721_);
return v_res_5728_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5740_ = lean_box(0);
v___x_5741_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5742_ = l_Lean_mkConst(v___x_5741_, v___x_5740_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5743_, lean_object* v_numCases_5744_, uint8_t v_isRec_5745_, uint8_t v_stopAtFirstFailure_5746_, uint8_t v_compress_5747_, lean_object* v_candidates_x3f_5748_, lean_object* v_goal_5749_, lean_object* v_kp_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_){
_start:
{
lean_object* v___x_5761_; 
v___x_5761_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5752_);
if (lean_obj_tag(v___x_5761_) == 0)
{
lean_object* v_a_5762_; lean_object* v___x_5763_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5762_);
lean_dec_ref_known(v___x_5761_, 1);
lean_inc_ref(v_goal_5749_);
v___x_5763_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5749_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_a_5764_; uint8_t v_trace_5765_; lean_object* v_mvarId_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___f_5769_; lean_object* v___x_5770_; lean_object* v___f_5771_; lean_object* v___x_5772_; 
v_a_5764_ = lean_ctor_get(v___x_5763_, 0);
lean_inc_n(v_a_5764_, 2);
lean_dec_ref_known(v___x_5763_, 1);
v_trace_5765_ = lean_ctor_get_uint8(v_a_5762_, sizeof(void*)*14);
lean_dec(v_a_5762_);
v_mvarId_5766_ = lean_ctor_get(v_goal_5749_, 1);
lean_inc(v_mvarId_5766_);
v___x_5767_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5743_);
v___x_5768_ = lean_box(v_isRec_5745_);
lean_inc_ref_n(v_c_5743_, 2);
lean_inc_ref(v___x_5767_);
v___f_5769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5769_, 0, v___x_5767_);
lean_closure_set(v___f_5769_, 1, v_c_5743_);
lean_closure_set(v___f_5769_, 2, v_a_5764_);
lean_closure_set(v___f_5769_, 3, v_numCases_5744_);
lean_closure_set(v___f_5769_, 4, v___x_5768_);
v___x_5770_ = lean_box(v_trace_5765_);
v___f_5771_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5771_, 0, v_goal_5749_);
lean_closure_set(v___f_5771_, 1, v___x_5770_);
lean_closure_set(v___f_5771_, 2, v___f_5769_);
lean_closure_set(v___f_5771_, 3, v_c_5743_);
lean_closure_set(v___f_5771_, 4, v_candidates_x3f_5748_);
v___x_5772_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5766_, v___f_5771_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
if (lean_obj_tag(v___x_5772_) == 0)
{
lean_object* v_a_5773_; lean_object* v_fst_5774_; lean_object* v_snd_5775_; lean_object* v_fst_5776_; lean_object* v_snd_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; 
v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
lean_inc(v_a_5773_);
lean_dec_ref_known(v___x_5772_, 1);
v_fst_5774_ = lean_ctor_get(v_a_5773_, 0);
lean_inc(v_fst_5774_);
v_snd_5775_ = lean_ctor_get(v_a_5773_, 1);
lean_inc_n(v_snd_5775_, 3);
lean_dec(v_a_5773_);
v_fst_5776_ = lean_ctor_get(v_fst_5774_, 0);
lean_inc(v_fst_5776_);
v_snd_5777_ = lean_ctor_get(v_fst_5774_, 1);
lean_inc(v_snd_5777_);
lean_dec(v_fst_5774_);
v___x_5778_ = l_List_lengthTR___redArg(v_fst_5776_);
v___x_5779_ = lean_unsigned_to_nat(0u);
v___x_5780_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5781_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5775_, v_c_5743_, v___x_5767_, v___x_5778_, v_isRec_5745_, v_fst_5776_, v___x_5780_);
lean_dec_ref(v_c_5743_);
v___x_5782_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5783_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5750_, v_snd_5775_, v_stopAtFirstFailure_5746_, v___x_5781_, v___x_5782_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
lean_dec(v___x_5781_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5871_; 
v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5786_ = v___x_5783_;
v_isShared_5787_ = v_isSharedCheck_5871_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5783_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5871_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v_fst_5788_; 
v_fst_5788_ = lean_ctor_get(v_a_5784_, 0);
if (lean_obj_tag(v_fst_5788_) == 0)
{
lean_object* v_snd_5789_; lean_object* v_mvarId_5790_; lean_object* v___x_5791_; 
lean_del_object(v___x_5786_);
v_snd_5789_ = lean_ctor_get(v_a_5784_, 1);
lean_inc(v_snd_5789_);
lean_dec(v_a_5784_);
v_mvarId_5790_ = lean_ctor_get(v_snd_5775_, 1);
lean_inc_n(v_mvarId_5790_, 2);
lean_dec(v_snd_5775_);
v___x_5791_ = l_Lean_MVarId_getType(v_mvarId_5790_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5858_; 
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5858_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5791_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5858_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v_fst_5796_; lean_object* v_snd_5797_; lean_object* v___y_5799_; lean_object* v___y_5800_; uint8_t v___x_5847_; 
v_fst_5796_ = lean_ctor_get(v_snd_5789_, 0);
lean_inc(v_fst_5796_);
v_snd_5797_ = lean_ctor_get(v_snd_5789_, 1);
lean_inc(v_snd_5797_);
lean_dec(v_snd_5789_);
v___x_5847_ = l_Lean_Expr_isFalse(v_a_5792_);
if (v___x_5847_ == 0)
{
lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v_a_5850_; lean_object* v___x_5851_; 
v___x_5848_ = l_Lean_mkMVar(v_a_5764_);
v___x_5849_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5848_, v_a_5757_);
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref(v___x_5849_);
v___x_5851_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5790_, v_a_5850_, v_a_5757_);
lean_dec_ref(v___x_5851_);
v___y_5799_ = v_a_5758_;
v___y_5800_ = v_a_5759_;
goto v___jp_5798_;
}
else
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v_a_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; 
v___x_5852_ = l_Lean_mkMVar(v_a_5764_);
v___x_5853_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5852_, v_a_5757_);
v_a_5854_ = lean_ctor_get(v___x_5853_, 0);
lean_inc(v_a_5854_);
lean_dec_ref(v___x_5853_);
v___x_5855_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5856_ = l_Lean_Meta_mkExpectedPropHint(v_a_5854_, v___x_5855_);
v___x_5857_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5790_, v___x_5856_, v_a_5757_);
lean_dec_ref(v___x_5857_);
v___y_5799_ = v_a_5758_;
v___y_5800_ = v_a_5759_;
goto v___jp_5798_;
}
v___jp_5798_:
{
lean_object* v___x_5801_; uint8_t v___x_5802_; 
v___x_5801_ = lean_array_get_size(v_snd_5797_);
v___x_5802_ = lean_nat_dec_eq(v___x_5801_, v___x_5779_);
if (v___x_5802_ == 0)
{
lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5806_; 
lean_dec(v_fst_5796_);
lean_dec(v_snd_5777_);
v___x_5803_ = lean_array_to_list(v_snd_5797_);
v___x_5804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5803_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 0, v___x_5804_);
v___x_5806_ = v___x_5794_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5804_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
return v___x_5806_;
}
}
else
{
lean_dec(v_snd_5797_);
if (lean_obj_tag(v_snd_5777_) == 1)
{
lean_object* v_val_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5842_; 
lean_del_object(v___x_5794_);
v_val_5808_ = lean_ctor_get(v_snd_5777_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v_snd_5777_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5810_ = v_snd_5777_;
v_isShared_5811_ = v_isSharedCheck_5842_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_val_5808_);
lean_dec(v_snd_5777_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5842_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v___x_5812_; 
v___x_5812_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5808_, v___y_5799_);
lean_dec(v_val_5808_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; lean_object* v___x_5814_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_a_5813_);
lean_dec_ref_known(v___x_5812_, 1);
v___x_5814_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5813_, v_fst_5796_, v_compress_5747_, v___y_5799_, v___y_5800_);
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_object* v_a_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5825_; 
v_a_5815_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5817_ = v___x_5814_;
v_isShared_5818_ = v_isSharedCheck_5825_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_a_5815_);
lean_dec(v___x_5814_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5825_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5820_; 
if (v_isShared_5811_ == 0)
{
lean_ctor_set_tag(v___x_5810_, 0);
lean_ctor_set(v___x_5810_, 0, v_a_5815_);
v___x_5820_ = v___x_5810_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_a_5815_);
v___x_5820_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5822_; 
if (v_isShared_5818_ == 0)
{
lean_ctor_set(v___x_5817_, 0, v___x_5820_);
v___x_5822_ = v___x_5817_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v___x_5820_);
v___x_5822_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
return v___x_5822_;
}
}
}
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5833_; 
lean_del_object(v___x_5810_);
v_a_5826_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5828_ = v___x_5814_;
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5814_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5831_; 
if (v_isShared_5829_ == 0)
{
v___x_5831_ = v___x_5828_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
else
{
lean_object* v_a_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5841_; 
lean_del_object(v___x_5810_);
lean_dec(v_fst_5796_);
v_a_5834_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5841_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5836_ = v___x_5812_;
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_a_5834_);
lean_dec(v___x_5812_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5839_; 
if (v_isShared_5837_ == 0)
{
v___x_5839_ = v___x_5836_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v_a_5834_);
v___x_5839_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
return v___x_5839_;
}
}
}
}
}
else
{
lean_object* v___x_5843_; lean_object* v___x_5845_; 
lean_dec(v_fst_5796_);
lean_dec(v_snd_5777_);
v___x_5843_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 0, v___x_5843_);
v___x_5845_ = v___x_5794_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5843_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
}
}
else
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5866_; 
lean_dec(v_mvarId_5790_);
lean_dec(v_snd_5789_);
lean_dec(v_snd_5777_);
lean_dec(v_a_5764_);
v_a_5859_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5791_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5791_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
}
else
{
lean_object* v_val_5867_; lean_object* v___x_5869_; 
lean_inc_ref(v_fst_5788_);
lean_dec(v_a_5784_);
lean_dec(v_snd_5777_);
lean_dec(v_snd_5775_);
lean_dec(v_a_5764_);
v_val_5867_ = lean_ctor_get(v_fst_5788_, 0);
lean_inc(v_val_5867_);
lean_dec_ref_known(v_fst_5788_, 1);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 0, v_val_5867_);
v___x_5869_ = v___x_5786_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_val_5867_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
else
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5879_; 
lean_dec(v_snd_5777_);
lean_dec(v_snd_5775_);
lean_dec(v_a_5764_);
v_a_5872_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5874_ = v___x_5783_;
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5783_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5877_; 
if (v_isShared_5875_ == 0)
{
v___x_5877_ = v___x_5874_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
v___x_5877_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
return v___x_5877_;
}
}
}
}
else
{
lean_object* v_a_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5887_; 
lean_dec_ref(v___x_5767_);
lean_dec(v_a_5764_);
lean_dec_ref(v_kp_5750_);
lean_dec_ref(v_c_5743_);
v_a_5880_ = lean_ctor_get(v___x_5772_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v___x_5772_);
if (v_isSharedCheck_5887_ == 0)
{
v___x_5882_ = v___x_5772_;
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_a_5880_);
lean_dec(v___x_5772_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v___x_5885_; 
if (v_isShared_5883_ == 0)
{
v___x_5885_ = v___x_5882_;
goto v_reusejp_5884_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
v___x_5885_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5884_;
}
v_reusejp_5884_:
{
return v___x_5885_;
}
}
}
}
else
{
lean_object* v_a_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5895_; 
lean_dec(v_a_5762_);
lean_dec_ref(v_kp_5750_);
lean_dec_ref(v_goal_5749_);
lean_dec(v_candidates_x3f_5748_);
lean_dec(v_numCases_5744_);
lean_dec_ref(v_c_5743_);
v_a_5888_ = lean_ctor_get(v___x_5763_, 0);
v_isSharedCheck_5895_ = !lean_is_exclusive(v___x_5763_);
if (v_isSharedCheck_5895_ == 0)
{
v___x_5890_ = v___x_5763_;
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_a_5888_);
lean_dec(v___x_5763_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v___x_5893_; 
if (v_isShared_5891_ == 0)
{
v___x_5893_ = v___x_5890_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
v___x_5893_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
return v___x_5893_;
}
}
}
}
else
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5903_; 
lean_dec_ref(v_kp_5750_);
lean_dec_ref(v_goal_5749_);
lean_dec(v_candidates_x3f_5748_);
lean_dec(v_numCases_5744_);
lean_dec_ref(v_c_5743_);
v_a_5896_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5898_ = v___x_5761_;
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5761_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5901_; 
if (v_isShared_5899_ == 0)
{
v___x_5901_ = v___x_5898_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
v___x_5901_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
return v___x_5901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5904_ = _args[0];
lean_object* v_numCases_5905_ = _args[1];
lean_object* v_isRec_5906_ = _args[2];
lean_object* v_stopAtFirstFailure_5907_ = _args[3];
lean_object* v_compress_5908_ = _args[4];
lean_object* v_candidates_x3f_5909_ = _args[5];
lean_object* v_goal_5910_ = _args[6];
lean_object* v_kp_5911_ = _args[7];
lean_object* v_a_5912_ = _args[8];
lean_object* v_a_5913_ = _args[9];
lean_object* v_a_5914_ = _args[10];
lean_object* v_a_5915_ = _args[11];
lean_object* v_a_5916_ = _args[12];
lean_object* v_a_5917_ = _args[13];
lean_object* v_a_5918_ = _args[14];
lean_object* v_a_5919_ = _args[15];
lean_object* v_a_5920_ = _args[16];
lean_object* v_a_5921_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5922_; uint8_t v_stopAtFirstFailure_boxed_5923_; uint8_t v_compress_boxed_5924_; lean_object* v_res_5925_; 
v_isRec_boxed_5922_ = lean_unbox(v_isRec_5906_);
v_stopAtFirstFailure_boxed_5923_ = lean_unbox(v_stopAtFirstFailure_5907_);
v_compress_boxed_5924_ = lean_unbox(v_compress_5908_);
v_res_5925_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5904_, v_numCases_5905_, v_isRec_boxed_5922_, v_stopAtFirstFailure_boxed_5923_, v_compress_boxed_5924_, v_candidates_x3f_5909_, v_goal_5910_, v_kp_5911_, v_a_5912_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_);
lean_dec(v_a_5920_);
lean_dec_ref(v_a_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_a_5917_);
lean_dec(v_a_5916_);
lean_dec_ref(v_a_5915_);
lean_dec(v_a_5914_);
lean_dec_ref(v_a_5913_);
lean_dec(v_a_5912_);
return v_res_5925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5926_, lean_object* v_numCases_5927_, uint8_t v_isRec_5928_, uint8_t v_stopAtFirstFailure_5929_, uint8_t v_compress_5930_, lean_object* v_candidates_x3f_5931_, lean_object* v_goal_5932_, lean_object* v_x_5933_, lean_object* v_kp_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_){
_start:
{
lean_object* v___x_5945_; 
v___x_5945_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5926_, v_numCases_5927_, v_isRec_5928_, v_stopAtFirstFailure_5929_, v_compress_5930_, v_candidates_x3f_5931_, v_goal_5932_, v_kp_5934_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5946_ = _args[0];
lean_object* v_numCases_5947_ = _args[1];
lean_object* v_isRec_5948_ = _args[2];
lean_object* v_stopAtFirstFailure_5949_ = _args[3];
lean_object* v_compress_5950_ = _args[4];
lean_object* v_candidates_x3f_5951_ = _args[5];
lean_object* v_goal_5952_ = _args[6];
lean_object* v_x_5953_ = _args[7];
lean_object* v_kp_5954_ = _args[8];
lean_object* v_a_5955_ = _args[9];
lean_object* v_a_5956_ = _args[10];
lean_object* v_a_5957_ = _args[11];
lean_object* v_a_5958_ = _args[12];
lean_object* v_a_5959_ = _args[13];
lean_object* v_a_5960_ = _args[14];
lean_object* v_a_5961_ = _args[15];
lean_object* v_a_5962_ = _args[16];
lean_object* v_a_5963_ = _args[17];
lean_object* v_a_5964_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5965_; uint8_t v_stopAtFirstFailure_boxed_5966_; uint8_t v_compress_boxed_5967_; lean_object* v_res_5968_; 
v_isRec_boxed_5965_ = lean_unbox(v_isRec_5948_);
v_stopAtFirstFailure_boxed_5966_ = lean_unbox(v_stopAtFirstFailure_5949_);
v_compress_boxed_5967_ = lean_unbox(v_compress_5950_);
v_res_5968_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5946_, v_numCases_5947_, v_isRec_boxed_5965_, v_stopAtFirstFailure_boxed_5966_, v_compress_boxed_5967_, v_candidates_x3f_5951_, v_goal_5952_, v_x_5953_, v_kp_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_, v_a_5962_, v_a_5963_);
lean_dec(v_a_5963_);
lean_dec_ref(v_a_5962_);
lean_dec(v_a_5961_);
lean_dec_ref(v_a_5960_);
lean_dec(v_a_5959_);
lean_dec_ref(v_a_5958_);
lean_dec(v_a_5957_);
lean_dec_ref(v_a_5956_);
lean_dec(v_a_5955_);
lean_dec_ref(v_x_5953_);
return v_res_5968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5969_, lean_object* v_snd_5970_, uint8_t v_stopAtFirstFailure_5971_, lean_object* v_as_5972_, lean_object* v_as_x27_5973_, lean_object* v_b_5974_, lean_object* v_a_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_){
_start:
{
lean_object* v___x_5986_; 
v___x_5986_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5969_, v_snd_5970_, v_stopAtFirstFailure_5971_, v_as_x27_5973_, v_b_5974_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
return v___x_5986_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5987_ = _args[0];
lean_object* v_snd_5988_ = _args[1];
lean_object* v_stopAtFirstFailure_5989_ = _args[2];
lean_object* v_as_5990_ = _args[3];
lean_object* v_as_x27_5991_ = _args[4];
lean_object* v_b_5992_ = _args[5];
lean_object* v_a_5993_ = _args[6];
lean_object* v___y_5994_ = _args[7];
lean_object* v___y_5995_ = _args[8];
lean_object* v___y_5996_ = _args[9];
lean_object* v___y_5997_ = _args[10];
lean_object* v___y_5998_ = _args[11];
lean_object* v___y_5999_ = _args[12];
lean_object* v___y_6000_ = _args[13];
lean_object* v___y_6001_ = _args[14];
lean_object* v___y_6002_ = _args[15];
lean_object* v___y_6003_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6004_; lean_object* v_res_6005_; 
v_stopAtFirstFailure_boxed_6004_ = lean_unbox(v_stopAtFirstFailure_5989_);
v_res_6005_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5987_, v_snd_5988_, v_stopAtFirstFailure_boxed_6004_, v_as_5990_, v_as_x27_5991_, v_b_5992_, v_a_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
lean_dec(v___y_6002_);
lean_dec_ref(v___y_6001_);
lean_dec(v___y_6000_);
lean_dec_ref(v___y_5999_);
lean_dec(v___y_5998_);
lean_dec_ref(v___y_5997_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec(v___y_5994_);
lean_dec(v_as_x27_5991_);
lean_dec(v_as_5990_);
return v_res_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6006_, lean_object* v_val_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_){
_start:
{
lean_object* v___x_6018_; 
v___x_6018_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6006_, v_val_6007_, v___y_6014_);
return v___x_6018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6019_, lean_object* v_val_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6019_, v_val_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
lean_dec(v___y_6029_);
lean_dec_ref(v___y_6028_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec_ref(v___y_6022_);
lean_dec(v___y_6021_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6032_, lean_object* v_x_6033_, lean_object* v_x_6034_, lean_object* v_x_6035_){
_start:
{
lean_object* v___x_6036_; 
v___x_6036_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6033_, v_x_6034_, v_x_6035_);
return v___x_6036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6037_, lean_object* v_x_6038_, size_t v_x_6039_, size_t v_x_6040_, lean_object* v_x_6041_, lean_object* v_x_6042_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6038_, v_x_6039_, v_x_6040_, v_x_6041_, v_x_6042_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6044_, lean_object* v_x_6045_, lean_object* v_x_6046_, lean_object* v_x_6047_, lean_object* v_x_6048_, lean_object* v_x_6049_){
_start:
{
size_t v_x_67849__boxed_6050_; size_t v_x_67850__boxed_6051_; lean_object* v_res_6052_; 
v_x_67849__boxed_6050_ = lean_unbox_usize(v_x_6046_);
lean_dec(v_x_6046_);
v_x_67850__boxed_6051_ = lean_unbox_usize(v_x_6047_);
lean_dec(v_x_6047_);
v_res_6052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6044_, v_x_6045_, v_x_67849__boxed_6050_, v_x_67850__boxed_6051_, v_x_6048_, v_x_6049_);
return v_res_6052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6053_, lean_object* v_n_6054_, lean_object* v_k_6055_, lean_object* v_v_6056_){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6054_, v_k_6055_, v_v_6056_);
return v___x_6057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6058_, size_t v_depth_6059_, lean_object* v_keys_6060_, lean_object* v_vals_6061_, lean_object* v_heq_6062_, lean_object* v_i_6063_, lean_object* v_entries_6064_){
_start:
{
lean_object* v___x_6065_; 
v___x_6065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6059_, v_keys_6060_, v_vals_6061_, v_i_6063_, v_entries_6064_);
return v___x_6065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6066_, lean_object* v_depth_6067_, lean_object* v_keys_6068_, lean_object* v_vals_6069_, lean_object* v_heq_6070_, lean_object* v_i_6071_, lean_object* v_entries_6072_){
_start:
{
size_t v_depth_boxed_6073_; lean_object* v_res_6074_; 
v_depth_boxed_6073_ = lean_unbox_usize(v_depth_6067_);
lean_dec(v_depth_6067_);
v_res_6074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6066_, v_depth_boxed_6073_, v_keys_6068_, v_vals_6069_, v_heq_6070_, v_i_6071_, v_entries_6072_);
lean_dec_ref(v_vals_6069_);
lean_dec_ref(v_keys_6068_);
return v_res_6074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6075_, lean_object* v_x_6076_, lean_object* v_x_6077_, lean_object* v_x_6078_, lean_object* v_x_6079_){
_start:
{
lean_object* v___x_6080_; 
v___x_6080_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6076_, v_x_6077_, v_x_6078_, v_x_6079_);
return v___x_6080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = lean_st_mk_ref(v_goal_6081_);
v___x_6093_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6092_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
if (lean_obj_tag(v___x_6093_) == 0)
{
lean_object* v_a_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6103_; 
v_a_6094_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6096_ = v___x_6093_;
v_isShared_6097_ = v_isSharedCheck_6103_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_a_6094_);
lean_dec(v___x_6093_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6103_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6101_; 
v___x_6098_ = lean_st_ref_get(v___x_6092_);
lean_dec(v___x_6092_);
v___x_6099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6099_, 0, v_a_6094_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 0, v___x_6099_);
v___x_6101_ = v___x_6096_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v___x_6099_);
v___x_6101_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
return v___x_6101_;
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
lean_dec(v___x_6092_);
v_a_6104_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6093_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6093_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v_res_6123_; 
v_res_6123_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec_ref(v___y_6118_);
lean_dec(v___y_6117_);
lean_dec_ref(v___y_6116_);
lean_dec(v___y_6115_);
lean_dec_ref(v___y_6114_);
lean_dec(v___y_6113_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_){
_start:
{
lean_object* v___x_6137_; 
v___x_6137_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6124_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec(v___y_6143_);
lean_dec_ref(v___y_6142_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6139_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6152_, lean_object* v___f_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v___x_6167_; lean_object* v___x_6168_; 
v___x_6167_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6167_, 0, v___y_6152_);
v___x_6168_ = l_Lean_Meta_Grind_Action_andThen(v___x_6167_, v___f_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
return v___x_6168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6169_, lean_object* v___f_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
lean_object* v_res_6184_; 
v_res_6184_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6169_, v___f_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
lean_dec(v___y_6176_);
lean_dec_ref(v___y_6175_);
lean_dec(v___y_6174_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6186_, uint8_t v_compress_6187_, lean_object* v_goal_6188_, lean_object* v_kna_6189_, lean_object* v_kp_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_, lean_object* v_a_6193_, lean_object* v_a_6194_, lean_object* v_a_6195_, lean_object* v_a_6196_, lean_object* v_a_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_){
_start:
{
lean_object* v_toGoalState_6201_; lean_object* v_mvarId_6202_; lean_object* v___f_6203_; lean_object* v___x_6204_; 
v_toGoalState_6201_ = lean_ctor_get(v_goal_6188_, 0);
lean_inc_ref(v_toGoalState_6201_);
v_mvarId_6202_ = lean_ctor_get(v_goal_6188_, 1);
lean_inc(v_mvarId_6202_);
v___f_6203_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_6203_, 0, v_goal_6188_);
v___x_6204_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6202_, v___f_6203_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_);
if (lean_obj_tag(v___x_6204_) == 0)
{
lean_object* v_a_6205_; lean_object* v_fst_6206_; 
v_a_6205_ = lean_ctor_get(v___x_6204_, 0);
lean_inc(v_a_6205_);
lean_dec_ref_known(v___x_6204_, 1);
v_fst_6206_ = lean_ctor_get(v_a_6205_, 0);
if (lean_obj_tag(v_fst_6206_) == 1)
{
lean_object* v_split_6207_; lean_object* v_snd_6208_; lean_object* v_c_6209_; lean_object* v_numCases_6210_; uint8_t v_isRec_6211_; lean_object* v_candidates_6212_; lean_object* v___f_6213_; lean_object* v___y_6215_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; uint8_t v___x_6228_; 
lean_inc_ref(v_fst_6206_);
v_split_6207_ = lean_ctor_get(v_toGoalState_6201_, 14);
lean_inc_ref(v_split_6207_);
lean_dec_ref(v_toGoalState_6201_);
v_snd_6208_ = lean_ctor_get(v_a_6205_, 1);
lean_inc(v_snd_6208_);
lean_dec(v_a_6205_);
v_c_6209_ = lean_ctor_get(v_fst_6206_, 0);
lean_inc_ref(v_c_6209_);
v_numCases_6210_ = lean_ctor_get(v_fst_6206_, 1);
lean_inc(v_numCases_6210_);
v_isRec_6211_ = lean_ctor_get_uint8(v_fst_6206_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6206_, 2);
v_candidates_6212_ = lean_ctor_get(v_split_6207_, 1);
lean_inc(v_candidates_6212_);
lean_dec_ref(v_split_6207_);
v___f_6213_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_6223_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6209_);
v___x_6224_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6208_, v___x_6223_);
lean_dec_ref(v___x_6223_);
v___x_6225_ = lean_unsigned_to_nat(1u);
v___x_6228_ = lean_nat_dec_lt(v___x_6225_, v_numCases_6210_);
if (v___x_6228_ == 0)
{
if (v_isRec_6211_ == 0)
{
v___y_6215_ = v___x_6224_;
goto v___jp_6214_;
}
else
{
goto v___jp_6226_;
}
}
else
{
goto v___jp_6226_;
}
v___jp_6214_:
{
lean_object* v___f_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; 
v___f_6216_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6216_, 0, v___y_6215_);
lean_closure_set(v___f_6216_, 1, v___f_6213_);
v___x_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6217_, 0, v_candidates_6212_);
v___x_6218_ = lean_box(v_isRec_6211_);
v___x_6219_ = lean_box(v_stopAtFirstFailure_6186_);
v___x_6220_ = lean_box(v_compress_6187_);
v___x_6221_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6221_, 0, v_c_6209_);
lean_closure_set(v___x_6221_, 1, v_numCases_6210_);
lean_closure_set(v___x_6221_, 2, v___x_6218_);
lean_closure_set(v___x_6221_, 3, v___x_6219_);
lean_closure_set(v___x_6221_, 4, v___x_6220_);
lean_closure_set(v___x_6221_, 5, v___x_6217_);
v___x_6222_ = l_Lean_Meta_Grind_Action_andThen(v___x_6221_, v___f_6216_, v_snd_6208_, v_kna_6189_, v_kp_6190_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_);
return v___x_6222_;
}
v___jp_6226_:
{
lean_object* v___x_6227_; 
v___x_6227_ = lean_nat_add(v___x_6224_, v___x_6225_);
lean_dec(v___x_6224_);
v___y_6215_ = v___x_6227_;
goto v___jp_6214_;
}
}
else
{
lean_object* v_snd_6229_; lean_object* v___x_6230_; 
lean_dec_ref(v_toGoalState_6201_);
lean_dec_ref(v_kp_6190_);
v_snd_6229_ = lean_ctor_get(v_a_6205_, 1);
lean_inc(v_snd_6229_);
lean_dec(v_a_6205_);
lean_inc(v_a_6199_);
lean_inc_ref(v_a_6198_);
lean_inc(v_a_6197_);
lean_inc_ref(v_a_6196_);
lean_inc(v_a_6195_);
lean_inc_ref(v_a_6194_);
lean_inc(v_a_6193_);
lean_inc_ref(v_a_6192_);
lean_inc(v_a_6191_);
v___x_6230_ = lean_apply_11(v_kna_6189_, v_snd_6229_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, lean_box(0));
return v___x_6230_;
}
}
else
{
lean_object* v_a_6231_; lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6238_; 
lean_dec_ref(v_toGoalState_6201_);
lean_dec_ref(v_kp_6190_);
lean_dec_ref(v_kna_6189_);
v_a_6231_ = lean_ctor_get(v___x_6204_, 0);
v_isSharedCheck_6238_ = !lean_is_exclusive(v___x_6204_);
if (v_isSharedCheck_6238_ == 0)
{
v___x_6233_ = v___x_6204_;
v_isShared_6234_ = v_isSharedCheck_6238_;
goto v_resetjp_6232_;
}
else
{
lean_inc(v_a_6231_);
lean_dec(v___x_6204_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6239_, lean_object* v_compress_6240_, lean_object* v_goal_6241_, lean_object* v_kna_6242_, lean_object* v_kp_6243_, lean_object* v_a_6244_, lean_object* v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_, lean_object* v_a_6248_, lean_object* v_a_6249_, lean_object* v_a_6250_, lean_object* v_a_6251_, lean_object* v_a_6252_, lean_object* v_a_6253_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6254_; uint8_t v_compress_boxed_6255_; lean_object* v_res_6256_; 
v_stopAtFirstFailure_boxed_6254_ = lean_unbox(v_stopAtFirstFailure_6239_);
v_compress_boxed_6255_ = lean_unbox(v_compress_6240_);
v_res_6256_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6254_, v_compress_boxed_6255_, v_goal_6241_, v_kna_6242_, v_kp_6243_, v_a_6244_, v_a_6245_, v_a_6246_, v_a_6247_, v_a_6248_, v_a_6249_, v_a_6250_, v_a_6251_, v_a_6252_);
lean_dec(v_a_6252_);
lean_dec_ref(v_a_6251_);
lean_dec(v_a_6250_);
lean_dec_ref(v_a_6249_);
lean_dec(v_a_6248_);
lean_dec_ref(v_a_6247_);
lean_dec(v_a_6246_);
lean_dec_ref(v_a_6245_);
lean_dec(v_a_6244_);
return v_res_6256_;
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
