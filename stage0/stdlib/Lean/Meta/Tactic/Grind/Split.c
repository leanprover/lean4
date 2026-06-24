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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
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
lean_dec_ref_known(v_x_715_, 2);
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
lean_dec_ref_known(v___y_775_, 1);
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
lean_dec_ref_known(v___x_1262_, 14);
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
v___y_1641_ = v___y_1777_;
v___y_1642_ = v___y_1775_;
v___y_1643_ = v___y_1772_;
v___y_1644_ = v___y_1774_;
v___y_1645_ = v___y_1771_;
v___y_1646_ = v___y_1778_;
v___y_1647_ = v___y_1776_;
v___y_1648_ = v___y_1773_;
v___y_1649_ = v___y_1780_;
v___y_1650_ = v___y_1779_;
v___y_1651_ = v___x_1782_;
goto v___jp_1640_;
}
else
{
v___y_1641_ = v___y_1777_;
v___y_1642_ = v___y_1775_;
v___y_1643_ = v___y_1772_;
v___y_1644_ = v___y_1774_;
v___y_1645_ = v___y_1771_;
v___y_1646_ = v___y_1778_;
v___y_1647_ = v___y_1776_;
v___y_1648_ = v___y_1773_;
v___y_1649_ = v___y_1780_;
v___y_1650_ = v___y_1779_;
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
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Lean_Meta_whnfD(v_a_1547_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_n(v_a_1549_, 2);
lean_dec_ref_known(v___x_1548_, 1);
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
lean_dec_ref_known(v___x_1557_, 2);
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
lean_dec_ref_known(v___x_1556_, 2);
v_val_1564_ = lean_ctor_get(v_a_1560_, 0);
lean_inc_ref(v_val_1564_);
lean_dec_ref_known(v_a_1560_, 1);
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
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
if (v___x_1574_ == 0)
{
lean_dec_ref_known(v___x_1556_, 2);
goto v___jp_1528_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Meta_Sym_reportIssue(v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_dec_ref_known(v___x_1575_, 1);
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
lean_dec_ref_known(v___x_1556_, 2);
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
lean_dec_ref_known(v___x_1556_, 2);
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
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = lean_unbox(v_a_1602_);
lean_dec(v_a_1602_);
if (v___x_1603_ == 0)
{
lean_dec_ref_known(v___x_1556_, 2);
goto v___jp_1525_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Sym_reportIssue(v___x_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec_ref_known(v___x_1604_, 1);
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
lean_dec_ref_known(v___x_1556_, 2);
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
v___x_1652_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1513_, v___y_1645_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = lean_unbox(v_a_1653_);
lean_dec(v_a_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_inc_ref(v_e_1513_);
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1513_, v___y_1645_, v___y_1643_, v___y_1648_, v___y_1644_, v___y_1642_, v___y_1647_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
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
v___x_1661_ = lean_st_ref_get(v___y_1649_);
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
lean_dec_ref_known(v___x_1663_, 1);
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
lean_dec_ref_known(v___x_1672_, 2);
v___x_1674_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1673_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
if (lean_obj_tag(v_a_1675_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v_a_1675_, 1);
lean_inc_ref(v_e_1513_);
v___x_1677_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1513_, v___y_1645_, v___y_1642_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
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
v___y_1533_ = v___y_1645_;
v___y_1534_ = v___y_1643_;
v___y_1535_ = v___y_1648_;
v___y_1536_ = v___y_1644_;
v___y_1537_ = v___y_1642_;
v___y_1538_ = v___y_1647_;
v___y_1539_ = v___y_1641_;
v___y_1540_ = v___y_1646_;
v___y_1541_ = v___y_1650_;
v___y_1542_ = v___y_1649_;
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
v___y_1533_ = v___y_1645_;
v___y_1534_ = v___y_1643_;
v___y_1535_ = v___y_1648_;
v___y_1536_ = v___y_1644_;
v___y_1537_ = v___y_1642_;
v___y_1538_ = v___y_1647_;
v___y_1539_ = v___y_1641_;
v___y_1540_ = v___y_1646_;
v___y_1541_ = v___y_1650_;
v___y_1542_ = v___y_1649_;
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
v___y_1533_ = v___y_1645_;
v___y_1534_ = v___y_1643_;
v___y_1535_ = v___y_1648_;
v___y_1536_ = v___y_1644_;
v___y_1537_ = v___y_1642_;
v___y_1538_ = v___y_1647_;
v___y_1539_ = v___y_1641_;
v___y_1540_ = v___y_1646_;
v___y_1541_ = v___y_1650_;
v___y_1542_ = v___y_1649_;
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
v_options_1724_ = lean_ctor_get(v___y_1650_, 2);
v_hasTrace_1725_ = lean_ctor_get_uint8(v_options_1724_, sizeof(void*)*1);
if (v_hasTrace_1725_ == 0)
{
lean_dec_ref(v_e_1513_);
goto v___jp_1637_;
}
else
{
lean_object* v_inheritedTraceOptions_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_inheritedTraceOptions_1726_ = lean_ctor_get(v___y_1650_, 13);
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
v___x_1730_ = l_Lean_Meta_Grind_updateLastTag(v___y_1645_, v___y_1643_, v___y_1648_, v___y_1644_, v___y_1642_, v___y_1647_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1730_, 1);
v___x_1731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1732_ = l_Lean_MessageData_ofExpr(v_e_1513_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1727_, v___x_1733_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_dec_ref_known(v___x_1734_, 1);
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
v___x_1764_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1763_, v___y_1645_, v___y_1642_, v___y_1641_, v___y_1646_, v___y_1650_, v___y_1649_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2077_, uint8_t v___x_2078_, lean_object* v_fst_2079_, lean_object* v_snd_2080_, lean_object* v___x_2081_, lean_object* v_____r_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2094_ = lean_unsigned_to_nat(2u);
v___x_2095_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*1, v_a_2077_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*1 + 1, v___x_2078_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_fst_2079_);
lean_ctor_set(v___x_2097_, 1, v_snd_2080_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2081_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2096_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2102_ = _args[0];
lean_object* v___x_2103_ = _args[1];
lean_object* v_fst_2104_ = _args[2];
lean_object* v_snd_2105_ = _args[3];
lean_object* v___x_2106_ = _args[4];
lean_object* v_____r_2107_ = _args[5];
lean_object* v___y_2108_ = _args[6];
lean_object* v___y_2109_ = _args[7];
lean_object* v___y_2110_ = _args[8];
lean_object* v___y_2111_ = _args[9];
lean_object* v___y_2112_ = _args[10];
lean_object* v___y_2113_ = _args[11];
lean_object* v___y_2114_ = _args[12];
lean_object* v___y_2115_ = _args[13];
lean_object* v___y_2116_ = _args[14];
lean_object* v___y_2117_ = _args[15];
lean_object* v___y_2118_ = _args[16];
_start:
{
uint8_t v_a_45067__boxed_2119_; uint8_t v___x_45068__boxed_2120_; lean_object* v_res_2121_; 
v_a_45067__boxed_2119_ = lean_unbox(v_a_2102_);
v___x_45068__boxed_2120_ = lean_unbox(v___x_2103_);
v_res_2121_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_45067__boxed_2119_, v___x_45068__boxed_2120_, v_fst_2104_, v_snd_2105_, v___x_2106_, v_____r_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec(v___y_2108_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2122_, lean_object* v_snd_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_____r_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2138_ = l_Lean_Expr_appFn_x21(v_fst_2122_);
v___x_2139_ = l_Lean_Expr_appFn_x21(v_snd_2123_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2124_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2125_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2145_, lean_object* v_snd_2146_, lean_object* v___x_2147_, lean_object* v___x_2148_, lean_object* v_____r_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2145_, v_snd_2146_, v___x_2147_, v___x_2148_, v_____r_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v_snd_2146_);
lean_dec(v_fst_2145_);
return v_res_2161_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___f_2163_; 
v___x_2162_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2163_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2163_, 0, v___x_2162_);
return v___f_2163_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2169_ = l_Lean_Name_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object* v___y_2188_, lean_object* v_eq_2189_, lean_object* v_a_2190_, lean_object* v_b_2191_, lean_object* v_a_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___y_2205_; lean_object* v___y_2226_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2349_; 
v_snd_2229_ = lean_ctor_get(v_a_2192_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_a_2192_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v_a_2192_, 0);
lean_dec(v_unused_2350_);
v___x_2231_ = v_a_2192_;
v_isShared_2232_ = v_isSharedCheck_2349_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_dec(v_a_2192_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2349_;
goto v_resetjp_2230_;
}
v___jp_2204_:
{
if (lean_obj_tag(v___y_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2216_; 
v_a_2206_ = lean_ctor_get(v___y_2205_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___y_2205_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2208_ = v___y_2205_;
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___y_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2216_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; 
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2210_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v_a_2206_, 1);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_a_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
else
{
lean_object* v_a_2214_; 
lean_del_object(v___x_2208_);
v_a_2214_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v_a_2206_, 1);
v_a_2192_ = v_a_2214_;
goto _start;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2217_ = lean_ctor_get(v___y_2205_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___y_2205_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___y_2205_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___y_2205_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_box(0);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
lean_inc(v___y_2194_);
lean_inc(v___y_2193_);
v___x_2228_ = lean_apply_12(v___y_2226_, v___x_2227_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, lean_box(0));
v___y_2205_ = v___x_2228_;
goto v___jp_2204_;
}
v_resetjp_2230_:
{
lean_object* v_snd_2233_; lean_object* v_fst_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2348_; 
v_snd_2233_ = lean_ctor_get(v_snd_2229_, 1);
v_fst_2234_ = lean_ctor_get(v_snd_2229_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_snd_2229_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2236_ = v_snd_2229_;
v_isShared_2237_ = v_isSharedCheck_2348_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2233_);
lean_inc(v_fst_2234_);
lean_dec(v_snd_2229_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2348_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_fst_2238_; lean_object* v_snd_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2347_; 
v_fst_2238_ = lean_ctor_get(v_snd_2233_, 0);
v_snd_2239_ = lean_ctor_get(v_snd_2233_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_snd_2233_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2241_ = v_snd_2233_;
v_isShared_2242_ = v_isSharedCheck_2347_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_snd_2239_);
lean_inc(v_fst_2238_);
lean_dec(v_snd_2233_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2347_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; uint8_t v___y_2246_; uint8_t v___x_2345_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = 1;
v___x_2345_ = l_Lean_Expr_isApp(v_fst_2238_);
if (v___x_2345_ == 0)
{
v___y_2246_ = v___x_2345_;
goto v___jp_2245_;
}
else
{
uint8_t v___x_2346_; 
v___x_2346_ = l_Lean_Expr_isApp(v_snd_2239_);
v___y_2246_ = v___x_2346_;
goto v___jp_2245_;
}
v___jp_2245_:
{
if (v___y_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v___x_2247_ = lean_unsigned_to_nat(2u);
v___x_2248_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1, v___y_2246_);
lean_ctor_set_uint8(v___x_2248_, sizeof(void*)*1 + 1, v___y_2246_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
if (v_isShared_2242_ == 0)
{
v___x_2251_ = v___x_2241_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_fst_2238_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_snd_2239_);
v___x_2251_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2251_);
v___x_2253_ = v___x_2236_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_fst_2234_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2253_);
lean_ctor_set(v___x_2231_, 0, v___x_2249_);
v___x_2255_ = v___x_2231_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; uint8_t v___x_2263_; 
lean_del_object(v___x_2241_);
lean_del_object(v___x_2236_);
lean_del_object(v___x_2231_);
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_sub(v_fst_2234_, v___x_2260_);
lean_dec(v_fst_2234_);
v___f_2262_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2188_);
lean_inc(v___x_2261_);
v___x_2263_ = l_List_elem___redArg(v___f_2262_, v___x_2261_, v___y_2188_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = l_Lean_Expr_appArg_x21(v_fst_2238_);
v___x_2265_ = l_Lean_Expr_appArg_x21(v_snd_2239_);
v___x_2266_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2264_, v___x_2265_, v___y_2193_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; uint8_t v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = lean_unbox(v_a_2267_);
if (v___x_2268_ == 0)
{
lean_object* v_options_2269_; lean_object* v_inheritedTraceOptions_2270_; uint8_t v_hasTrace_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; 
v_options_2269_ = lean_ctor_get(v___y_2201_, 2);
v_inheritedTraceOptions_2270_ = lean_ctor_get(v___y_2201_, 13);
v_hasTrace_2271_ = lean_ctor_get_uint8(v_options_2269_, sizeof(void*)*1);
v___x_2272_ = lean_box(v___x_2244_);
lean_inc(v___x_2261_);
lean_inc(v_snd_2239_);
lean_inc(v_fst_2238_);
lean_inc(v_a_2267_);
v___f_2273_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed), 17, 5);
lean_closure_set(v___f_2273_, 0, v_a_2267_);
lean_closure_set(v___f_2273_, 1, v___x_2272_);
lean_closure_set(v___f_2273_, 2, v_fst_2238_);
lean_closure_set(v___f_2273_, 3, v_snd_2239_);
lean_closure_set(v___f_2273_, 4, v___x_2261_);
if (v_hasTrace_2271_ == 0)
{
lean_dec(v_a_2267_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
v___y_2226_ = v___f_2273_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2275_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2270_, v_options_2269_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_dec(v_a_2267_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
v___y_2226_ = v___f_2273_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2277_; 
lean_dec_ref(v___f_2273_);
v___x_2277_ = l_Lean_Meta_Grind_updateLastTag(v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2278_; 
lean_dec_ref_known(v___x_2277_, 1);
v___x_2278_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2189_, v___y_2193_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2190_);
v___x_2281_ = l_Lean_MessageData_ofExpr(v_a_2190_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
lean_inc_ref(v_b_2191_);
v___x_2285_ = l_Lean_MessageData_ofExpr(v_b_2191_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
lean_inc_ref(v_eq_2189_);
v___x_2289_ = l_Lean_MessageData_ofExpr(v_eq_2189_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_MessageData_ofExpr(v___x_2264_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_MessageData_ofExpr(v___x_2265_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Nat_reprFast(v_a_2279_);
v___x_2302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
v___x_2303_ = l_Lean_MessageData_ofFormat(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2300_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2274_, v___x_2304_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_unbox(v_a_2267_);
lean_dec(v_a_2267_);
v___x_2308_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2307_, v___x_2244_, v_fst_2238_, v_snd_2239_, v___x_2261_, v_a_2306_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
v___y_2205_ = v___x_2308_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_a_2267_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2309_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2305_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_a_2267_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2317_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2278_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2278_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2267_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2325_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2277_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2277_);
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
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec(v_a_2267_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
v___x_2333_ = lean_box(0);
v___x_2334_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2238_, v_snd_2239_, v___x_2261_, v___x_2243_, v___x_2333_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
v___y_2205_ = v___x_2334_;
goto v___jp_2204_;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2264_);
lean_dec(v___x_2261_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
lean_dec_ref(v_b_2191_);
lean_dec_ref(v_a_2190_);
lean_dec_ref(v_eq_2189_);
lean_dec(v___y_2188_);
v_a_2335_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2266_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2266_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2238_, v_snd_2239_, v___x_2261_, v___x_2243_, v___x_2343_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v_snd_2239_);
lean_dec(v_fst_2238_);
v___y_2205_ = v___x_2344_;
goto v___jp_2204_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object* v___y_2351_, lean_object* v_eq_2352_, lean_object* v_a_2353_, lean_object* v_b_2354_, lean_object* v_a_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2351_, v_eq_2352_, v_a_2353_, v_b_2354_, v_a_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec(v___y_2356_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2368_, lean_object* v_b_2369_, lean_object* v_eq_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
uint8_t v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2415_; lean_object* v___x_2451_; 
lean_inc_ref(v_eq_2370_);
v___x_2451_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2370_, v_a_2371_, v_a_2375_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; uint8_t v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
v___x_2453_ = lean_unbox(v_a_2452_);
lean_dec(v_a_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref_known(v___x_2451_, 1);
lean_inc_ref(v_eq_2370_);
v___x_2454_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2370_, v_a_2371_, v_a_2375_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
v___y_2415_ = v___x_2454_;
goto v___jp_2414_;
}
else
{
v___y_2415_ = v___x_2451_;
goto v___jp_2414_;
}
}
else
{
v___y_2415_ = v___x_2451_;
goto v___jp_2414_;
}
v___jp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2385_ = l_Lean_Expr_getAppNumArgs(v_a_2368_);
v___x_2386_ = lean_box(0);
lean_inc_ref(v_b_2369_);
lean_inc_ref(v_a_2368_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_a_2368_);
lean_ctor_set(v___x_2387_, 1, v_b_2369_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2385_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2384_, v_eq_2370_, v_a_2368_, v_b_2369_, v___x_2389_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2405_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2405_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_fst_2395_; 
v_fst_2395_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_fst_2395_);
lean_dec(v_a_2391_);
if (lean_obj_tag(v_fst_2395_) == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2396_ = lean_unsigned_to_nat(2u);
v___x_2397_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___y_2383_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1 + 1, v___y_2383_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2397_);
v___x_2399_ = v___x_2393_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2403_; 
v_val_2401_ = lean_ctor_get(v_fst_2395_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v_fst_2395_, 1);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_val_2401_);
v___x_2403_ = v___x_2393_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_val_2401_);
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
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_a_2406_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2390_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2390_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
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
v___jp_2414_:
{
if (lean_obj_tag(v___y_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2442_; 
v_a_2416_ = lean_ctor_get(v___y_2415_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___y_2415_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2418_ = v___y_2415_;
v_isShared_2419_ = v_isSharedCheck_2442_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___y_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2442_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_unbox(v_a_2416_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v_toGoalState_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2418_);
v___x_2421_ = lean_st_ref_get(v_a_2371_);
v_toGoalState_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; 
v_unused_2437_ = lean_ctor_get(v___x_2421_, 1);
lean_dec(v_unused_2437_);
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2436_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_toGoalState_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2436_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_split_2426_; lean_object* v_argPosMap_2427_; lean_object* v___x_2429_; 
v_split_2426_ = lean_ctor_get(v_toGoalState_2422_, 14);
lean_inc_ref(v_split_2426_);
lean_dec_ref(v_toGoalState_2422_);
v_argPosMap_2427_ = lean_ctor_get(v_split_2426_, 6);
lean_inc_ref(v_argPosMap_2427_);
lean_dec_ref(v_split_2426_);
lean_inc_ref(v_b_2369_);
lean_inc_ref(v_a_2368_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v_b_2369_);
lean_ctor_set(v___x_2424_, 0, v_a_2368_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2368_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_b_2369_);
v___x_2429_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2427_, v___x_2429_);
lean_dec_ref(v___x_2429_);
lean_dec_ref(v_argPosMap_2427_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_unbox(v_a_2416_);
lean_dec(v_a_2416_);
v___y_2383_ = v___x_2432_;
v___y_2384_ = v___x_2431_;
goto v___jp_2382_;
}
else
{
lean_object* v_val_2433_; uint8_t v___x_2434_; 
v_val_2433_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2434_ = lean_unbox(v_a_2416_);
lean_dec(v_a_2416_);
v___y_2383_ = v___x_2434_;
v___y_2384_ = v_val_2433_;
goto v___jp_2382_;
}
}
}
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
lean_dec(v_a_2416_);
lean_dec_ref(v_eq_2370_);
lean_dec_ref(v_b_2369_);
lean_dec_ref(v_a_2368_);
v___x_2438_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2438_);
v___x_2440_ = v___x_2418_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_eq_2370_);
lean_dec_ref(v_b_2369_);
lean_dec_ref(v_a_2368_);
v_a_2443_ = lean_ctor_get(v___y_2415_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___y_2415_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___y_2415_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___y_2415_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2455_, lean_object* v_b_2456_, lean_object* v_eq_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2455_, v_b_2456_, v_eq_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec(v_a_2458_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* v___y_2470_, lean_object* v_eq_2471_, lean_object* v_a_2472_, lean_object* v_b_2473_, lean_object* v_inst_2474_, lean_object* v_a_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2470_, v_eq_2471_, v_a_2472_, v_b_2473_, v_a_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v___y_2488_ = _args[0];
lean_object* v_eq_2489_ = _args[1];
lean_object* v_a_2490_ = _args[2];
lean_object* v_b_2491_ = _args[3];
lean_object* v_inst_2492_ = _args[4];
lean_object* v_a_2493_ = _args[5];
lean_object* v___y_2494_ = _args[6];
lean_object* v___y_2495_ = _args[7];
lean_object* v___y_2496_ = _args[8];
lean_object* v___y_2497_ = _args[9];
lean_object* v___y_2498_ = _args[10];
lean_object* v___y_2499_ = _args[11];
lean_object* v___y_2500_ = _args[12];
lean_object* v___y_2501_ = _args[13];
lean_object* v___y_2502_ = _args[14];
lean_object* v___y_2503_ = _args[15];
lean_object* v___y_2504_ = _args[16];
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2488_, v_eq_2489_, v_a_2490_, v_b_2491_, v_inst_2492_, v_a_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2506_, lean_object* v_m_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2507_, v_a_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2510_, lean_object* v_m_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2510_, v_m_2511_, v_a_2512_);
lean_dec_ref(v_a_2512_);
lean_dec_ref(v_m_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2514_, lean_object* v_a_2515_, lean_object* v_x_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2515_, v_x_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2518_, lean_object* v_a_2519_, lean_object* v_x_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2518_, v_a_2519_, v_x_2520_);
lean_dec(v_x_2520_);
lean_dec_ref(v_a_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
uint8_t v___y_2531_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___x_2556_; 
lean_inc_ref(v_imp_2522_);
v___x_2556_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
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
v___x_2559_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
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
lean_object* v_binderType_2582_; lean_object* v_body_2583_; lean_object* v___y_2585_; lean_object* v___x_2613_; 
v_binderType_2582_ = lean_ctor_get(v_imp_2522_, 1);
lean_inc_ref_n(v_binderType_2582_, 2);
v_body_2583_ = lean_ctor_get(v_imp_2522_, 2);
lean_inc_ref(v_body_2583_);
lean_dec_ref(v_imp_2522_);
v___x_2613_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2582_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; uint8_t v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
v___x_2615_ = lean_unbox(v_a_2614_);
lean_dec(v_a_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
lean_dec_ref_known(v___x_2613_, 1);
v___x_2616_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2582_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
v___y_2585_ = v___x_2616_;
goto v___jp_2584_;
}
else
{
lean_dec_ref(v_binderType_2582_);
v___y_2585_ = v___x_2613_;
goto v___jp_2584_;
}
}
else
{
lean_dec_ref(v_binderType_2582_);
v___y_2585_ = v___x_2613_;
goto v___jp_2584_;
}
v___jp_2584_:
{
if (lean_obj_tag(v___y_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2604_; 
v_a_2586_ = lean_ctor_get(v___y_2585_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___y_2585_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2588_ = v___y_2585_;
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___y_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_unbox(v_a_2586_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
lean_del_object(v___x_2588_);
v___x_2591_ = l_Lean_Expr_hasLooseBVars(v_body_2583_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
lean_inc_ref(v_body_2583_);
v___x_2592_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2583_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; uint8_t v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
v___x_2594_ = lean_unbox(v_a_2593_);
lean_dec(v_a_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
lean_dec_ref_known(v___x_2592_, 1);
v___x_2595_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2583_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
v___x_2596_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
v___y_2536_ = v___x_2596_;
v___y_2537_ = v___x_2595_;
goto v___jp_2535_;
}
else
{
uint8_t v___x_2597_; 
lean_dec_ref(v_body_2583_);
v___x_2597_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
v___y_2536_ = v___x_2597_;
v___y_2537_ = v___x_2592_;
goto v___jp_2535_;
}
}
else
{
uint8_t v___x_2598_; 
lean_dec_ref(v_body_2583_);
v___x_2598_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
v___y_2536_ = v___x_2598_;
v___y_2537_ = v___x_2592_;
goto v___jp_2535_;
}
}
else
{
uint8_t v___x_2599_; 
lean_dec_ref(v_body_2583_);
v___x_2599_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
v___y_2531_ = v___x_2599_;
goto v___jp_2530_;
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec(v_a_2586_);
lean_dec_ref(v_body_2583_);
v___x_2600_ = lean_box(0);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2600_);
v___x_2602_ = v___x_2588_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
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
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_body_2583_);
v_a_2605_ = lean_ctor_get(v___y_2585_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___y_2585_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___y_2585_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___y_2585_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_imp_2522_);
v_a_2617_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2556_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2556_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
v___jp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_unsigned_to_nat(2u);
v___x_2533_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*1, v___y_2531_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*1 + 1, v___y_2531_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
v___jp_2535_:
{
if (lean_obj_tag(v___y_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2547_; 
v_a_2538_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2540_ = v___y_2537_;
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___y_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_unbox(v_a_2538_);
lean_dec(v_a_2538_);
if (v___x_2542_ == 0)
{
lean_del_object(v___x_2540_);
v___y_2531_ = v___y_2536_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_box(0);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
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
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___y_2537_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___y_2537_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2634_, lean_object* v_h_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2634_, v_a_2636_, v_a_2640_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2648_, lean_object* v_h_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2648_, v_h_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec(v_a_2650_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
switch(lean_obj_tag(v_s_2662_))
{
case 0:
{
lean_object* v_e_2674_; lean_object* v___x_2675_; 
v_e_2674_ = lean_ctor_get(v_s_2662_, 0);
lean_inc_ref(v_e_2674_);
lean_dec_ref_known(v_s_2662_, 2);
v___x_2675_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2674_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2675_;
}
case 1:
{
lean_object* v_e_2676_; lean_object* v___x_2677_; 
v_e_2676_ = lean_ctor_get(v_s_2662_, 0);
lean_inc_ref(v_e_2676_);
lean_dec_ref_known(v_s_2662_, 2);
v___x_2677_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2676_, v_a_2663_, v_a_2667_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2677_;
}
default: 
{
lean_object* v_a_2678_; lean_object* v_b_2679_; lean_object* v_eq_2680_; lean_object* v___x_2681_; 
v_a_2678_ = lean_ctor_get(v_s_2662_, 0);
lean_inc_ref(v_a_2678_);
v_b_2679_ = lean_ctor_get(v_s_2662_, 1);
lean_inc_ref(v_b_2679_);
v_eq_2680_ = lean_ctor_get(v_s_2662_, 3);
lean_inc_ref(v_eq_2680_);
lean_dec_ref_known(v_s_2662_, 5);
v___x_2681_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2678_, v_b_2679_, v_eq_2680_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2695_){
_start:
{
if (lean_obj_tag(v_x_2695_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_unsigned_to_nat(0u);
return v___x_2696_;
}
else
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2698_);
lean_dec(v_x_2698_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2700_, lean_object* v_k_2701_){
_start:
{
if (lean_obj_tag(v_t_2700_) == 0)
{
return v_k_2701_;
}
else
{
lean_object* v_c_2702_; lean_object* v_numCases_2703_; uint8_t v_isRec_2704_; uint8_t v_tryPostpone_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_c_2702_ = lean_ctor_get(v_t_2700_, 0);
lean_inc_ref(v_c_2702_);
v_numCases_2703_ = lean_ctor_get(v_t_2700_, 1);
lean_inc(v_numCases_2703_);
v_isRec_2704_ = lean_ctor_get_uint8(v_t_2700_, sizeof(void*)*2);
v_tryPostpone_2705_ = lean_ctor_get_uint8(v_t_2700_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2700_, 2);
v___x_2706_ = lean_box(v_isRec_2704_);
v___x_2707_ = lean_box(v_tryPostpone_2705_);
v___x_2708_ = lean_apply_4(v_k_2701_, v_c_2702_, v_numCases_2703_, v___x_2706_, v___x_2707_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2709_, lean_object* v_ctorIdx_2710_, lean_object* v_t_2711_, lean_object* v_h_2712_, lean_object* v_k_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2711_, v_k_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2715_, lean_object* v_ctorIdx_2716_, lean_object* v_t_2717_, lean_object* v_h_2718_, lean_object* v_k_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2715_, v_ctorIdx_2716_, v_t_2717_, v_h_2718_, v_k_2719_);
lean_dec(v_ctorIdx_2716_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2721_, lean_object* v_none_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2721_, v_none_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2724_, lean_object* v_t_2725_, lean_object* v_h_2726_, lean_object* v_none_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2725_, v_none_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2729_, lean_object* v_some_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2729_, v_some_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2732_, lean_object* v_t_2733_, lean_object* v_h_2734_, lean_object* v_some_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2733_, v_some_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2737_, lean_object* v_as_2738_, size_t v_i_2739_, size_t v_stop_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_eq(v_i_2739_, v_stop_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_array_uget_borrowed(v_as_2738_, v_i_2739_);
v___x_2743_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2742_, v_a_2737_);
if (v___x_2743_ == 0)
{
size_t v___x_2744_; size_t v___x_2745_; 
v___x_2744_ = ((size_t)1ULL);
v___x_2745_ = lean_usize_add(v_i_2739_, v___x_2744_);
v_i_2739_ = v___x_2745_;
goto _start;
}
else
{
return v___x_2743_;
}
}
else
{
uint8_t v___x_2747_; 
v___x_2747_ = 0;
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2748_, lean_object* v_as_2749_, lean_object* v_i_2750_, lean_object* v_stop_2751_){
_start:
{
uint64_t v_a_2749__boxed_2752_; size_t v_i_boxed_2753_; size_t v_stop_boxed_2754_; uint8_t v_res_2755_; lean_object* v_r_2756_; 
v_a_2749__boxed_2752_ = lean_unbox_uint64(v_a_2748_);
lean_dec_ref(v_a_2748_);
v_i_boxed_2753_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_stop_boxed_2754_ = lean_unbox_usize(v_stop_2751_);
lean_dec(v_stop_2751_);
v_res_2755_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2749__boxed_2752_, v_as_2749_, v_i_boxed_2753_, v_stop_boxed_2754_);
lean_dec_ref(v_as_2749_);
v_r_2756_ = lean_box(v_res_2755_);
return v_r_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2759_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2812_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2812_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2812_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
if (lean_obj_tag(v_a_2769_) == 1)
{
lean_object* v_val_2773_; lean_object* v___x_2774_; 
lean_del_object(v___x_2771_);
v_val_2773_ = lean_ctor_get(v_a_2769_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v_a_2769_, 1);
v___x_2774_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2798_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2798_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2798_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = lean_array_get_size(v_val_2773_);
v___x_2781_ = lean_nat_dec_lt(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
lean_dec(v_a_2775_);
lean_dec(v_val_2773_);
v___x_2782_ = lean_box(v___x_2781_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2782_);
v___x_2784_ = v___x_2777_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
else
{
if (v___x_2781_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_dec(v_a_2775_);
lean_dec(v_val_2773_);
v___x_2786_ = lean_box(v___x_2781_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2786_);
v___x_2788_ = v___x_2777_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
else
{
size_t v___x_2790_; size_t v___x_2791_; uint64_t v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2790_ = ((size_t)0ULL);
v___x_2791_ = lean_usize_of_nat(v___x_2780_);
v___x_2792_ = lean_unbox_uint64(v_a_2775_);
lean_dec(v_a_2775_);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2792_, v_val_2773_, v___x_2790_, v___x_2791_);
lean_dec(v_val_2773_);
v___x_2794_ = lean_box(v___x_2793_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2794_);
v___x_2796_ = v___x_2777_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_val_2773_);
v_a_2799_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2774_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2774_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_a_2769_);
v___x_2807_ = 1;
v___x_2808_ = lean_box(v___x_2807_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2808_);
v___x_2810_ = v___x_2771_;
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
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2768_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2768_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_c_2821_);
return v_res_2832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2836_, lean_object* v_c_x3f_2837_, lean_object* v_cs_x27_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
if (lean_obj_tag(v_cs_2836_) == 0)
{
lean_object* v___x_2850_; lean_object* v_toGoalState_2851_; lean_object* v_split_2852_; lean_object* v_mvarId_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2961_; 
v___x_2850_ = lean_st_ref_take(v_a_2839_);
v_toGoalState_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_toGoalState_2851_);
v_split_2852_ = lean_ctor_get(v_toGoalState_2851_, 14);
lean_inc_ref(v_split_2852_);
v_mvarId_2853_ = lean_ctor_get(v___x_2850_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; 
v_unused_2962_ = lean_ctor_get(v___x_2850_, 0);
lean_dec(v_unused_2962_);
v___x_2855_ = v___x_2850_;
v_isShared_2856_ = v_isSharedCheck_2961_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_mvarId_2853_);
lean_dec(v___x_2850_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2961_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_nextDeclIdx_2857_; lean_object* v_enodeMap_2858_; lean_object* v_exprs_2859_; lean_object* v_parents_2860_; lean_object* v_congrTable_2861_; lean_object* v_appMap_2862_; lean_object* v_indicesFound_2863_; lean_object* v_newFacts_2864_; uint8_t v_inconsistent_2865_; lean_object* v_nextIdx_2866_; lean_object* v_newRawFacts_2867_; lean_object* v_facts_2868_; lean_object* v_extThms_2869_; lean_object* v_ematch_2870_; lean_object* v_inj_2871_; lean_object* v_clean_2872_; lean_object* v_sstates_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2959_; 
v_nextDeclIdx_2857_ = lean_ctor_get(v_toGoalState_2851_, 0);
v_enodeMap_2858_ = lean_ctor_get(v_toGoalState_2851_, 1);
v_exprs_2859_ = lean_ctor_get(v_toGoalState_2851_, 2);
v_parents_2860_ = lean_ctor_get(v_toGoalState_2851_, 3);
v_congrTable_2861_ = lean_ctor_get(v_toGoalState_2851_, 4);
v_appMap_2862_ = lean_ctor_get(v_toGoalState_2851_, 5);
v_indicesFound_2863_ = lean_ctor_get(v_toGoalState_2851_, 6);
v_newFacts_2864_ = lean_ctor_get(v_toGoalState_2851_, 7);
v_inconsistent_2865_ = lean_ctor_get_uint8(v_toGoalState_2851_, sizeof(void*)*17);
v_nextIdx_2866_ = lean_ctor_get(v_toGoalState_2851_, 8);
v_newRawFacts_2867_ = lean_ctor_get(v_toGoalState_2851_, 9);
v_facts_2868_ = lean_ctor_get(v_toGoalState_2851_, 10);
v_extThms_2869_ = lean_ctor_get(v_toGoalState_2851_, 11);
v_ematch_2870_ = lean_ctor_get(v_toGoalState_2851_, 12);
v_inj_2871_ = lean_ctor_get(v_toGoalState_2851_, 13);
v_clean_2872_ = lean_ctor_get(v_toGoalState_2851_, 15);
v_sstates_2873_ = lean_ctor_get(v_toGoalState_2851_, 16);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_toGoalState_2851_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_toGoalState_2851_, 14);
lean_dec(v_unused_2960_);
v___x_2875_ = v_toGoalState_2851_;
v_isShared_2876_ = v_isSharedCheck_2959_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_sstates_2873_);
lean_inc(v_clean_2872_);
lean_inc(v_inj_2871_);
lean_inc(v_ematch_2870_);
lean_inc(v_extThms_2869_);
lean_inc(v_facts_2868_);
lean_inc(v_newRawFacts_2867_);
lean_inc(v_nextIdx_2866_);
lean_inc(v_newFacts_2864_);
lean_inc(v_indicesFound_2863_);
lean_inc(v_appMap_2862_);
lean_inc(v_congrTable_2861_);
lean_inc(v_parents_2860_);
lean_inc(v_exprs_2859_);
lean_inc(v_enodeMap_2858_);
lean_inc(v_nextDeclIdx_2857_);
lean_dec(v_toGoalState_2851_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2959_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_num_2877_; lean_object* v_added_2878_; lean_object* v_resolved_2879_; lean_object* v_trace_2880_; lean_object* v_lookaheads_2881_; lean_object* v_argPosMap_2882_; lean_object* v_argsAt_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2957_; 
v_num_2877_ = lean_ctor_get(v_split_2852_, 0);
v_added_2878_ = lean_ctor_get(v_split_2852_, 2);
v_resolved_2879_ = lean_ctor_get(v_split_2852_, 3);
v_trace_2880_ = lean_ctor_get(v_split_2852_, 4);
v_lookaheads_2881_ = lean_ctor_get(v_split_2852_, 5);
v_argPosMap_2882_ = lean_ctor_get(v_split_2852_, 6);
v_argsAt_2883_ = lean_ctor_get(v_split_2852_, 7);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_split_2852_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v_split_2852_, 1);
lean_dec(v_unused_2958_);
v___x_2885_ = v_split_2852_;
v_isShared_2886_ = v_isSharedCheck_2957_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_argsAt_2883_);
lean_inc(v_argPosMap_2882_);
lean_inc(v_lookaheads_2881_);
lean_inc(v_trace_2880_);
lean_inc(v_resolved_2879_);
lean_inc(v_added_2878_);
lean_inc(v_num_2877_);
lean_dec(v_split_2852_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2957_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = l_List_reverse___redArg(v_cs_x27_2838_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v___x_2887_);
v___x_2889_ = v___x_2885_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_num_2877_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_added_2878_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_resolved_2879_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_trace_2880_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v_lookaheads_2881_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_argPosMap_2882_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_argsAt_2883_);
v___x_2889_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 14, v___x_2889_);
v___x_2891_ = v___x_2875_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_nextDeclIdx_2857_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_enodeMap_2858_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_exprs_2859_);
lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_parents_2860_);
lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_congrTable_2861_);
lean_ctor_set(v_reuseFailAlloc_2955_, 5, v_appMap_2862_);
lean_ctor_set(v_reuseFailAlloc_2955_, 6, v_indicesFound_2863_);
lean_ctor_set(v_reuseFailAlloc_2955_, 7, v_newFacts_2864_);
lean_ctor_set(v_reuseFailAlloc_2955_, 8, v_nextIdx_2866_);
lean_ctor_set(v_reuseFailAlloc_2955_, 9, v_newRawFacts_2867_);
lean_ctor_set(v_reuseFailAlloc_2955_, 10, v_facts_2868_);
lean_ctor_set(v_reuseFailAlloc_2955_, 11, v_extThms_2869_);
lean_ctor_set(v_reuseFailAlloc_2955_, 12, v_ematch_2870_);
lean_ctor_set(v_reuseFailAlloc_2955_, 13, v_inj_2871_);
lean_ctor_set(v_reuseFailAlloc_2955_, 14, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2955_, 15, v_clean_2872_);
lean_ctor_set(v_reuseFailAlloc_2955_, 16, v_sstates_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2955_, sizeof(void*)*17, v_inconsistent_2865_);
v___x_2891_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2893_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2891_);
v___x_2893_ = v___x_2855_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_mvarId_2853_);
v___x_2893_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_st_ref_set(v_a_2839_, v___x_2893_);
if (lean_obj_tag(v_c_x3f_2837_) == 1)
{
lean_object* v___x_2895_; lean_object* v_toGoalState_2896_; lean_object* v_ematch_2897_; lean_object* v_mvarId_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2951_; 
v___x_2895_ = lean_st_ref_take(v_a_2839_);
v_toGoalState_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_ref(v_toGoalState_2896_);
v_ematch_2897_ = lean_ctor_get(v_toGoalState_2896_, 12);
lean_inc_ref(v_ematch_2897_);
v_mvarId_2898_ = lean_ctor_get(v___x_2895_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; 
v_unused_2952_ = lean_ctor_get(v___x_2895_, 0);
lean_dec(v_unused_2952_);
v___x_2900_ = v___x_2895_;
v_isShared_2901_ = v_isSharedCheck_2951_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_mvarId_2898_);
lean_dec(v___x_2895_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2951_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_nextDeclIdx_2902_; lean_object* v_enodeMap_2903_; lean_object* v_exprs_2904_; lean_object* v_parents_2905_; lean_object* v_congrTable_2906_; lean_object* v_appMap_2907_; lean_object* v_indicesFound_2908_; lean_object* v_newFacts_2909_; uint8_t v_inconsistent_2910_; lean_object* v_nextIdx_2911_; lean_object* v_newRawFacts_2912_; lean_object* v_facts_2913_; lean_object* v_extThms_2914_; lean_object* v_inj_2915_; lean_object* v_split_2916_; lean_object* v_clean_2917_; lean_object* v_sstates_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2949_; 
v_nextDeclIdx_2902_ = lean_ctor_get(v_toGoalState_2896_, 0);
v_enodeMap_2903_ = lean_ctor_get(v_toGoalState_2896_, 1);
v_exprs_2904_ = lean_ctor_get(v_toGoalState_2896_, 2);
v_parents_2905_ = lean_ctor_get(v_toGoalState_2896_, 3);
v_congrTable_2906_ = lean_ctor_get(v_toGoalState_2896_, 4);
v_appMap_2907_ = lean_ctor_get(v_toGoalState_2896_, 5);
v_indicesFound_2908_ = lean_ctor_get(v_toGoalState_2896_, 6);
v_newFacts_2909_ = lean_ctor_get(v_toGoalState_2896_, 7);
v_inconsistent_2910_ = lean_ctor_get_uint8(v_toGoalState_2896_, sizeof(void*)*17);
v_nextIdx_2911_ = lean_ctor_get(v_toGoalState_2896_, 8);
v_newRawFacts_2912_ = lean_ctor_get(v_toGoalState_2896_, 9);
v_facts_2913_ = lean_ctor_get(v_toGoalState_2896_, 10);
v_extThms_2914_ = lean_ctor_get(v_toGoalState_2896_, 11);
v_inj_2915_ = lean_ctor_get(v_toGoalState_2896_, 13);
v_split_2916_ = lean_ctor_get(v_toGoalState_2896_, 14);
v_clean_2917_ = lean_ctor_get(v_toGoalState_2896_, 15);
v_sstates_2918_ = lean_ctor_get(v_toGoalState_2896_, 16);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_toGoalState_2896_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; 
v_unused_2950_ = lean_ctor_get(v_toGoalState_2896_, 12);
lean_dec(v_unused_2950_);
v___x_2920_ = v_toGoalState_2896_;
v_isShared_2921_ = v_isSharedCheck_2949_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_sstates_2918_);
lean_inc(v_clean_2917_);
lean_inc(v_split_2916_);
lean_inc(v_inj_2915_);
lean_inc(v_extThms_2914_);
lean_inc(v_facts_2913_);
lean_inc(v_newRawFacts_2912_);
lean_inc(v_nextIdx_2911_);
lean_inc(v_newFacts_2909_);
lean_inc(v_indicesFound_2908_);
lean_inc(v_appMap_2907_);
lean_inc(v_congrTable_2906_);
lean_inc(v_parents_2905_);
lean_inc(v_exprs_2904_);
lean_inc(v_enodeMap_2903_);
lean_inc(v_nextDeclIdx_2902_);
lean_dec(v_toGoalState_2896_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2949_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v_thmMap_2922_; lean_object* v_gmt_2923_; lean_object* v_thms_2924_; lean_object* v_newThms_2925_; lean_object* v_numInstances_2926_; lean_object* v_numDelayedInstances_2927_; lean_object* v_preInstances_2928_; lean_object* v_nextThmIdx_2929_; lean_object* v_matchEqNames_2930_; lean_object* v_delayedThmInsts_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2947_; 
v_thmMap_2922_ = lean_ctor_get(v_ematch_2897_, 0);
v_gmt_2923_ = lean_ctor_get(v_ematch_2897_, 1);
v_thms_2924_ = lean_ctor_get(v_ematch_2897_, 2);
v_newThms_2925_ = lean_ctor_get(v_ematch_2897_, 3);
v_numInstances_2926_ = lean_ctor_get(v_ematch_2897_, 4);
v_numDelayedInstances_2927_ = lean_ctor_get(v_ematch_2897_, 5);
v_preInstances_2928_ = lean_ctor_get(v_ematch_2897_, 7);
v_nextThmIdx_2929_ = lean_ctor_get(v_ematch_2897_, 8);
v_matchEqNames_2930_ = lean_ctor_get(v_ematch_2897_, 9);
v_delayedThmInsts_2931_ = lean_ctor_get(v_ematch_2897_, 10);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_ematch_2897_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v_ematch_2897_, 6);
lean_dec(v_unused_2948_);
v___x_2933_ = v_ematch_2897_;
v_isShared_2934_ = v_isSharedCheck_2947_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_delayedThmInsts_2931_);
lean_inc(v_matchEqNames_2930_);
lean_inc(v_nextThmIdx_2929_);
lean_inc(v_preInstances_2928_);
lean_inc(v_numDelayedInstances_2927_);
lean_inc(v_numInstances_2926_);
lean_inc(v_newThms_2925_);
lean_inc(v_thms_2924_);
lean_inc(v_gmt_2923_);
lean_inc(v_thmMap_2922_);
lean_dec(v_ematch_2897_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2947_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = lean_unsigned_to_nat(0u);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 6, v___x_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_thmMap_2922_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_gmt_2923_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_thms_2924_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_newThms_2925_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_numInstances_2926_);
lean_ctor_set(v_reuseFailAlloc_2946_, 5, v_numDelayedInstances_2927_);
lean_ctor_set(v_reuseFailAlloc_2946_, 6, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2946_, 7, v_preInstances_2928_);
lean_ctor_set(v_reuseFailAlloc_2946_, 8, v_nextThmIdx_2929_);
lean_ctor_set(v_reuseFailAlloc_2946_, 9, v_matchEqNames_2930_);
lean_ctor_set(v_reuseFailAlloc_2946_, 10, v_delayedThmInsts_2931_);
v___x_2937_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 12, v___x_2937_);
v___x_2939_ = v___x_2920_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_nextDeclIdx_2902_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_enodeMap_2903_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_exprs_2904_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_parents_2905_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_congrTable_2906_);
lean_ctor_set(v_reuseFailAlloc_2945_, 5, v_appMap_2907_);
lean_ctor_set(v_reuseFailAlloc_2945_, 6, v_indicesFound_2908_);
lean_ctor_set(v_reuseFailAlloc_2945_, 7, v_newFacts_2909_);
lean_ctor_set(v_reuseFailAlloc_2945_, 8, v_nextIdx_2911_);
lean_ctor_set(v_reuseFailAlloc_2945_, 9, v_newRawFacts_2912_);
lean_ctor_set(v_reuseFailAlloc_2945_, 10, v_facts_2913_);
lean_ctor_set(v_reuseFailAlloc_2945_, 11, v_extThms_2914_);
lean_ctor_set(v_reuseFailAlloc_2945_, 12, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2945_, 13, v_inj_2915_);
lean_ctor_set(v_reuseFailAlloc_2945_, 14, v_split_2916_);
lean_ctor_set(v_reuseFailAlloc_2945_, 15, v_clean_2917_);
lean_ctor_set(v_reuseFailAlloc_2945_, 16, v_sstates_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2945_, sizeof(void*)*17, v_inconsistent_2910_);
v___x_2939_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2941_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2939_);
v___x_2941_ = v___x_2900_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_mvarId_2898_);
v___x_2941_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_st_ref_set(v_a_2839_, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_c_x3f_2837_);
return v___x_2943_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_c_x3f_2837_);
return v___x_2953_;
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
lean_object* v_head_2963_; lean_object* v_tail_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3184_; 
v_head_2963_ = lean_ctor_get(v_cs_2836_, 0);
v_tail_2964_ = lean_ctor_get(v_cs_2836_, 1);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_cs_2836_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_2966_ = v_cs_2836_;
v_isShared_2967_ = v_isSharedCheck_3184_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_tail_2964_);
lean_inc(v_head_2963_);
lean_dec(v_cs_2836_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3184_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3014_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; uint8_t v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3054_; uint8_t v___y_3055_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; uint8_t v___y_3091_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___x_3144_; 
v___x_3144_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2963_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
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
lean_del_object(v___x_2966_);
lean_dec(v_head_2963_);
v_cs_2836_ = v_tail_2964_;
goto _start;
}
else
{
lean_object* v_options_3148_; uint8_t v_hasTrace_3149_; 
v_options_3148_ = lean_ctor_get(v_a_2847_, 2);
v_hasTrace_3149_ = lean_ctor_get_uint8(v_options_3148_, sizeof(void*)*1);
if (v_hasTrace_3149_ == 0)
{
v___y_3102_ = v_a_2839_;
v___y_3103_ = v_a_2840_;
v___y_3104_ = v_a_2841_;
v___y_3105_ = v_a_2842_;
v___y_3106_ = v_a_2843_;
v___y_3107_ = v_a_2844_;
v___y_3108_ = v_a_2845_;
v___y_3109_ = v_a_2846_;
v___y_3110_ = v_a_2847_;
v___y_3111_ = v_a_2848_;
goto v___jp_3101_;
}
else
{
lean_object* v_inheritedTraceOptions_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_inheritedTraceOptions_3150_ = lean_ctor_get(v_a_2847_, 13);
v___x_3151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3153_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3150_, v_options_3148_, v___x_3152_);
if (v___x_3153_ == 0)
{
v___y_3102_ = v_a_2839_;
v___y_3103_ = v_a_2840_;
v___y_3104_ = v_a_2841_;
v___y_3105_ = v_a_2842_;
v___y_3106_ = v_a_2843_;
v___y_3107_ = v_a_2844_;
v___y_3108_ = v_a_2845_;
v___y_3109_ = v_a_2846_;
v___y_3110_ = v_a_2847_;
v___y_3111_ = v_a_2848_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_Meta_Grind_updateLastTag(v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec_ref_known(v___x_3154_, 1);
v___x_3155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3156_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2963_);
v___x_3157_ = l_Lean_MessageData_ofExpr(v___x_3156_);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3155_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3151_, v___x_3158_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_dec_ref_known(v___x_3159_, 1);
v___y_3102_ = v_a_2839_;
v___y_3103_ = v_a_2840_;
v___y_3104_ = v_a_2841_;
v___y_3105_ = v_a_2842_;
v___y_3106_ = v_a_2843_;
v___y_3107_ = v_a_2844_;
v___y_3108_ = v_a_2845_;
v___y_3109_ = v_a_2846_;
v___y_3110_ = v_a_2847_;
v___y_3111_ = v_a_2848_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3168_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3154_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3154_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3176_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3144_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3144_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
v___jp_2968_:
{
lean_object* v___x_2980_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v_cs_x27_2838_);
v___x_2980_ = v___x_2966_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_head_2963_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_cs_x27_2838_);
v___x_2980_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
v_cs_2836_ = v_tail_2964_;
v_cs_x27_2838_ = v___x_2980_;
v_a_2839_ = v___y_2971_;
v_a_2840_ = v___y_2970_;
v_a_2841_ = v___y_2976_;
v_a_2842_ = v___y_2972_;
v_a_2843_ = v___y_2974_;
v_a_2844_ = v___y_2977_;
v_a_2845_ = v___y_2969_;
v_a_2846_ = v___y_2975_;
v_a_2847_ = v___y_2978_;
v_a_2848_ = v___y_2973_;
goto _start;
}
}
v___jp_2983_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2998_, 0, v_head_2963_);
lean_ctor_set(v___x_2998_, 1, v___y_2993_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*2, v___y_2996_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*2 + 1, v___y_2994_);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___y_2989_);
lean_ctor_set(v___x_2999_, 1, v_cs_x27_2838_);
v_cs_2836_ = v_tail_2964_;
v_c_x3f_2837_ = v___x_2998_;
v_cs_x27_2838_ = v___x_2999_;
v_a_2839_ = v___y_2990_;
v_a_2840_ = v___y_2984_;
v_a_2841_ = v___y_2995_;
v_a_2842_ = v___y_2991_;
v_a_2843_ = v___y_2985_;
v_a_2844_ = v___y_2987_;
v_a_2845_ = v___y_2988_;
v_a_2846_ = v___y_2986_;
v_a_2847_ = v___y_2997_;
v_a_2848_ = v___y_2992_;
goto _start;
}
v___jp_3001_:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2963_, v___y_3009_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3008_, v___y_3009_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; uint8_t v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_nat_dec_lt(v_a_3018_, v_a_3020_);
lean_dec(v_a_3020_);
lean_dec(v_a_3018_);
if (v___x_3021_ == 0)
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_nat_dec_lt(v___y_3011_, v___y_3003_);
lean_dec(v___y_3003_);
if (v___x_3022_ == 0)
{
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3008_);
v___y_2969_ = v___y_3007_;
v___y_2970_ = v___y_3002_;
v___y_2971_ = v___y_3009_;
v___y_2972_ = v___y_3010_;
v___y_2973_ = v___y_3012_;
v___y_2974_ = v___y_3004_;
v___y_2975_ = v___y_3005_;
v___y_2976_ = v___y_3014_;
v___y_2977_ = v___y_3006_;
v___y_2978_ = v___y_3016_;
goto v___jp_2968_;
}
else
{
lean_del_object(v___x_2966_);
lean_dec(v_c_x3f_2837_);
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3007_;
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___y_3009_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
goto v___jp_2983_;
}
}
else
{
lean_dec(v___y_3003_);
lean_del_object(v___x_2966_);
lean_dec(v_c_x3f_2837_);
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3004_;
v___y_2986_ = v___y_3005_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3007_;
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___y_3009_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3012_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
goto v___jp_2983_;
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_a_3018_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3003_);
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3023_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3019_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3019_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3003_);
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3031_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3017_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3017_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
v___jp_3039_:
{
if (v___y_3055_ == 0)
{
v___y_3002_ = v___y_3040_;
v___y_3003_ = v___y_3041_;
v___y_3004_ = v___y_3042_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3045_;
v___y_3008_ = v___y_3046_;
v___y_3009_ = v___y_3047_;
v___y_3010_ = v___y_3048_;
v___y_3011_ = v___y_3049_;
v___y_3012_ = v___y_3050_;
v___y_3013_ = v___y_3051_;
v___y_3014_ = v___y_3052_;
v___y_3015_ = v___y_3054_;
v___y_3016_ = v___y_3053_;
goto v___jp_3001_;
}
else
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_nat_dec_lt(v___x_3056_, v___y_3041_);
if (v___x_3057_ == 0)
{
v___y_3002_ = v___y_3040_;
v___y_3003_ = v___y_3041_;
v___y_3004_ = v___y_3042_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3045_;
v___y_3008_ = v___y_3046_;
v___y_3009_ = v___y_3047_;
v___y_3010_ = v___y_3048_;
v___y_3011_ = v___y_3049_;
v___y_3012_ = v___y_3050_;
v___y_3013_ = v___y_3051_;
v___y_3014_ = v___y_3052_;
v___y_3015_ = v___y_3054_;
v___y_3016_ = v___y_3053_;
goto v___jp_3001_;
}
else
{
lean_dec(v___y_3041_);
lean_del_object(v___x_2966_);
lean_dec(v_c_x3f_2837_);
v___y_2984_ = v___y_3040_;
v___y_2985_ = v___y_3042_;
v___y_2986_ = v___y_3043_;
v___y_2987_ = v___y_3044_;
v___y_2988_ = v___y_3045_;
v___y_2989_ = v___y_3046_;
v___y_2990_ = v___y_3047_;
v___y_2991_ = v___y_3048_;
v___y_2992_ = v___y_3050_;
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3051_;
v___y_2995_ = v___y_3052_;
v___y_2996_ = v___y_3054_;
v___y_2997_ = v___y_3053_;
goto v___jp_2983_;
}
}
}
v___jp_3058_:
{
lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = lean_unsigned_to_nat(1u);
v___x_3076_ = lean_nat_dec_eq(v___y_3068_, v___x_3075_);
if (v___x_3076_ == 0)
{
v___y_3040_ = v___y_3059_;
v___y_3041_ = v___y_3060_;
v___y_3042_ = v___y_3061_;
v___y_3043_ = v___y_3062_;
v___y_3044_ = v___y_3063_;
v___y_3045_ = v___y_3064_;
v___y_3046_ = v___y_3065_;
v___y_3047_ = v___y_3066_;
v___y_3048_ = v___y_3067_;
v___y_3049_ = v___y_3068_;
v___y_3050_ = v___y_3069_;
v___y_3051_ = v___y_3070_;
v___y_3052_ = v___y_3071_;
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___x_3076_;
goto v___jp_3039_;
}
else
{
if (v___y_3072_ == 0)
{
v___y_3040_ = v___y_3059_;
v___y_3041_ = v___y_3060_;
v___y_3042_ = v___y_3061_;
v___y_3043_ = v___y_3062_;
v___y_3044_ = v___y_3063_;
v___y_3045_ = v___y_3064_;
v___y_3046_ = v___y_3065_;
v___y_3047_ = v___y_3066_;
v___y_3048_ = v___y_3067_;
v___y_3049_ = v___y_3068_;
v___y_3050_ = v___y_3069_;
v___y_3051_ = v___y_3070_;
v___y_3052_ = v___y_3071_;
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___x_3076_;
goto v___jp_3039_;
}
else
{
v___y_3040_ = v___y_3059_;
v___y_3041_ = v___y_3060_;
v___y_3042_ = v___y_3061_;
v___y_3043_ = v___y_3062_;
v___y_3044_ = v___y_3063_;
v___y_3045_ = v___y_3064_;
v___y_3046_ = v___y_3065_;
v___y_3047_ = v___y_3066_;
v___y_3048_ = v___y_3067_;
v___y_3049_ = v___y_3068_;
v___y_3050_ = v___y_3069_;
v___y_3051_ = v___y_3070_;
v___y_3052_ = v___y_3071_;
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3074_;
goto v___jp_3039_;
}
}
}
v___jp_3077_:
{
if (lean_obj_tag(v_c_x3f_2837_) == 0)
{
lean_object* v___x_3092_; 
lean_del_object(v___x_2966_);
v___x_3092_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3092_, 0, v_head_2963_);
lean_ctor_set(v___x_3092_, 1, v___y_3085_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*2, v___y_3089_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*2 + 1, v___y_3087_);
v_cs_2836_ = v_tail_2964_;
v_c_x3f_2837_ = v___x_3092_;
v_a_2839_ = v___y_3083_;
v_a_2840_ = v___y_3078_;
v_a_2841_ = v___y_3088_;
v_a_2842_ = v___y_3084_;
v_a_2843_ = v___y_3079_;
v_a_2844_ = v___y_3081_;
v_a_2845_ = v___y_3082_;
v_a_2846_ = v___y_3080_;
v_a_2847_ = v___y_3090_;
v_a_2848_ = v___y_3086_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3094_; 
v_tryPostpone_3094_ = lean_ctor_get_uint8(v_c_x3f_2837_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3094_ == 0)
{
if (v___y_3087_ == 0)
{
lean_object* v_c_3095_; lean_object* v_numCases_3096_; 
v_c_3095_ = lean_ctor_get(v_c_x3f_2837_, 0);
v_numCases_3096_ = lean_ctor_get(v_c_x3f_2837_, 1);
lean_inc_ref(v_c_3095_);
lean_inc(v_numCases_3096_);
v___y_3059_ = v___y_3078_;
v___y_3060_ = v_numCases_3096_;
v___y_3061_ = v___y_3079_;
v___y_3062_ = v___y_3080_;
v___y_3063_ = v___y_3081_;
v___y_3064_ = v___y_3082_;
v___y_3065_ = v_c_3095_;
v___y_3066_ = v___y_3083_;
v___y_3067_ = v___y_3084_;
v___y_3068_ = v___y_3085_;
v___y_3069_ = v___y_3086_;
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___y_3089_;
v___y_3073_ = v___y_3090_;
v___y_3074_ = v___y_3087_;
goto v___jp_3058_;
}
else
{
lean_dec(v___y_3085_);
v___y_2969_ = v___y_3082_;
v___y_2970_ = v___y_3078_;
v___y_2971_ = v___y_3083_;
v___y_2972_ = v___y_3084_;
v___y_2973_ = v___y_3086_;
v___y_2974_ = v___y_3079_;
v___y_2975_ = v___y_3080_;
v___y_2976_ = v___y_3088_;
v___y_2977_ = v___y_3081_;
v___y_2978_ = v___y_3090_;
goto v___jp_2968_;
}
}
else
{
if (v___y_3087_ == 0)
{
lean_object* v_c_3097_; 
lean_del_object(v___x_2966_);
v_c_3097_ = lean_ctor_get(v_c_x3f_2837_, 0);
lean_inc_ref(v_c_3097_);
lean_dec_ref_known(v_c_x3f_2837_, 2);
v___y_2984_ = v___y_3078_;
v___y_2985_ = v___y_3079_;
v___y_2986_ = v___y_3080_;
v___y_2987_ = v___y_3081_;
v___y_2988_ = v___y_3082_;
v___y_2989_ = v_c_3097_;
v___y_2990_ = v___y_3083_;
v___y_2991_ = v___y_3084_;
v___y_2992_ = v___y_3086_;
v___y_2993_ = v___y_3085_;
v___y_2994_ = v___y_3087_;
v___y_2995_ = v___y_3088_;
v___y_2996_ = v___y_3089_;
v___y_2997_ = v___y_3090_;
goto v___jp_2983_;
}
else
{
if (v___y_3091_ == 0)
{
lean_object* v_c_3098_; lean_object* v_numCases_3099_; 
v_c_3098_ = lean_ctor_get(v_c_x3f_2837_, 0);
v_numCases_3099_ = lean_ctor_get(v_c_x3f_2837_, 1);
lean_inc_ref(v_c_3098_);
lean_inc(v_numCases_3099_);
v___y_3059_ = v___y_3078_;
v___y_3060_ = v_numCases_3099_;
v___y_3061_ = v___y_3079_;
v___y_3062_ = v___y_3080_;
v___y_3063_ = v___y_3081_;
v___y_3064_ = v___y_3082_;
v___y_3065_ = v_c_3098_;
v___y_3066_ = v___y_3083_;
v___y_3067_ = v___y_3084_;
v___y_3068_ = v___y_3085_;
v___y_3069_ = v___y_3086_;
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___y_3089_;
v___y_3073_ = v___y_3090_;
v___y_3074_ = v___y_3091_;
goto v___jp_3058_;
}
else
{
lean_object* v_c_3100_; 
lean_del_object(v___x_2966_);
v_c_3100_ = lean_ctor_get(v_c_x3f_2837_, 0);
lean_inc_ref(v_c_3100_);
lean_dec_ref_known(v_c_x3f_2837_, 2);
v___y_2984_ = v___y_3078_;
v___y_2985_ = v___y_3079_;
v___y_2986_ = v___y_3080_;
v___y_2987_ = v___y_3081_;
v___y_2988_ = v___y_3082_;
v___y_2989_ = v_c_3100_;
v___y_2990_ = v___y_3083_;
v___y_2991_ = v___y_3084_;
v___y_2992_ = v___y_3086_;
v___y_2993_ = v___y_3085_;
v___y_2994_ = v___y_3087_;
v___y_2995_ = v___y_3088_;
v___y_2996_ = v___y_3089_;
v___y_2997_ = v___y_3090_;
goto v___jp_2983_;
}
}
}
}
}
v___jp_3101_:
{
lean_object* v___x_3112_; 
lean_inc(v_head_2963_);
v___x_3112_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2963_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
switch(lean_obj_tag(v_a_3113_))
{
case 0:
{
lean_del_object(v___x_2966_);
lean_dec(v_head_2963_);
v_cs_2836_ = v_tail_2964_;
v_a_2839_ = v___y_3102_;
v_a_2840_ = v___y_3103_;
v_a_2841_ = v___y_3104_;
v_a_2842_ = v___y_3105_;
v_a_2843_ = v___y_3106_;
v_a_2844_ = v___y_3107_;
v_a_2845_ = v___y_3108_;
v_a_2846_ = v___y_3109_;
v_a_2847_ = v___y_3110_;
v_a_2848_ = v___y_3111_;
goto _start;
}
case 1:
{
lean_object* v___x_3115_; 
lean_del_object(v___x_2966_);
v___x_3115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_head_2963_);
lean_ctor_set(v___x_3115_, 1, v_cs_x27_2838_);
v_cs_2836_ = v_tail_2964_;
v_cs_x27_2838_ = v___x_3115_;
v_a_2839_ = v___y_3102_;
v_a_2840_ = v___y_3103_;
v_a_2841_ = v___y_3104_;
v_a_2842_ = v___y_3105_;
v_a_2843_ = v___y_3106_;
v_a_2844_ = v___y_3107_;
v_a_2845_ = v___y_3108_;
v_a_2846_ = v___y_3109_;
v_a_2847_ = v___y_3110_;
v_a_2848_ = v___y_3111_;
goto _start;
}
default: 
{
lean_object* v_numCases_3117_; uint8_t v_isRec_3118_; uint8_t v_tryPostpone_3119_; lean_object* v___x_3120_; 
v_numCases_3117_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_numCases_3117_);
v_isRec_3118_ = lean_ctor_get_uint8(v_a_3113_, sizeof(void*)*1);
v_tryPostpone_3119_ = lean_ctor_get_uint8(v_a_3113_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3113_, 1);
v___x_3120_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3104_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; uint8_t v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = lean_unbox(v_a_3121_);
if (v___x_3122_ == 0)
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_unbox(v_a_3121_);
lean_dec(v_a_3121_);
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___y_3106_;
v___y_3080_ = v___y_3109_;
v___y_3081_ = v___y_3107_;
v___y_3082_ = v___y_3108_;
v___y_3083_ = v___y_3102_;
v___y_3084_ = v___y_3105_;
v___y_3085_ = v_numCases_3117_;
v___y_3086_ = v___y_3111_;
v___y_3087_ = v_tryPostpone_3119_;
v___y_3088_ = v___y_3104_;
v___y_3089_ = v_isRec_3118_;
v___y_3090_ = v___y_3110_;
v___y_3091_ = v___x_3123_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3124_; uint8_t v___x_3125_; 
lean_dec(v_a_3121_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_dec_lt(v___x_3124_, v_numCases_3117_);
if (v___x_3125_ == 0)
{
v___y_3078_ = v___y_3103_;
v___y_3079_ = v___y_3106_;
v___y_3080_ = v___y_3109_;
v___y_3081_ = v___y_3107_;
v___y_3082_ = v___y_3108_;
v___y_3083_ = v___y_3102_;
v___y_3084_ = v___y_3105_;
v___y_3085_ = v_numCases_3117_;
v___y_3086_ = v___y_3111_;
v___y_3087_ = v_tryPostpone_3119_;
v___y_3088_ = v___y_3104_;
v___y_3089_ = v_isRec_3118_;
v___y_3090_ = v___y_3110_;
v___y_3091_ = v___x_3125_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3126_; 
lean_dec(v_numCases_3117_);
lean_del_object(v___x_2966_);
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v_head_2963_);
lean_ctor_set(v___x_3126_, 1, v_cs_x27_2838_);
v_cs_2836_ = v_tail_2964_;
v_cs_x27_2838_ = v___x_3126_;
v_a_2839_ = v___y_3102_;
v_a_2840_ = v___y_3103_;
v_a_2841_ = v___y_3104_;
v_a_2842_ = v___y_3105_;
v_a_2843_ = v___y_3106_;
v_a_2844_ = v___y_3107_;
v_a_2845_ = v___y_3108_;
v_a_2846_ = v___y_3109_;
v_a_2847_ = v___y_3110_;
v_a_2848_ = v___y_3111_;
goto _start;
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_numCases_3117_);
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3128_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3120_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3120_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_del_object(v___x_2966_);
lean_dec(v_tail_2964_);
lean_dec(v_head_2963_);
lean_dec(v_cs_x27_2838_);
lean_dec(v_c_x3f_2837_);
v_a_3136_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3112_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3112_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3185_, lean_object* v_c_x3f_3186_, lean_object* v_cs_x27_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3185_, v_c_x3f_3186_, v_cs_x27_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec(v_a_3188_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3200_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3247_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3247_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3247_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
lean_del_object(v___x_3214_);
v___x_3217_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3200_, v_a_3202_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3234_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3234_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3234_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_unbox(v_a_3218_);
lean_dec(v_a_3218_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v_toGoalState_3224_; lean_object* v_split_3225_; lean_object* v_candidates_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_del_object(v___x_3220_);
v___x_3223_ = lean_st_ref_get(v_a_3200_);
v_toGoalState_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc_ref(v_toGoalState_3224_);
lean_dec(v___x_3223_);
v_split_3225_ = lean_ctor_get(v_toGoalState_3224_, 14);
lean_inc_ref(v_split_3225_);
lean_dec_ref(v_toGoalState_3224_);
v_candidates_3226_ = lean_ctor_get(v_split_3225_, 1);
lean_inc(v_candidates_3226_);
lean_dec_ref(v_split_3225_);
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_box(0);
v___x_3229_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3226_, v___x_3227_, v___x_3228_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_box(0);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3230_);
v___x_3232_ = v___x_3220_;
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
v_a_3235_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3217_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3217_);
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
else
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3243_);
v___x_3245_ = v___x_3214_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
v_a_3248_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3211_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3211_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3277_ = l_Lean_mkConst(v___x_3276_, v___x_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3280_ = l_Lean_Expr_app___override(v___x_3279_, v_c_3278_);
return v___x_3280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3291_ = l_Lean_mkConst(v___x_3290_, v___x_3289_);
return v___x_3291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3299_ = l_Lean_mkConst(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3307_ = l_Lean_mkConst(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; uint8_t v___y_3331_; lean_object* v___x_3367_; 
lean_inc_ref(v_c_3308_);
v___x_3367_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3308_, v_a_3316_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3453_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3453_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3453_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = l_Lean_Expr_cleanupAnnotations(v_a_3368_);
v___x_3386_ = l_Lean_Expr_isApp(v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec_ref(v___x_3385_);
lean_del_object(v___x_3370_);
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
v___y_3377_ = v_a_3313_;
v___y_3378_ = v_a_3314_;
v___y_3379_ = v_a_3315_;
v___y_3380_ = v_a_3316_;
v___y_3381_ = v_a_3317_;
v___y_3382_ = v_a_3318_;
goto v___jp_3372_;
}
else
{
lean_object* v_arg_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v_arg_3387_ = lean_ctor_get(v___x_3385_, 1);
lean_inc_ref(v_arg_3387_);
v___x_3388_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3385_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3390_ = l_Lean_Expr_isConstOf(v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
uint8_t v___x_3391_; 
v___x_3391_ = l_Lean_Expr_isApp(v___x_3388_);
if (v___x_3391_ == 0)
{
lean_dec_ref(v___x_3388_);
lean_dec_ref(v_arg_3387_);
lean_del_object(v___x_3370_);
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
v___y_3377_ = v_a_3313_;
v___y_3378_ = v_a_3314_;
v___y_3379_ = v_a_3315_;
v___y_3380_ = v_a_3316_;
v___y_3381_ = v_a_3317_;
v___y_3382_ = v_a_3318_;
goto v___jp_3372_;
}
else
{
lean_object* v_arg_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v_arg_3392_ = lean_ctor_get(v___x_3388_, 1);
lean_inc_ref(v_arg_3392_);
v___x_3393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3388_);
v___x_3394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3395_ = l_Lean_Expr_isConstOf(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
uint8_t v___x_3396_; 
v___x_3396_ = l_Lean_Expr_isApp(v___x_3393_);
if (v___x_3396_ == 0)
{
lean_dec_ref(v___x_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
lean_del_object(v___x_3370_);
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
v___y_3377_ = v_a_3313_;
v___y_3378_ = v_a_3314_;
v___y_3379_ = v_a_3315_;
v___y_3380_ = v_a_3316_;
v___y_3381_ = v_a_3317_;
v___y_3382_ = v_a_3318_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3393_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3399_ = l_Lean_Expr_isConstOf(v___x_3397_, v___x_3398_);
lean_dec_ref(v___x_3397_);
if (v___x_3399_ == 0)
{
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
lean_del_object(v___x_3370_);
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
v___y_3377_ = v_a_3313_;
v___y_3378_ = v_a_3314_;
v___y_3379_ = v_a_3315_;
v___y_3380_ = v_a_3316_;
v___y_3381_ = v_a_3317_;
v___y_3382_ = v_a_3318_;
goto v___jp_3372_;
}
else
{
uint8_t v___x_3400_; 
lean_inc_ref(v_c_3308_);
v___x_3400_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3308_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
v___x_3401_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3308_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3401_);
v___x_3403_ = v___x_3370_;
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
else
{
lean_object* v___x_3405_; 
lean_del_object(v___x_3370_);
lean_inc_ref(v_c_3308_);
v___x_3405_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3308_, v_a_3309_, v_a_3313_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; uint8_t v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = lean_unbox(v_a_3406_);
lean_dec(v_a_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3418_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3414_ = l_Lean_mkApp3(v___x_3413_, v_arg_3392_, v_arg_3387_, v_a_3409_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3414_);
v___x_3416_ = v___x_3411_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
return v___x_3408_;
}
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3429_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3425_ = l_Lean_mkApp3(v___x_3424_, v_arg_3392_, v_arg_3387_, v_a_3420_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
return v___x_3419_;
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
lean_dec_ref(v_c_3308_);
v_a_3430_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3405_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3405_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3438_; 
lean_dec_ref(v___x_3393_);
lean_del_object(v___x_3370_);
v___x_3438_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3448_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3444_ = l_Lean_mkApp3(v___x_3443_, v_arg_3392_, v_arg_3387_, v_a_3439_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3444_);
v___x_3446_ = v___x_3441_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
else
{
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3387_);
return v___x_3438_;
}
}
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
lean_dec_ref(v___x_3388_);
lean_dec_ref(v_c_3308_);
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3387_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3449_);
v___x_3451_ = v___x_3370_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
v___jp_3372_:
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Lean_Meta_Grind_isIte(v_c_3308_);
if (v___x_3383_ == 0)
{
uint8_t v___x_3384_; 
v___x_3384_ = l_Lean_Meta_Grind_isDIte(v_c_3308_);
v___y_3321_ = v___y_3375_;
v___y_3322_ = v___y_3374_;
v___y_3323_ = v___y_3373_;
v___y_3324_ = v___y_3376_;
v___y_3325_ = v___y_3377_;
v___y_3326_ = v___y_3380_;
v___y_3327_ = v___y_3382_;
v___y_3328_ = v___y_3381_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___x_3384_;
goto v___jp_3320_;
}
else
{
v___y_3321_ = v___y_3375_;
v___y_3322_ = v___y_3374_;
v___y_3323_ = v___y_3373_;
v___y_3324_ = v___y_3376_;
v___y_3325_ = v___y_3377_;
v___y_3326_ = v___y_3380_;
v___y_3327_ = v___y_3382_;
v___y_3328_ = v___y_3381_;
v___y_3329_ = v___y_3378_;
v___y_3330_ = v___y_3379_;
v___y_3331_ = v___x_3383_;
goto v___jp_3320_;
}
}
}
}
else
{
lean_dec_ref(v_c_3308_);
return v___x_3367_;
}
v___jp_3320_:
{
if (v___y_3331_ == 0)
{
lean_object* v___x_3332_; 
lean_inc_ref(v_c_3308_);
v___x_3332_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3308_, v___y_3323_, v___y_3325_, v___y_3330_, v___y_3326_, v___y_3328_, v___y_3327_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3351_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3351_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3351_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_unbox(v_a_3333_);
lean_dec(v_a_3333_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3339_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v_c_3308_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_c_3308_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v___x_3341_; 
lean_del_object(v___x_3335_);
lean_inc_ref(v_c_3308_);
v___x_3341_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3308_, v___y_3323_, v___y_3322_, v___y_3321_, v___y_3324_, v___y_3325_, v___y_3329_, v___y_3330_, v___y_3326_, v___y_3328_, v___y_3327_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3308_, v_a_3342_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
else
{
lean_dec_ref(v_c_3308_);
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v_c_3308_);
v_a_3352_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3332_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3332_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = l_Lean_Expr_getAppNumArgs(v_c_3308_);
v___x_3362_ = lean_nat_sub(v___x_3361_, v___x_3360_);
lean_dec(v___x_3361_);
v___x_3363_ = lean_nat_sub(v___x_3362_, v___x_3360_);
lean_dec(v___x_3362_);
v___x_3364_ = l_Lean_Expr_getRevArg_x21(v_c_3308_, v___x_3363_);
lean_dec_ref(v_c_3308_);
v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec(v_a_3455_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3467_, lean_object* v_major_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3469_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; uint8_t v_trace_3478_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v_trace_3478_ = lean_ctor_get_uint8(v_a_3477_, sizeof(void*)*13);
lean_dec(v_a_3477_);
if (v_trace_3478_ == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Meta_Grind_cases(v_mvarId_3467_, v_major_3468_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
return v___x_3479_;
}
else
{
lean_object* v___x_3480_; 
lean_inc(v_a_3474_);
lean_inc_ref(v_a_3473_);
lean_inc(v_a_3472_);
lean_inc_ref(v_a_3471_);
lean_inc_ref(v_major_3468_);
v___x_3480_ = lean_infer_type(v_major_3468_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3482_ = l_Lean_Meta_whnfD(v_a_3481_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = l_Lean_Expr_getAppFn(v_a_3483_);
lean_dec(v_a_3483_);
if (lean_obj_tag(v___x_3484_) == 4)
{
lean_object* v_declName_3485_; lean_object* v___x_3486_; 
v_declName_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_declName_3485_);
lean_dec_ref_known(v___x_3484_, 2);
v___x_3486_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3485_, v_a_3470_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref_known(v___x_3486_, 1);
v___x_3487_ = l_Lean_Meta_Grind_cases(v_mvarId_3467_, v_major_3468_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
return v___x_3487_;
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v_major_3468_);
lean_dec(v_mvarId_3467_);
v_a_3488_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3486_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3486_);
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
lean_object* v___x_3496_; 
lean_dec_ref(v___x_3484_);
v___x_3496_ = l_Lean_Meta_Grind_cases(v_mvarId_3467_, v_major_3468_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
return v___x_3496_;
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_major_3468_);
lean_dec(v_mvarId_3467_);
v_a_3497_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3482_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3482_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_major_3468_);
lean_dec(v_mvarId_3467_);
v_a_3505_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3480_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3480_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_major_3468_);
lean_dec(v_mvarId_3467_);
v_a_3513_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3476_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3476_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3521_, lean_object* v_major_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3521_, v_major_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3531_, lean_object* v_major_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3531_, v_major_3532_, v_a_3535_, v_a_3536_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3545_, lean_object* v_major_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3545_, v_major_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec(v_a_3547_);
return v_res_3558_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3559_){
_start:
{
uint64_t v_anchor_3560_; 
v_anchor_3560_ = lean_ctor_get_uint64(v_e_3559_, sizeof(void*)*3);
return v_anchor_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3561_){
_start:
{
uint64_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3561_);
lean_dec_ref(v_e_3561_);
v_r_3563_ = lean_box_uint64(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3567_) == 0)
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_box(0);
return v___x_3568_;
}
else
{
lean_object* v_key_3569_; lean_object* v_value_3570_; lean_object* v_tail_3571_; uint64_t v___x_3572_; uint8_t v___x_3573_; 
v_key_3569_ = lean_ctor_get(v_x_3567_, 0);
v_value_3570_ = lean_ctor_get(v_x_3567_, 1);
v_tail_3571_ = lean_ctor_get(v_x_3567_, 2);
v___x_3572_ = lean_unbox_uint64(v_key_3569_);
v___x_3573_ = lean_uint64_dec_eq(v___x_3572_, v_a_3566_);
if (v___x_3573_ == 0)
{
v_x_3567_ = v_tail_3571_;
goto _start;
}
else
{
lean_object* v___x_3575_; 
lean_inc(v_value_3570_);
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_value_3570_);
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3576_, lean_object* v_x_3577_){
_start:
{
uint64_t v_a_boxed_3578_; lean_object* v_res_3579_; 
v_a_boxed_3578_ = lean_unbox_uint64(v_a_3576_);
lean_dec_ref(v_a_3576_);
v_res_3579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3578_, v_x_3577_);
lean_dec(v_x_3577_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3580_, uint64_t v_a_3581_){
_start:
{
lean_object* v_buckets_3582_; lean_object* v___x_3583_; uint64_t v___x_3584_; uint64_t v___x_3585_; uint64_t v_fold_3586_; uint64_t v___x_3587_; uint64_t v___x_3588_; uint64_t v___x_3589_; size_t v___x_3590_; size_t v___x_3591_; size_t v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_buckets_3582_ = lean_ctor_get(v_m_3580_, 1);
v___x_3583_ = lean_array_get_size(v_buckets_3582_);
v___x_3584_ = 32ULL;
v___x_3585_ = lean_uint64_shift_right(v_a_3581_, v___x_3584_);
v_fold_3586_ = lean_uint64_xor(v_a_3581_, v___x_3585_);
v___x_3587_ = 16ULL;
v___x_3588_ = lean_uint64_shift_right(v_fold_3586_, v___x_3587_);
v___x_3589_ = lean_uint64_xor(v_fold_3586_, v___x_3588_);
v___x_3590_ = lean_uint64_to_usize(v___x_3589_);
v___x_3591_ = lean_usize_of_nat(v___x_3583_);
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_sub(v___x_3591_, v___x_3592_);
v___x_3594_ = lean_usize_land(v___x_3590_, v___x_3593_);
v___x_3595_ = lean_array_uget_borrowed(v_buckets_3582_, v___x_3594_);
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3581_, v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3597_, lean_object* v_a_3598_){
_start:
{
uint64_t v_a_boxed_3599_; lean_object* v_res_3600_; 
v_a_boxed_3599_ = lean_unbox_uint64(v_a_3598_);
lean_dec_ref(v_a_3598_);
v_res_3600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3597_, v_a_boxed_3599_);
lean_dec_ref(v_m_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
return v_x_3601_;
}
else
{
lean_object* v_key_3603_; lean_object* v_value_3604_; lean_object* v_tail_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3629_; 
v_key_3603_ = lean_ctor_get(v_x_3602_, 0);
v_value_3604_ = lean_ctor_get(v_x_3602_, 1);
v_tail_3605_ = lean_ctor_get(v_x_3602_, 2);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3607_ = v_x_3602_;
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_tail_3605_);
lean_inc(v_value_3604_);
lean_inc(v_key_3603_);
lean_dec(v_x_3602_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3629_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; uint64_t v___x_3610_; uint64_t v___x_3611_; uint64_t v___x_3612_; uint64_t v___x_3613_; uint64_t v_fold_3614_; uint64_t v___x_3615_; uint64_t v___x_3616_; uint64_t v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; size_t v___x_3620_; size_t v___x_3621_; size_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3609_ = lean_array_get_size(v_x_3601_);
v___x_3610_ = 32ULL;
v___x_3611_ = lean_unbox_uint64(v_key_3603_);
v___x_3612_ = lean_uint64_shift_right(v___x_3611_, v___x_3610_);
v___x_3613_ = lean_unbox_uint64(v_key_3603_);
v_fold_3614_ = lean_uint64_xor(v___x_3613_, v___x_3612_);
v___x_3615_ = 16ULL;
v___x_3616_ = lean_uint64_shift_right(v_fold_3614_, v___x_3615_);
v___x_3617_ = lean_uint64_xor(v_fold_3614_, v___x_3616_);
v___x_3618_ = lean_uint64_to_usize(v___x_3617_);
v___x_3619_ = lean_usize_of_nat(v___x_3609_);
v___x_3620_ = ((size_t)1ULL);
v___x_3621_ = lean_usize_sub(v___x_3619_, v___x_3620_);
v___x_3622_ = lean_usize_land(v___x_3618_, v___x_3621_);
v___x_3623_ = lean_array_uget_borrowed(v_x_3601_, v___x_3622_);
lean_inc(v___x_3623_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 2, v___x_3623_);
v___x_3625_ = v___x_3607_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_key_3603_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_value_3604_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_array_uset(v_x_3601_, v___x_3622_, v___x_3625_);
v_x_3601_ = v___x_3626_;
v_x_3602_ = v_tail_3605_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3630_, lean_object* v_source_3631_, lean_object* v_target_3632_){
_start:
{
lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = lean_array_get_size(v_source_3631_);
v___x_3634_ = lean_nat_dec_lt(v_i_3630_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_dec_ref(v_source_3631_);
lean_dec(v_i_3630_);
return v_target_3632_;
}
else
{
lean_object* v_es_3635_; lean_object* v___x_3636_; lean_object* v_source_3637_; lean_object* v_target_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_es_3635_ = lean_array_fget(v_source_3631_, v_i_3630_);
v___x_3636_ = lean_box(0);
v_source_3637_ = lean_array_fset(v_source_3631_, v_i_3630_, v___x_3636_);
v_target_3638_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3632_, v_es_3635_);
v___x_3639_ = lean_unsigned_to_nat(1u);
v___x_3640_ = lean_nat_add(v_i_3630_, v___x_3639_);
lean_dec(v_i_3630_);
v_i_3630_ = v___x_3640_;
v_source_3631_ = v_source_3637_;
v_target_3632_ = v_target_3638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3642_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_nbuckets_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3643_ = lean_array_get_size(v_data_3642_);
v___x_3644_ = lean_unsigned_to_nat(2u);
v_nbuckets_3645_ = lean_nat_mul(v___x_3643_, v___x_3644_);
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3647_ = lean_box(0);
v___x_3648_ = lean_mk_array(v_nbuckets_3645_, v___x_3647_);
v___x_3649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3646_, v_data_3642_, v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3650_, lean_object* v_b_3651_, lean_object* v_x_3652_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_dec(v_b_3651_);
return v_x_3652_;
}
else
{
lean_object* v_key_3653_; lean_object* v_value_3654_; lean_object* v_tail_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3669_; 
v_key_3653_ = lean_ctor_get(v_x_3652_, 0);
v_value_3654_ = lean_ctor_get(v_x_3652_, 1);
v_tail_3655_ = lean_ctor_get(v_x_3652_, 2);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_x_3652_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3657_ = v_x_3652_;
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_tail_3655_);
lean_inc(v_value_3654_);
lean_inc(v_key_3653_);
lean_dec(v_x_3652_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
uint64_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = lean_unbox_uint64(v_key_3653_);
v___x_3660_ = lean_uint64_dec_eq(v___x_3659_, v_a_3650_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3650_, v_b_3651_, v_tail_3655_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 2, v___x_3661_);
v___x_3663_ = v___x_3657_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_key_3653_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_value_3654_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_dec(v_value_3654_);
lean_dec(v_key_3653_);
v___x_3665_ = lean_box_uint64(v_a_3650_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v_b_3651_);
lean_ctor_set(v___x_3657_, 0, v___x_3665_);
v___x_3667_ = v___x_3657_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_b_3651_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_tail_3655_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3670_, lean_object* v_b_3671_, lean_object* v_x_3672_){
_start:
{
uint64_t v_a_boxed_3673_; lean_object* v_res_3674_; 
v_a_boxed_3673_ = lean_unbox_uint64(v_a_3670_);
lean_dec_ref(v_a_3670_);
v_res_3674_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3673_, v_b_3671_, v_x_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3675_, lean_object* v_x_3676_){
_start:
{
if (lean_obj_tag(v_x_3676_) == 0)
{
uint8_t v___x_3677_; 
v___x_3677_ = 0;
return v___x_3677_;
}
else
{
lean_object* v_key_3678_; lean_object* v_tail_3679_; uint64_t v___x_3680_; uint8_t v___x_3681_; 
v_key_3678_ = lean_ctor_get(v_x_3676_, 0);
v_tail_3679_ = lean_ctor_get(v_x_3676_, 2);
v___x_3680_ = lean_unbox_uint64(v_key_3678_);
v___x_3681_ = lean_uint64_dec_eq(v___x_3680_, v_a_3675_);
if (v___x_3681_ == 0)
{
v_x_3676_ = v_tail_3679_;
goto _start;
}
else
{
return v___x_3681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3683_, lean_object* v_x_3684_){
_start:
{
uint64_t v_a_boxed_3685_; uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_a_boxed_3685_ = lean_unbox_uint64(v_a_3683_);
lean_dec_ref(v_a_3683_);
v_res_3686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3685_, v_x_3684_);
lean_dec(v_x_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3688_, uint64_t v_a_3689_, lean_object* v_b_3690_){
_start:
{
lean_object* v_size_3691_; lean_object* v_buckets_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3735_; 
v_size_3691_ = lean_ctor_get(v_m_3688_, 0);
v_buckets_3692_ = lean_ctor_get(v_m_3688_, 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_m_3688_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3694_ = v_m_3688_;
v_isShared_3695_ = v_isSharedCheck_3735_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_buckets_3692_);
lean_inc(v_size_3691_);
lean_dec(v_m_3688_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3735_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; uint64_t v___x_3697_; uint64_t v___x_3698_; uint64_t v_fold_3699_; uint64_t v___x_3700_; uint64_t v___x_3701_; uint64_t v___x_3702_; size_t v___x_3703_; size_t v___x_3704_; size_t v___x_3705_; size_t v___x_3706_; size_t v___x_3707_; lean_object* v_bkt_3708_; uint8_t v___x_3709_; 
v___x_3696_ = lean_array_get_size(v_buckets_3692_);
v___x_3697_ = 32ULL;
v___x_3698_ = lean_uint64_shift_right(v_a_3689_, v___x_3697_);
v_fold_3699_ = lean_uint64_xor(v_a_3689_, v___x_3698_);
v___x_3700_ = 16ULL;
v___x_3701_ = lean_uint64_shift_right(v_fold_3699_, v___x_3700_);
v___x_3702_ = lean_uint64_xor(v_fold_3699_, v___x_3701_);
v___x_3703_ = lean_uint64_to_usize(v___x_3702_);
v___x_3704_ = lean_usize_of_nat(v___x_3696_);
v___x_3705_ = ((size_t)1ULL);
v___x_3706_ = lean_usize_sub(v___x_3704_, v___x_3705_);
v___x_3707_ = lean_usize_land(v___x_3703_, v___x_3706_);
v_bkt_3708_ = lean_array_uget_borrowed(v_buckets_3692_, v___x_3707_);
v___x_3709_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3689_, v_bkt_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; lean_object* v_size_x27_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v_buckets_x27_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3710_ = lean_unsigned_to_nat(1u);
v_size_x27_3711_ = lean_nat_add(v_size_3691_, v___x_3710_);
lean_dec(v_size_3691_);
v___x_3712_ = lean_box_uint64(v_a_3689_);
lean_inc(v_bkt_3708_);
v___x_3713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_b_3690_);
lean_ctor_set(v___x_3713_, 2, v_bkt_3708_);
v_buckets_x27_3714_ = lean_array_uset(v_buckets_3692_, v___x_3707_, v___x_3713_);
v___x_3715_ = lean_unsigned_to_nat(4u);
v___x_3716_ = lean_nat_mul(v_size_x27_3711_, v___x_3715_);
v___x_3717_ = lean_unsigned_to_nat(3u);
v___x_3718_ = lean_nat_div(v___x_3716_, v___x_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_array_get_size(v_buckets_x27_3714_);
v___x_3720_ = lean_nat_dec_le(v___x_3718_, v___x_3719_);
lean_dec(v___x_3718_);
if (v___x_3720_ == 0)
{
lean_object* v_val_3721_; lean_object* v___x_3723_; 
v_val_3721_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3714_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_val_3721_);
lean_ctor_set(v___x_3694_, 0, v_size_x27_3711_);
v___x_3723_ = v___x_3694_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_size_x27_3711_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_val_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
else
{
lean_object* v___x_3726_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_buckets_x27_3714_);
lean_ctor_set(v___x_3694_, 0, v_size_x27_3711_);
v___x_3726_ = v___x_3694_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_size_x27_3711_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_buckets_x27_3714_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v_buckets_x27_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
lean_inc(v_bkt_3708_);
v___x_3728_ = lean_box(0);
v_buckets_x27_3729_ = lean_array_uset(v_buckets_3692_, v___x_3707_, v___x_3728_);
v___x_3730_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3689_, v_b_3690_, v_bkt_3708_);
v___x_3731_ = lean_array_uset(v_buckets_x27_3729_, v___x_3707_, v___x_3730_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3731_);
v___x_3733_ = v___x_3694_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_size_3691_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3731_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3736_, lean_object* v_a_3737_, lean_object* v_b_3738_){
_start:
{
uint64_t v_a_boxed_3739_; lean_object* v_res_3740_; 
v_a_boxed_3739_ = lean_unbox_uint64(v_a_3737_);
lean_dec_ref(v_a_3737_);
v_res_3740_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3736_, v_a_boxed_3739_, v_b_3738_);
return v_res_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3741_ = lean_box(0);
v___x_3742_ = lean_unsigned_to_nat(16u);
v___x_3743_ = lean_mk_array(v___x_3742_, v___x_3741_);
return v___x_3743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_found_3746_; 
v___x_3744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3745_ = lean_unsigned_to_nat(0u);
v_found_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3746_, 0, v___x_3745_);
lean_ctor_set(v_found_3746_, 1, v___x_3744_);
return v_found_3746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_found_3747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v_found_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3750_, lean_object* v_numDigits_3751_, lean_object* v_es_3752_, lean_object* v_as_3753_, size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_b_3756_){
_start:
{
lean_object* v_a_3758_; uint8_t v___x_3762_; 
v___x_3762_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
if (v___x_3762_ == 0)
{
return v_b_3756_;
}
else
{
lean_object* v_snd_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3797_; 
v_snd_3763_ = lean_ctor_get(v_b_3756_, 1);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_b_3756_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v_b_3756_, 0);
lean_dec(v_unused_3798_);
v___x_3765_ = v_b_3756_;
v_isShared_3766_ = v_isSharedCheck_3797_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_snd_3763_);
lean_dec(v_b_3756_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3797_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v_a_3767_; uint64_t v_anchor_3768_; lean_object* v___x_3769_; uint64_t v___x_3770_; uint64_t v___x_3771_; lean_object* v___x_3772_; 
v_a_3767_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
v_anchor_3768_ = lean_ctor_get_uint64(v_a_3767_, sizeof(void*)*3);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_uint64_of_nat(v_shift_3750_);
v___x_3771_ = lean_uint64_shift_right(v_anchor_3768_, v___x_3770_);
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3763_, v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 1)
{
lean_object* v_val_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3791_; 
v_val_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3791_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_val_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3791_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
uint64_t v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = lean_unbox_uint64(v_val_3773_);
lean_dec(v_val_3773_);
v___x_3778_ = lean_uint64_dec_eq(v___x_3777_, v_anchor_3768_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_add(v_numDigits_3751_, v___x_3779_);
v___x_3781_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3752_, v___x_3780_);
lean_dec(v___x_3780_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v___x_3781_);
v___x_3783_ = v___x_3775_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3785_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3783_);
v___x_3785_ = v___x_3765_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_snd_3763_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
else
{
lean_object* v___x_3789_; 
lean_del_object(v___x_3775_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3769_);
v___x_3789_ = v___x_3765_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_snd_3763_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v_a_3758_ = v___x_3789_;
goto v___jp_3757_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec(v___x_3772_);
v___x_3792_ = lean_box_uint64(v_anchor_3768_);
v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3763_, v___x_3771_, v___x_3792_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v___x_3793_);
lean_ctor_set(v___x_3765_, 0, v___x_3769_);
v___x_3795_ = v___x_3765_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
v_a_3758_ = v___x_3795_;
goto v___jp_3757_;
}
}
}
}
v___jp_3757_:
{
size_t v___x_3759_; size_t v___x_3760_; 
v___x_3759_ = ((size_t)1ULL);
v___x_3760_ = lean_usize_add(v_i_3755_, v___x_3759_);
v_i_3755_ = v___x_3760_;
v_b_3756_ = v_a_3758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3799_, lean_object* v_numDigits_3800_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3801_ = lean_unsigned_to_nat(4u);
v___x_3802_ = lean_nat_mul(v___x_3801_, v_numDigits_3800_);
v___x_3803_ = lean_unsigned_to_nat(64u);
v___x_3804_ = lean_nat_dec_lt(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec(v___x_3802_);
lean_inc(v_numDigits_3800_);
return v_numDigits_3800_;
}
else
{
lean_object* v_shift_3805_; lean_object* v___x_3806_; size_t v_sz_3807_; size_t v___x_3808_; lean_object* v___x_3809_; lean_object* v_fst_3810_; 
v_shift_3805_ = lean_nat_sub(v___x_3803_, v___x_3802_);
lean_dec(v___x_3802_);
v___x_3806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3807_ = lean_array_size(v_es_3799_);
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3805_, v_numDigits_3800_, v_es_3799_, v_es_3799_, v_sz_3807_, v___x_3808_, v___x_3806_);
lean_dec(v_shift_3805_);
v_fst_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_fst_3810_);
lean_dec_ref(v___x_3809_);
if (lean_obj_tag(v_fst_3810_) == 0)
{
lean_inc(v_numDigits_3800_);
return v_numDigits_3800_;
}
else
{
lean_object* v_val_3811_; 
v_val_3811_ = lean_ctor_get(v_fst_3810_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v_fst_3810_, 1);
return v_val_3811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3812_, lean_object* v_numDigits_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3812_, v_numDigits_3813_);
lean_dec(v_numDigits_3813_);
lean_dec_ref(v_es_3812_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3815_, lean_object* v_numDigits_3816_, lean_object* v_es_3817_, lean_object* v_as_3818_, lean_object* v_sz_3819_, lean_object* v_i_3820_, lean_object* v_b_3821_){
_start:
{
size_t v_sz_boxed_3822_; size_t v_i_boxed_3823_; lean_object* v_res_3824_; 
v_sz_boxed_3822_ = lean_unbox_usize(v_sz_3819_);
lean_dec(v_sz_3819_);
v_i_boxed_3823_ = lean_unbox_usize(v_i_3820_);
lean_dec(v_i_3820_);
v_res_3824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3815_, v_numDigits_3816_, v_es_3817_, v_as_3818_, v_sz_boxed_3822_, v_i_boxed_3823_, v_b_3821_);
lean_dec_ref(v_as_3818_);
lean_dec_ref(v_es_3817_);
lean_dec(v_numDigits_3816_);
lean_dec(v_shift_3815_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3825_){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = lean_unsigned_to_nat(4u);
v___x_3827_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3825_, v___x_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3828_);
lean_dec_ref(v_es_3828_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3830_, lean_object* v_as_3831_, size_t v_i_3832_, size_t v_stop_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_a_3847_; uint8_t v___x_3851_; 
v___x_3851_ = lean_usize_dec_eq(v_i_3832_, v_stop_3833_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_array_uget_borrowed(v_as_3831_, v_i_3832_);
v___x_3853_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3852_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v_e_3855_; lean_object* v___x_3856_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v_e_3855_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3852_);
lean_inc(v___x_3852_);
v___x_3856_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3852_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
if (lean_obj_tag(v_a_3857_) == 2)
{
lean_object* v_numCases_3858_; uint8_t v_isRec_3859_; lean_object* v___x_3860_; 
v_numCases_3858_ = lean_ctor_get(v_a_3857_, 0);
lean_inc(v_numCases_3858_);
v_isRec_3859_ = lean_ctor_get_uint8(v_a_3857_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3857_, 1);
lean_inc_ref(v_filter_3830_);
lean_inc(v___y_3844_);
lean_inc_ref(v___y_3843_);
lean_inc(v___y_3842_);
lean_inc_ref(v___y_3841_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc(v___y_3835_);
lean_inc_ref(v_e_3855_);
v___x_3860_ = lean_apply_12(v_filter_3830_, v_e_3855_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, lean_box(0));
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; uint8_t v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = lean_unbox(v_a_3861_);
lean_dec(v_a_3861_);
if (v___x_3862_ == 0)
{
lean_dec(v_numCases_3858_);
lean_dec_ref(v_e_3855_);
lean_dec(v_a_3854_);
v_a_3847_ = v_b_3834_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3863_; uint64_t v___x_3864_; lean_object* v___x_3865_; 
lean_inc(v___x_3852_);
v___x_3863_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3863_, 0, v___x_3852_);
lean_ctor_set(v___x_3863_, 1, v_numCases_3858_);
lean_ctor_set(v___x_3863_, 2, v_e_3855_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*3 + 8, v_isRec_3859_);
v___x_3864_ = lean_unbox_uint64(v_a_3854_);
lean_dec(v_a_3854_);
lean_ctor_set_uint64(v___x_3863_, sizeof(void*)*3, v___x_3864_);
v___x_3865_ = lean_array_push(v_b_3834_, v___x_3863_);
v_a_3847_ = v___x_3865_;
goto v___jp_3846_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_numCases_3858_);
lean_dec_ref(v_e_3855_);
lean_dec(v_a_3854_);
lean_dec_ref(v_b_3834_);
lean_dec_ref(v_filter_3830_);
v_a_3866_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3860_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3860_);
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
lean_dec(v_a_3857_);
lean_dec_ref(v_e_3855_);
lean_dec(v_a_3854_);
v_a_3847_ = v_b_3834_;
goto v___jp_3846_;
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_e_3855_);
lean_dec(v_a_3854_);
lean_dec_ref(v_b_3834_);
lean_dec_ref(v_filter_3830_);
v_a_3874_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3856_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3856_);
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
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref(v_b_3834_);
lean_dec_ref(v_filter_3830_);
v_a_3882_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3853_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3853_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
else
{
lean_object* v___x_3890_; 
lean_dec_ref(v_filter_3830_);
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_b_3834_);
return v___x_3890_;
}
v___jp_3846_:
{
size_t v___x_3848_; size_t v___x_3849_; 
v___x_3848_ = ((size_t)1ULL);
v___x_3849_ = lean_usize_add(v_i_3832_, v___x_3848_);
v_i_3832_ = v___x_3849_;
v_b_3834_ = v_a_3847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3891_, lean_object* v_as_3892_, lean_object* v_i_3893_, lean_object* v_stop_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
size_t v_i_boxed_3907_; size_t v_stop_boxed_3908_; lean_object* v_res_3909_; 
v_i_boxed_3907_ = lean_unbox_usize(v_i_3893_);
lean_dec(v_i_3893_);
v_stop_boxed_3908_ = lean_unbox_usize(v_stop_3894_);
lean_dec(v_stop_3894_);
v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3891_, v_as_3892_, v_i_boxed_3907_, v_stop_boxed_3908_, v_b_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v_as_3892_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3912_, lean_object* v_as_3913_, lean_object* v_start_3914_, lean_object* v_stop_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; uint8_t v___x_3928_; 
v___x_3927_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3928_ = lean_nat_dec_lt(v_start_3914_, v_stop_3915_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec_ref(v_filter_3912_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
return v___x_3929_;
}
else
{
lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3930_ = lean_array_get_size(v_as_3913_);
v___x_3931_ = lean_nat_dec_le(v_stop_3915_, v___x_3930_);
if (v___x_3931_ == 0)
{
uint8_t v___x_3932_; 
v___x_3932_ = lean_nat_dec_lt(v_start_3914_, v___x_3930_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; 
lean_dec_ref(v_filter_3912_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3927_);
return v___x_3933_;
}
else
{
size_t v___x_3934_; size_t v___x_3935_; lean_object* v___x_3936_; 
v___x_3934_ = lean_usize_of_nat(v_start_3914_);
v___x_3935_ = lean_usize_of_nat(v___x_3930_);
v___x_3936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3912_, v_as_3913_, v___x_3934_, v___x_3935_, v___x_3927_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v___x_3936_;
}
}
else
{
size_t v___x_3937_; size_t v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = lean_usize_of_nat(v_start_3914_);
v___x_3938_ = lean_usize_of_nat(v_stop_3915_);
v___x_3939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3912_, v_as_3913_, v___x_3937_, v___x_3938_, v___x_3927_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v___x_3939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3940_, lean_object* v_as_3941_, lean_object* v_start_3942_, lean_object* v_stop_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3940_, v_as_3941_, v_start_3942_, v_stop_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec(v_stop_3943_);
lean_dec(v_start_3942_);
lean_dec_ref(v_as_3941_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3956_, lean_object* v_candidates_x3f_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v_candidates_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; 
if (lean_obj_tag(v_candidates_x3f_3957_) == 0)
{
lean_object* v___x_4003_; lean_object* v_toGoalState_4004_; lean_object* v_split_4005_; lean_object* v_candidates_4006_; 
v___x_4003_ = lean_st_ref_get(v_a_3958_);
v_toGoalState_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc_ref(v_toGoalState_4004_);
lean_dec(v___x_4003_);
v_split_4005_ = lean_ctor_get(v_toGoalState_4004_, 14);
lean_inc_ref(v_split_4005_);
lean_dec_ref(v_toGoalState_4004_);
v_candidates_4006_ = lean_ctor_get(v_split_4005_, 1);
lean_inc(v_candidates_4006_);
lean_dec_ref(v_split_4005_);
v_candidates_3970_ = v_candidates_4006_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
v___y_3973_ = v_a_3960_;
v___y_3974_ = v_a_3961_;
v___y_3975_ = v_a_3962_;
v___y_3976_ = v_a_3963_;
v___y_3977_ = v_a_3964_;
v___y_3978_ = v_a_3965_;
v___y_3979_ = v_a_3966_;
v___y_3980_ = v_a_3967_;
goto v___jp_3969_;
}
else
{
lean_object* v_val_4007_; 
v_val_4007_ = lean_ctor_get(v_candidates_x3f_3957_, 0);
lean_inc(v_val_4007_);
lean_dec_ref_known(v_candidates_x3f_3957_, 1);
v_candidates_3970_ = v_val_4007_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
v___y_3973_ = v_a_3960_;
v___y_3974_ = v_a_3961_;
v___y_3975_ = v_a_3962_;
v___y_3976_ = v_a_3963_;
v___y_3977_ = v_a_3964_;
v___y_3978_ = v_a_3965_;
v___y_3979_ = v_a_3966_;
v___y_3980_ = v_a_3967_;
goto v___jp_3969_;
}
v___jp_3969_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3981_ = lean_array_mk(v_candidates_3970_);
v___x_3982_ = lean_unsigned_to_nat(0u);
v___x_3983_ = lean_array_get_size(v___x_3981_);
v___x_3984_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3956_, v___x_3981_, v___x_3982_, v___x_3983_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec_ref(v___x_3981_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3994_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_3994_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3994_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3989_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3985_);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v_a_3985_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3990_);
v___x_3992_ = v___x_3987_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3984_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3984_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4008_, lean_object* v_candidates_x3f_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4008_, v_candidates_x3f_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec(v_a_4010_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4022_, lean_object* v_m_4023_, uint64_t v_a_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4023_, v_a_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_){
_start:
{
uint64_t v_a_boxed_4029_; lean_object* v_res_4030_; 
v_a_boxed_4029_ = lean_unbox_uint64(v_a_4028_);
lean_dec_ref(v_a_4028_);
v_res_4030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4026_, v_m_4027_, v_a_boxed_4029_);
lean_dec_ref(v_m_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4031_, lean_object* v_m_4032_, uint64_t v_a_4033_, lean_object* v_b_4034_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4032_, v_a_4033_, v_b_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4036_, lean_object* v_m_4037_, lean_object* v_a_4038_, lean_object* v_b_4039_){
_start:
{
uint64_t v_a_boxed_4040_; lean_object* v_res_4041_; 
v_a_boxed_4040_ = lean_unbox_uint64(v_a_4038_);
lean_dec_ref(v_a_4038_);
v_res_4041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4036_, v_m_4037_, v_a_boxed_4040_, v_b_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4042_, uint64_t v_a_4043_, lean_object* v_x_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_a_4047_, lean_object* v_x_4048_){
_start:
{
uint64_t v_a_boxed_4049_; lean_object* v_res_4050_; 
v_a_boxed_4049_ = lean_unbox_uint64(v_a_4047_);
lean_dec_ref(v_a_4047_);
v_res_4050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4046_, v_a_boxed_4049_, v_x_4048_);
lean_dec(v_x_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4051_, uint64_t v_a_4052_, lean_object* v_x_4053_){
_start:
{
uint8_t v___x_4054_; 
v___x_4054_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4052_, v_x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_a_4056_, lean_object* v_x_4057_){
_start:
{
uint64_t v_a_boxed_4058_; uint8_t v_res_4059_; lean_object* v_r_4060_; 
v_a_boxed_4058_ = lean_unbox_uint64(v_a_4056_);
lean_dec_ref(v_a_4056_);
v_res_4059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4055_, v_a_boxed_4058_, v_x_4057_);
lean_dec(v_x_4057_);
v_r_4060_ = lean_box(v_res_4059_);
return v_r_4060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4061_, lean_object* v_data_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4064_, uint64_t v_a_4065_, lean_object* v_b_4066_, lean_object* v_x_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4065_, v_b_4066_, v_x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4069_, lean_object* v_a_4070_, lean_object* v_b_4071_, lean_object* v_x_4072_){
_start:
{
uint64_t v_a_boxed_4073_; lean_object* v_res_4074_; 
v_a_boxed_4073_ = lean_unbox_uint64(v_a_4070_);
lean_dec_ref(v_a_4070_);
v_res_4074_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4069_, v_a_boxed_4073_, v_b_4071_, v_x_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4075_, lean_object* v_i_4076_, lean_object* v_source_4077_, lean_object* v_target_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4076_, v_source_4077_, v_target_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4081_, v_x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = 1;
v___x_4097_ = lean_box(v___x_4096_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v_x_4099_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4112_, uint64_t v_a_4113_, lean_object* v_c_4114_, lean_object* v_numDigits_4115_, lean_object* v_as_4116_, size_t v_sz_4117_, size_t v_i_4118_, lean_object* v_b_4119_){
_start:
{
lean_object* v_a_4122_; uint8_t v___x_4126_; 
v___x_4126_ = lean_usize_dec_lt(v_i_4118_, v_sz_4117_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; 
lean_dec(v_numDigits_4115_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_b_4119_);
return v___x_4127_;
}
else
{
lean_object* v_snd_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4154_; 
v_snd_4128_ = lean_ctor_get(v_b_4119_, 1);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_b_4119_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v_b_4119_, 0);
lean_dec(v_unused_4155_);
v___x_4130_ = v_b_4119_;
v_isShared_4131_ = v_isSharedCheck_4154_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_snd_4128_);
lean_dec(v_b_4119_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4154_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_a_4132_; lean_object* v_c_4133_; uint64_t v_anchor_4134_; lean_object* v___x_4135_; uint64_t v___x_4136_; uint64_t v___x_4137_; uint8_t v___x_4138_; 
v_a_4132_ = lean_array_uget_borrowed(v_as_4116_, v_i_4118_);
v_c_4133_ = lean_ctor_get(v_a_4132_, 0);
v_anchor_4134_ = lean_ctor_get_uint64(v_a_4132_, sizeof(void*)*3);
v___x_4135_ = lean_box(0);
v___x_4136_ = lean_uint64_shift_right(v_anchor_4134_, v___x_4112_);
v___x_4137_ = lean_uint64_shift_right(v_a_4113_, v___x_4112_);
v___x_4138_ = lean_uint64_dec_eq(v___x_4136_, v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4140_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4135_);
v___x_4140_ = v___x_4130_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v_snd_4128_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
v_a_4122_ = v___x_4140_;
goto v___jp_4121_;
}
}
else
{
uint8_t v___x_4142_; 
v___x_4142_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4133_, v_c_4114_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = lean_nat_add(v_snd_4128_, v___x_4143_);
lean_dec(v_snd_4128_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v___x_4144_);
lean_ctor_set(v___x_4130_, 0, v___x_4135_);
v___x_4146_ = v___x_4130_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
v_a_4122_ = v___x_4146_;
goto v___jp_4121_;
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
lean_inc(v_snd_4128_);
v___x_4148_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4148_, 0, v_numDigits_4115_);
lean_ctor_set(v___x_4148_, 1, v_snd_4128_);
lean_ctor_set_uint64(v___x_4148_, sizeof(void*)*2, v_a_4113_);
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4149_);
v___x_4151_ = v___x_4130_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_snd_4128_);
v___x_4151_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
}
}
}
v___jp_4121_:
{
size_t v___x_4123_; size_t v___x_4124_; 
v___x_4123_ = ((size_t)1ULL);
v___x_4124_ = lean_usize_add(v_i_4118_, v___x_4123_);
v_i_4118_ = v___x_4124_;
v_b_4119_ = v_a_4122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4156_, lean_object* v_a_4157_, lean_object* v_c_4158_, lean_object* v_numDigits_4159_, lean_object* v_as_4160_, lean_object* v_sz_4161_, lean_object* v_i_4162_, lean_object* v_b_4163_, lean_object* v___y_4164_){
_start:
{
uint64_t v___x_8483__boxed_4165_; uint64_t v_a_8484__boxed_4166_; size_t v_sz_boxed_4167_; size_t v_i_boxed_4168_; lean_object* v_res_4169_; 
v___x_8483__boxed_4165_ = lean_unbox_uint64(v___x_4156_);
lean_dec_ref(v___x_4156_);
v_a_8484__boxed_4166_ = lean_unbox_uint64(v_a_4157_);
lean_dec_ref(v_a_4157_);
v_sz_boxed_4167_ = lean_unbox_usize(v_sz_4161_);
lean_dec(v_sz_4161_);
v_i_boxed_4168_ = lean_unbox_usize(v_i_4162_);
lean_dec(v_i_4162_);
v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_8483__boxed_4165_, v_a_8484__boxed_4166_, v_c_4158_, v_numDigits_4159_, v_as_4160_, v_sz_boxed_4167_, v_i_boxed_4168_, v_b_4163_);
lean_dec_ref(v_as_4160_);
lean_dec_ref(v_c_4158_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4174_, lean_object* v_candidates_x3f_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___f_4187_; lean_object* v___x_4188_; 
v___f_4187_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4188_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4187_, v_candidates_x3f_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v_candidates_4190_; lean_object* v_numDigits_4191_; lean_object* v___x_4192_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v_candidates_4190_ = lean_ctor_get(v_a_4189_, 0);
lean_inc_ref(v_candidates_4190_);
v_numDigits_4191_ = lean_ctor_get(v_a_4189_, 1);
lean_inc(v_numDigits_4191_);
lean_dec(v_a_4189_);
v___x_4192_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4174_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint64_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; size_t v_sz_4201_; size_t v___x_4202_; uint64_t v___x_4203_; lean_object* v___x_4204_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = lean_unsigned_to_nat(64u);
v___x_4195_ = lean_unsigned_to_nat(4u);
v___x_4196_ = lean_nat_mul(v___x_4195_, v_numDigits_4191_);
v___x_4197_ = lean_nat_sub(v___x_4194_, v___x_4196_);
lean_dec(v___x_4196_);
v___x_4198_ = lean_uint64_of_nat(v___x_4197_);
lean_dec(v___x_4197_);
v___x_4199_ = lean_unsigned_to_nat(0u);
v___x_4200_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4201_ = lean_array_size(v_candidates_4190_);
v___x_4202_ = ((size_t)0ULL);
v___x_4203_ = lean_unbox_uint64(v_a_4193_);
lean_inc(v_numDigits_4191_);
v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4198_, v___x_4203_, v_c_4174_, v_numDigits_4191_, v_candidates_4190_, v_sz_4201_, v___x_4202_, v___x_4200_);
lean_dec_ref(v_candidates_4190_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4219_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v_fst_4209_; 
v_fst_4209_ = lean_ctor_get(v_a_4205_, 0);
lean_inc(v_fst_4209_);
lean_dec(v_a_4205_);
if (lean_obj_tag(v_fst_4209_) == 0)
{
lean_object* v___x_4210_; uint64_t v___x_4211_; lean_object* v___x_4213_; 
v___x_4210_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4210_, 0, v_numDigits_4191_);
lean_ctor_set(v___x_4210_, 1, v___x_4199_);
v___x_4211_ = lean_unbox_uint64(v_a_4193_);
lean_dec(v_a_4193_);
lean_ctor_set_uint64(v___x_4210_, sizeof(void*)*2, v___x_4211_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4210_);
v___x_4213_ = v___x_4207_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4210_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
else
{
lean_object* v_val_4215_; lean_object* v___x_4217_; 
lean_dec(v_a_4193_);
lean_dec(v_numDigits_4191_);
v_val_4215_ = lean_ctor_get(v_fst_4209_, 0);
lean_inc(v_val_4215_);
lean_dec_ref_known(v_fst_4209_, 1);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_val_4215_);
v___x_4217_ = v___x_4207_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_val_4215_);
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
lean_dec(v_a_4193_);
lean_dec(v_numDigits_4191_);
v_a_4220_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4204_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4204_);
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
lean_dec(v_numDigits_4191_);
lean_dec_ref(v_candidates_4190_);
v_a_4228_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4192_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4192_);
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
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4188_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4188_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4244_, lean_object* v_candidates_x3f_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4244_, v_candidates_x3f_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec(v_a_4246_);
lean_dec_ref(v_c_4244_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4258_, uint64_t v_a_4259_, lean_object* v_c_4260_, lean_object* v_numDigits_4261_, lean_object* v_as_4262_, size_t v_sz_4263_, size_t v_i_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4258_, v_a_4259_, v_c_4260_, v_numDigits_4261_, v_as_4262_, v_sz_4263_, v_i_4264_, v_b_4265_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4278_ = _args[0];
lean_object* v_a_4279_ = _args[1];
lean_object* v_c_4280_ = _args[2];
lean_object* v_numDigits_4281_ = _args[3];
lean_object* v_as_4282_ = _args[4];
lean_object* v_sz_4283_ = _args[5];
lean_object* v_i_4284_ = _args[6];
lean_object* v_b_4285_ = _args[7];
lean_object* v___y_4286_ = _args[8];
lean_object* v___y_4287_ = _args[9];
lean_object* v___y_4288_ = _args[10];
lean_object* v___y_4289_ = _args[11];
lean_object* v___y_4290_ = _args[12];
lean_object* v___y_4291_ = _args[13];
lean_object* v___y_4292_ = _args[14];
lean_object* v___y_4293_ = _args[15];
lean_object* v___y_4294_ = _args[16];
lean_object* v___y_4295_ = _args[17];
lean_object* v___y_4296_ = _args[18];
_start:
{
uint64_t v___x_8682__boxed_4297_; uint64_t v_a_8683__boxed_4298_; size_t v_sz_boxed_4299_; size_t v_i_boxed_4300_; lean_object* v_res_4301_; 
v___x_8682__boxed_4297_ = lean_unbox_uint64(v___x_4278_);
lean_dec_ref(v___x_4278_);
v_a_8683__boxed_4298_ = lean_unbox_uint64(v_a_4279_);
lean_dec_ref(v_a_4279_);
v_sz_boxed_4299_ = lean_unbox_usize(v_sz_4283_);
lean_dec(v_sz_4283_);
v_i_boxed_4300_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_8682__boxed_4297_, v_a_8683__boxed_4298_, v_c_4280_, v_numDigits_4281_, v_as_4282_, v_sz_boxed_4299_, v_i_boxed_4300_, v_b_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v_as_4282_);
lean_dec_ref(v_c_4280_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v_numDigits_4329_; uint64_t v_anchor_4330_; lean_object* v_ordinal_4331_; lean_object* v___x_4332_; 
v_numDigits_4329_ = lean_ctor_get(v_info_4326_, 0);
v_anchor_4330_ = lean_ctor_get_uint64(v_info_4326_, sizeof(void*)*2);
v_ordinal_4331_ = lean_ctor_get(v_info_4326_, 1);
v___x_4332_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4329_, v_anchor_4330_, v_a_4327_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4369_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4369_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4369_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = lean_nat_dec_eq(v_ordinal_4331_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v_ref_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
v_ref_4339_ = lean_ctor_get(v_a_4327_, 5);
v___x_4340_ = l_Lean_SourceInfo_fromRef(v_ref_4339_, v___x_4338_);
v___x_4341_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4342_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4340_, 3);
v___x_4343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4340_);
lean_ctor_set(v___x_4343_, 1, v___x_4341_);
v___x_4344_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4345_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4340_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v___x_4347_ = lean_unsigned_to_nat(1u);
v___x_4348_ = lean_nat_add(v_ordinal_4331_, v___x_4347_);
v___x_4349_ = l_Nat_reprFast(v___x_4348_);
v___x_4350_ = lean_box(2);
v___x_4351_ = l_Lean_Syntax_mkNumLit(v___x_4349_, v___x_4350_);
v___x_4352_ = l_Lean_Syntax_node3(v___x_4340_, v___x_4344_, v_a_4333_, v___x_4346_, v___x_4351_);
v___x_4353_ = l_Lean_Syntax_node2(v___x_4340_, v___x_4342_, v___x_4343_, v___x_4352_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4353_);
v___x_4355_ = v___x_4335_;
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
else
{
lean_object* v_ref_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4367_; 
v_ref_4357_ = lean_ctor_get(v_a_4327_, 5);
v___x_4358_ = 0;
v___x_4359_ = l_Lean_SourceInfo_fromRef(v_ref_4357_, v___x_4358_);
v___x_4360_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4361_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4359_, 2);
v___x_4362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4359_);
lean_ctor_set(v___x_4362_, 1, v___x_4360_);
v___x_4363_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4364_ = l_Lean_Syntax_node1(v___x_4359_, v___x_4363_, v_a_4333_);
v___x_4365_ = l_Lean_Syntax_node2(v___x_4359_, v___x_4361_, v___x_4362_, v___x_4364_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4365_);
v___x_4367_ = v___x_4335_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
else
{
return v___x_4332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4370_, v_a_4371_);
lean_dec_ref(v_a_4371_);
lean_dec_ref(v_info_4370_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4374_, v_a_4375_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4379_, v_a_4380_, v_a_4381_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec_ref(v_info_4379_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_p_4403_; lean_object* v___x_4406_; 
lean_inc_ref(v_proof_4396_);
v___x_4406_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4396_, v_a_4398_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4445_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4445_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4445_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = l_Lean_Expr_cleanupAnnotations(v_a_4407_);
v___x_4428_ = l_Lean_Expr_isApp(v___x_4427_);
if (v___x_4428_ == 0)
{
lean_dec_ref(v___x_4427_);
v___y_4412_ = v_a_4397_;
v___y_4413_ = v_a_4398_;
v___y_4414_ = v_a_4399_;
v___y_4415_ = v_a_4400_;
goto v___jp_4411_;
}
else
{
lean_object* v_arg_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; 
v_arg_4429_ = lean_ctor_get(v___x_4427_, 1);
lean_inc_ref(v_arg_4429_);
v___x_4430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4427_);
v___x_4431_ = l_Lean_Expr_isApp(v___x_4430_);
if (v___x_4431_ == 0)
{
lean_dec_ref(v___x_4430_);
lean_dec_ref(v_arg_4429_);
v___y_4412_ = v_a_4397_;
v___y_4413_ = v_a_4398_;
v___y_4414_ = v_a_4399_;
v___y_4415_ = v_a_4400_;
goto v___jp_4411_;
}
else
{
lean_object* v_arg_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; 
v_arg_4432_ = lean_ctor_get(v___x_4430_, 1);
lean_inc_ref(v_arg_4432_);
v___x_4433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4430_);
v___x_4434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4435_ = l_Lean_Expr_isConstOf(v___x_4433_, v___x_4434_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
lean_dec_ref(v_arg_4432_);
v___x_4436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4437_ = l_Lean_Expr_isConstOf(v___x_4433_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4439_ = l_Lean_Expr_isConstOf(v___x_4433_, v___x_4438_);
lean_dec_ref(v___x_4433_);
if (v___x_4439_ == 0)
{
lean_dec_ref(v_arg_4429_);
v___y_4412_ = v_a_4397_;
v___y_4413_ = v_a_4398_;
v___y_4414_ = v_a_4399_;
v___y_4415_ = v_a_4400_;
goto v___jp_4411_;
}
else
{
lean_del_object(v___x_4409_);
lean_dec_ref(v_proof_4396_);
v_p_4403_ = v_arg_4429_;
goto v___jp_4402_;
}
}
else
{
lean_dec_ref(v___x_4433_);
lean_del_object(v___x_4409_);
lean_dec_ref(v_proof_4396_);
v_p_4403_ = v_arg_4429_;
goto v___jp_4402_;
}
}
else
{
uint8_t v___x_4440_; 
lean_dec_ref(v___x_4433_);
lean_del_object(v___x_4409_);
lean_dec_ref(v_proof_4396_);
v___x_4440_ = l_Lean_Expr_isFalse(v_arg_4432_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_dec_ref(v_arg_4429_);
v___x_4441_ = lean_box(0);
v___x_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
return v___x_4442_;
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4443_, 0, v_arg_4429_);
v___x_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
return v___x_4444_;
}
}
}
}
v___jp_4411_:
{
if (lean_obj_tag(v_proof_4396_) == 6)
{
lean_object* v_body_4416_; uint8_t v___x_4417_; 
v_body_4416_ = lean_ctor_get(v_proof_4396_, 2);
lean_inc_ref(v_body_4416_);
lean_dec_ref_known(v_proof_4396_, 3);
v___x_4417_ = l_Lean_Expr_hasLooseBVars(v_body_4416_);
if (v___x_4417_ == 0)
{
lean_del_object(v___x_4409_);
v_proof_4396_ = v_body_4416_;
v_a_4397_ = v___y_4412_;
v_a_4398_ = v___y_4413_;
v_a_4399_ = v___y_4414_;
v_a_4400_ = v___y_4415_;
goto _start;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
lean_dec_ref(v_body_4416_);
v___x_4419_ = lean_box(0);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4419_);
v___x_4421_ = v___x_4409_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
else
{
lean_object* v___x_4423_; lean_object* v___x_4425_; 
lean_dec_ref(v_proof_4396_);
v___x_4423_ = lean_box(0);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4423_);
v___x_4425_ = v___x_4409_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec_ref(v_proof_4396_);
v_a_4446_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4406_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4406_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
v___jp_4402_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4404_, 0, v_p_4403_);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v___x_4464_; 
v___x_4464_ = l_Lean_Expr_hasMVar(v_e_4461_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; 
v___x_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_e_4461_);
return v___x_4465_;
}
else
{
lean_object* v___x_4466_; lean_object* v_mctx_4467_; lean_object* v___x_4468_; lean_object* v_fst_4469_; lean_object* v_snd_4470_; lean_object* v___x_4471_; lean_object* v_cache_4472_; lean_object* v_zetaDeltaFVarIds_4473_; lean_object* v_postponed_4474_; lean_object* v_diag_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4484_; 
v___x_4466_ = lean_st_ref_get(v___y_4462_);
v_mctx_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc_ref(v_mctx_4467_);
lean_dec(v___x_4466_);
v___x_4468_ = l_Lean_instantiateMVarsCore(v_mctx_4467_, v_e_4461_);
v_fst_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_fst_4469_);
v_snd_4470_ = lean_ctor_get(v___x_4468_, 1);
lean_inc(v_snd_4470_);
lean_dec_ref(v___x_4468_);
v___x_4471_ = lean_st_ref_take(v___y_4462_);
v_cache_4472_ = lean_ctor_get(v___x_4471_, 1);
v_zetaDeltaFVarIds_4473_ = lean_ctor_get(v___x_4471_, 2);
v_postponed_4474_ = lean_ctor_get(v___x_4471_, 3);
v_diag_4475_ = lean_ctor_get(v___x_4471_, 4);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; 
v_unused_4485_ = lean_ctor_get(v___x_4471_, 0);
lean_dec(v_unused_4485_);
v___x_4477_ = v___x_4471_;
v_isShared_4478_ = v_isSharedCheck_4484_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_diag_4475_);
lean_inc(v_postponed_4474_);
lean_inc(v_zetaDeltaFVarIds_4473_);
lean_inc(v_cache_4472_);
lean_dec(v___x_4471_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4484_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v_snd_4470_);
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_snd_4470_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_cache_4472_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v_zetaDeltaFVarIds_4473_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v_postponed_4474_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v_diag_4475_);
v___x_4480_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = lean_st_ref_set(v___y_4462_, v___x_4480_);
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v_fst_4469_);
return v___x_4482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4486_, v___y_4487_);
lean_dec(v___y_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4490_, v___y_4492_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4504_, v_x_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
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
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
v_a_4520_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4511_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4511_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4528_, lean_object* v_x_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4528_, v_x_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4536_, lean_object* v_mvarId_4537_, lean_object* v_x_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4537_, v_x_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4545_, lean_object* v_mvarId_4546_, lean_object* v_x_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4545_, v_mvarId_4546_, v_x_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4571_; 
v___x_4560_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4554_, v___y_4556_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4571_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
uint8_t v___x_4565_; 
v___x_4565_ = l_Lean_Expr_hasSyntheticSorry(v_a_4561_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_del_object(v___x_4563_);
v___x_4566_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4561_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
lean_dec(v_a_4561_);
v___x_4567_ = lean_box(0);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4567_);
v___x_4569_ = v___x_4563_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; lean_object* v___f_4586_; lean_object* v___x_4587_; 
lean_inc(v_mvarId_4579_);
v___x_4585_ = l_Lean_mkMVar(v_mvarId_4579_);
v___f_4586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4586_, 0, v___x_4585_);
v___x_4587_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4579_, v___f_4586_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4616_){
_start:
{
if (lean_obj_tag(v_x_4616_) == 0)
{
uint8_t v___x_4617_; 
v___x_4617_ = 1;
return v___x_4617_;
}
else
{
lean_object* v_head_4618_; lean_object* v_tail_4619_; lean_object* v___x_4620_; uint8_t v___x_4621_; 
v_head_4618_ = lean_ctor_get(v_x_4616_, 0);
lean_inc_n(v_head_4618_, 2);
v_tail_4619_ = lean_ctor_get(v_x_4616_, 1);
lean_inc(v_tail_4619_);
lean_dec_ref_known(v_x_4616_, 2);
v___x_4620_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4621_ = l_Lean_Syntax_isOfKind(v_head_4618_, v___x_4620_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4622_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4618_);
v___x_4623_ = l_Lean_Syntax_isOfKind(v_head_4618_, v___x_4622_);
if (v___x_4623_ == 0)
{
lean_dec(v_head_4618_);
v_x_4616_ = v_tail_4619_;
goto _start;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4625_ = lean_unsigned_to_nat(1u);
v___x_4626_ = l_Lean_Syntax_getArg(v_head_4618_, v___x_4625_);
lean_dec(v_head_4618_);
v___x_4627_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4628_ = l_Lean_Syntax_isOfKind(v___x_4626_, v___x_4627_);
if (v___x_4628_ == 0)
{
v_x_4616_ = v_tail_4619_;
goto _start;
}
else
{
if (v___x_4621_ == 0)
{
lean_dec(v_tail_4619_);
return v___x_4621_;
}
else
{
v_x_4616_ = v_tail_4619_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4631_ = lean_unsigned_to_nat(3u);
v___x_4632_ = l_Lean_Syntax_getArg(v_head_4618_, v___x_4631_);
lean_dec(v_head_4618_);
v___x_4633_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4634_ = l_Lean_Syntax_isOfKind(v___x_4632_, v___x_4633_);
if (v___x_4634_ == 0)
{
v_x_4616_ = v_tail_4619_;
goto _start;
}
else
{
uint8_t v___x_4636_; 
lean_dec(v_tail_4619_);
v___x_4636_ = 0;
return v___x_4636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4637_){
_start:
{
uint8_t v_res_4638_; lean_object* v_r_4639_; 
v_res_4638_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4637_);
v_r_4639_ = lean_box(v_res_4638_);
return v_r_4639_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4640_){
_start:
{
uint8_t v___x_4641_; 
v___x_4641_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4642_){
_start:
{
uint8_t v_res_4643_; lean_object* v_r_4644_; 
v_res_4643_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4642_);
v_r_4644_ = lean_box(v_res_4643_);
return v_r_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4660_, lean_object* v_a_4661_){
_start:
{
if (lean_obj_tag(v_seq_4660_) == 0)
{
lean_object* v_ref_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_ref_4663_ = lean_ctor_get(v_a_4661_, 5);
v___x_4664_ = 0;
v___x_4665_ = l_Lean_SourceInfo_fromRef(v_ref_4663_, v___x_4664_);
v___x_4666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4665_);
v___x_4668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4665_);
lean_ctor_set(v___x_4668_, 1, v___x_4666_);
v___x_4669_ = l_Lean_Syntax_node1(v___x_4665_, v___x_4667_, v___x_4668_);
v___x_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4669_);
return v___x_4670_;
}
else
{
lean_object* v_tail_4671_; 
v_tail_4671_ = lean_ctor_get(v_seq_4660_, 1);
if (lean_obj_tag(v_tail_4671_) == 0)
{
lean_object* v_head_4672_; lean_object* v___x_4673_; 
v_head_4672_ = lean_ctor_get(v_seq_4660_, 0);
lean_inc(v_head_4672_);
lean_dec_ref_known(v_seq_4660_, 2);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v_head_4672_);
return v___x_4673_;
}
else
{
lean_object* v_head_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4696_; 
lean_inc(v_tail_4671_);
v_head_4674_ = lean_ctor_get(v_seq_4660_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_seq_4660_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; 
v_unused_4697_ = lean_ctor_get(v_seq_4660_, 1);
lean_dec(v_unused_4697_);
v___x_4676_ = v_seq_4660_;
v_isShared_4677_ = v_isSharedCheck_4696_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_head_4674_);
lean_dec(v_seq_4660_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4696_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4695_; 
v___x_4678_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4671_, v_a_4661_);
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4695_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4695_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v_ref_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v_ref_4683_ = lean_ctor_get(v_a_4661_, 5);
v___x_4684_ = 0;
v___x_4685_ = l_Lean_SourceInfo_fromRef(v_ref_4683_, v___x_4684_);
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4685_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set_tag(v___x_4676_, 2);
lean_ctor_set(v___x_4676_, 1, v___x_4687_);
lean_ctor_set(v___x_4676_, 0, v___x_4685_);
v___x_4689_ = v___x_4676_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4690_ = l_Lean_Syntax_node3(v___x_4685_, v___x_4686_, v_head_4674_, v___x_4689_, v_a_4679_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4690_);
v___x_4692_ = v___x_4681_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4698_, v_a_4699_);
lean_dec_ref(v_a_4699_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4702_, v_a_4703_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4707_, v_a_4708_, v_a_4709_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4712_, lean_object* v_seq_4713_, lean_object* v_a_4714_){
_start:
{
if (lean_obj_tag(v_seq_4713_) == 0)
{
lean_object* v___x_4716_; 
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v_cases_4712_);
return v___x_4716_;
}
else
{
lean_object* v___x_4717_; lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4732_; 
v___x_4717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4713_, v_a_4714_);
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4720_ = v___x_4717_;
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4717_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_ref_4722_; uint8_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
v_ref_4722_ = lean_ctor_get(v_a_4714_, 5);
v___x_4723_ = 0;
v___x_4724_ = l_Lean_SourceInfo_fromRef(v_ref_4722_, v___x_4723_);
v___x_4725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4724_);
v___x_4727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4724_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
v___x_4728_ = l_Lean_Syntax_node3(v___x_4724_, v___x_4725_, v_cases_4712_, v___x_4727_, v_a_4718_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 0, v___x_4728_);
v___x_4730_ = v___x_4720_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4733_, lean_object* v_seq_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4733_, v_seq_4734_, v_a_4735_);
lean_dec_ref(v_a_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4738_, lean_object* v_seq_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4738_, v_seq_4739_, v_a_4740_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4744_, lean_object* v_seq_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4744_, v_seq_4745_, v_a_4746_, v_a_4747_);
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
return v_res_4749_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4750_, lean_object* v_x_4751_){
_start:
{
if (lean_obj_tag(v_x_4750_) == 0)
{
if (lean_obj_tag(v_x_4751_) == 0)
{
uint8_t v___x_4752_; 
v___x_4752_ = 1;
return v___x_4752_;
}
else
{
uint8_t v___x_4753_; 
lean_dec_ref_known(v_x_4751_, 2);
v___x_4753_ = 0;
return v___x_4753_;
}
}
else
{
if (lean_obj_tag(v_x_4751_) == 0)
{
uint8_t v___x_4754_; 
lean_dec_ref_known(v_x_4750_, 2);
v___x_4754_ = 0;
return v___x_4754_;
}
else
{
lean_object* v_head_4755_; lean_object* v_tail_4756_; lean_object* v_head_4757_; lean_object* v_tail_4758_; uint8_t v___x_4759_; 
v_head_4755_ = lean_ctor_get(v_x_4750_, 0);
lean_inc(v_head_4755_);
v_tail_4756_ = lean_ctor_get(v_x_4750_, 1);
lean_inc(v_tail_4756_);
lean_dec_ref_known(v_x_4750_, 2);
v_head_4757_ = lean_ctor_get(v_x_4751_, 0);
lean_inc(v_head_4757_);
v_tail_4758_ = lean_ctor_get(v_x_4751_, 1);
lean_inc(v_tail_4758_);
lean_dec_ref_known(v_x_4751_, 2);
v___x_4759_ = l_Lean_Syntax_structEq(v_head_4755_, v_head_4757_);
if (v___x_4759_ == 0)
{
lean_dec(v_tail_4758_);
lean_dec(v_tail_4756_);
return v___x_4759_;
}
else
{
v_x_4750_ = v_tail_4756_;
v_x_4751_ = v_tail_4758_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4761_, lean_object* v_x_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4761_, v_x_4762_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4765_, uint8_t v___x_4766_, lean_object* v_as_4767_, size_t v_i_4768_, size_t v_stop_4769_){
_start:
{
uint8_t v___x_4770_; 
v___x_4770_ = lean_usize_dec_eq(v_i_4768_, v_stop_4769_);
if (v___x_4770_ == 0)
{
uint8_t v___x_4771_; uint8_t v___y_4773_; lean_object* v___x_4777_; uint8_t v___x_4778_; 
v___x_4771_ = 1;
v___x_4777_ = lean_array_uget_borrowed(v_as_4767_, v_i_4768_);
lean_inc(v_alt_4765_);
lean_inc(v___x_4777_);
v___x_4778_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4777_, v_alt_4765_);
if (v___x_4778_ == 0)
{
v___y_4773_ = v___x_4766_;
goto v___jp_4772_;
}
else
{
v___y_4773_ = v___x_4770_;
goto v___jp_4772_;
}
v___jp_4772_:
{
if (v___y_4773_ == 0)
{
size_t v___x_4774_; size_t v___x_4775_; 
v___x_4774_ = ((size_t)1ULL);
v___x_4775_ = lean_usize_add(v_i_4768_, v___x_4774_);
v_i_4768_ = v___x_4775_;
goto _start;
}
else
{
lean_dec(v_alt_4765_);
return v___x_4771_;
}
}
}
else
{
uint8_t v___x_4779_; 
lean_dec(v_alt_4765_);
v___x_4779_ = 0;
return v___x_4779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4780_, lean_object* v___x_4781_, lean_object* v_as_4782_, lean_object* v_i_4783_, lean_object* v_stop_4784_){
_start:
{
uint8_t v___x_359__boxed_4785_; size_t v_i_boxed_4786_; size_t v_stop_boxed_4787_; uint8_t v_res_4788_; lean_object* v_r_4789_; 
v___x_359__boxed_4785_ = lean_unbox(v___x_4781_);
v_i_boxed_4786_ = lean_unbox_usize(v_i_4783_);
lean_dec(v_i_4783_);
v_stop_boxed_4787_ = lean_unbox_usize(v_stop_4784_);
lean_dec(v_stop_4784_);
v_res_4788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4780_, v___x_359__boxed_4785_, v_as_4782_, v_i_boxed_4786_, v_stop_boxed_4787_);
lean_dec_ref(v_as_4782_);
v_r_4789_ = lean_box(v_res_4788_);
return v_r_4789_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4790_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4791_ = lean_unsigned_to_nat(0u);
v___x_4792_ = lean_array_get_size(v_alts_4790_);
v___x_4793_ = lean_nat_dec_lt(v___x_4791_, v___x_4792_);
if (v___x_4793_ == 0)
{
uint8_t v___x_4794_; 
v___x_4794_ = 1;
return v___x_4794_;
}
else
{
lean_object* v_alt_4795_; uint8_t v___x_4796_; 
v_alt_4795_ = lean_array_fget_borrowed(v_alts_4790_, v___x_4791_);
lean_inc(v_alt_4795_);
v___x_4796_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4795_);
if (v___x_4796_ == 0)
{
return v___x_4796_;
}
else
{
if (v___x_4793_ == 0)
{
return v___x_4796_;
}
else
{
if (v___x_4793_ == 0)
{
return v___x_4796_;
}
else
{
size_t v___x_4797_; size_t v___x_4798_; uint8_t v___x_4799_; 
v___x_4797_ = ((size_t)0ULL);
v___x_4798_ = lean_usize_of_nat(v___x_4792_);
lean_inc(v_alt_4795_);
v___x_4799_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4795_, v___x_4796_, v_alts_4790_, v___x_4797_, v___x_4798_);
if (v___x_4799_ == 0)
{
return v___x_4796_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = 0;
return v___x_4800_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4801_){
_start:
{
uint8_t v_res_4802_; lean_object* v_r_4803_; 
v_res_4802_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4801_);
lean_dec_ref(v_alts_4801_);
v_r_4803_ = lean_box(v_res_4802_);
return v_r_4803_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4811_){
_start:
{
if (lean_obj_tag(v_alt_4811_) == 1)
{
lean_object* v_tail_4812_; 
v_tail_4812_ = lean_ctor_get(v_alt_4811_, 1);
if (lean_obj_tag(v_tail_4812_) == 0)
{
lean_object* v_head_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v_head_4813_ = lean_ctor_get(v_alt_4811_, 0);
lean_inc(v_head_4813_);
lean_dec_ref_known(v_alt_4811_, 2);
v___x_4814_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4815_ = l_Lean_Syntax_isOfKind(v_head_4813_, v___x_4814_);
return v___x_4815_;
}
else
{
uint8_t v___x_4816_; 
lean_dec_ref_known(v_alt_4811_, 2);
v___x_4816_ = 0;
return v___x_4816_;
}
}
else
{
uint8_t v___x_4817_; 
lean_dec(v_alt_4811_);
v___x_4817_ = 0;
return v___x_4817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4818_){
_start:
{
uint8_t v_res_4819_; lean_object* v_r_4820_; 
v_res_4819_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4818_);
v_r_4820_ = lean_box(v_res_4819_);
return v_r_4820_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4821_, lean_object* v_x_4822_, lean_object* v___y_4823_){
_start:
{
if (lean_obj_tag(v_x_4821_) == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = l_List_reverse___redArg(v_x_4822_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
else
{
lean_object* v_head_4827_; lean_object* v_tail_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4846_; 
v_head_4827_ = lean_ctor_get(v_x_4821_, 0);
v_tail_4828_ = lean_ctor_get(v_x_4821_, 1);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_x_4821_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4830_ = v_x_4821_;
v_isShared_4831_ = v_isSharedCheck_4846_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_tail_4828_);
lean_inc(v_head_4827_);
lean_dec(v_x_4821_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4846_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4827_, v___y_4823_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
lean_inc(v_a_4833_);
lean_dec_ref_known(v___x_4832_, 1);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 1, v_x_4822_);
lean_ctor_set(v___x_4830_, 0, v_a_4833_);
v___x_4835_ = v___x_4830_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4833_);
lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_x_4822_);
v___x_4835_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
v_x_4821_ = v_tail_4828_;
v_x_4822_ = v___x_4835_;
goto _start;
}
}
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
lean_del_object(v___x_4830_);
lean_dec(v_tail_4828_);
lean_dec(v_x_4822_);
v_a_4838_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4832_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4832_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4847_, lean_object* v_x_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4847_, v_x_4848_, v___y_4849_);
lean_dec_ref(v___y_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4852_, lean_object* v_alts_4853_, uint8_t v_compress_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_seq_4859_; 
if (v_compress_4854_ == 0)
{
goto v___jp_4862_;
}
else
{
uint8_t v___x_4872_; 
v___x_4872_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4853_);
if (v___x_4872_ == 0)
{
goto v___jp_4862_;
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; 
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = lean_array_get_size(v_alts_4853_);
v___x_4875_ = lean_nat_dec_lt(v___x_4873_, v___x_4874_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec_ref(v_alts_4853_);
v___x_4876_ = lean_box(0);
v___x_4877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4877_, 0, v_cases_4852_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; lean_object* v_firstAlt_4880_; uint8_t v___x_4881_; 
v___x_4879_ = lean_box(0);
v_firstAlt_4880_ = lean_array_get(v___x_4879_, v_alts_4853_, v___x_4873_);
lean_dec_ref(v_alts_4853_);
lean_inc(v_firstAlt_4880_);
v___x_4881_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4880_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4891_; 
v___x_4882_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4852_, v_firstAlt_4880_, v_a_4855_);
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4885_ = v___x_4882_;
v_isShared_4886_ = v_isSharedCheck_4891_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4891_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4887_, 0, v_a_4883_);
lean_ctor_set(v___x_4887_, 1, v___x_4879_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v___x_4887_);
v___x_4889_ = v___x_4885_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_object* v___x_4892_; 
lean_dec(v_cases_4852_);
v___x_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_firstAlt_4880_);
return v___x_4892_;
}
}
}
}
v___jp_4858_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4860_, 0, v_cases_4852_);
lean_ctor_set(v___x_4860_, 1, v_seq_4859_);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
return v___x_4861_;
}
v___jp_4862_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4863_ = lean_array_get_size(v_alts_4853_);
v___x_4864_ = lean_unsigned_to_nat(1u);
v___x_4865_ = lean_nat_dec_eq(v___x_4863_, v___x_4864_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4866_ = lean_array_to_list(v_alts_4853_);
v___x_4867_ = lean_box(0);
v___x_4868_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4866_, v___x_4867_, v_a_4855_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v___x_4868_, 1);
v_seq_4859_ = v_a_4869_;
goto v___jp_4858_;
}
else
{
lean_dec(v_cases_4852_);
return v___x_4868_;
}
}
else
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = lean_unsigned_to_nat(0u);
v___x_4871_ = lean_array_fget(v_alts_4853_, v___x_4870_);
lean_dec_ref(v_alts_4853_);
v_seq_4859_ = v___x_4871_;
goto v___jp_4858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4893_, lean_object* v_alts_4894_, lean_object* v_compress_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
uint8_t v_compress_boxed_4899_; lean_object* v_res_4900_; 
v_compress_boxed_4899_ = lean_unbox(v_compress_4895_);
v_res_4900_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4893_, v_alts_4894_, v_compress_boxed_4899_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4901_, lean_object* v_x_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4901_, v_x_4902_, v___y_4903_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4907_, v_x_4908_, v___y_4909_, v___y_4910_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v___x_4916_; lean_object* v_env_4917_; uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4916_ = lean_st_ref_get(v___y_4914_);
v_env_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc_ref(v_env_4917_);
lean_dec(v___x_4916_);
v___x_4918_ = l_Lean_Meta_isMatcherAppCore(v_env_4917_, v_e_4913_);
v___x_4919_ = lean_box(v___x_4918_);
v___x_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4921_, v___y_4922_);
lean_dec(v___y_4922_);
lean_dec_ref(v_e_4921_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4925_, v___y_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v_e_4938_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v___x_4962_; 
lean_inc(v___y_4956_);
lean_inc_ref(v___y_4955_);
lean_inc(v___y_4954_);
lean_inc_ref(v___y_4953_);
lean_inc(v___y_4952_);
v___x_4962_ = lean_apply_10(v_x_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, lean_box(0));
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4975_, lean_object* v_x_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v___f_4987_; lean_object* v___x_4988_; 
lean_inc(v___y_4981_);
lean_inc_ref(v___y_4980_);
lean_inc(v___y_4979_);
lean_inc_ref(v___y_4978_);
lean_inc(v___y_4977_);
v___f_4987_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4987_, 0, v_x_4976_);
lean_closure_set(v___f_4987_, 1, v___y_4977_);
lean_closure_set(v___f_4987_, 2, v___y_4978_);
lean_closure_set(v___f_4987_, 3, v___y_4979_);
lean_closure_set(v___f_4987_, 4, v___y_4980_);
lean_closure_set(v___f_4987_, 5, v___y_4981_);
v___x_4988_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4975_, v___f_4987_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
if (lean_obj_tag(v___x_4988_) == 0)
{
return v___x_4988_;
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4988_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4988_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4997_, lean_object* v_x_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4997_, v_x_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5010_, lean_object* v_mvarId_5011_, lean_object* v_x_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5011_, v_x_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5024_, lean_object* v_mvarId_5025_, lean_object* v_x_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5024_, v_mvarId_5025_, v_x_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5038_, lean_object* v___y_5039_){
_start:
{
uint8_t v___x_5041_; 
v___x_5041_ = l_Lean_Expr_hasMVar(v_e_5038_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; 
v___x_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5042_, 0, v_e_5038_);
return v___x_5042_;
}
else
{
lean_object* v___x_5043_; lean_object* v_mctx_5044_; lean_object* v___x_5045_; lean_object* v_fst_5046_; lean_object* v_snd_5047_; lean_object* v___x_5048_; lean_object* v_cache_5049_; lean_object* v_zetaDeltaFVarIds_5050_; lean_object* v_postponed_5051_; lean_object* v_diag_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5061_; 
v___x_5043_ = lean_st_ref_get(v___y_5039_);
v_mctx_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc_ref(v_mctx_5044_);
lean_dec(v___x_5043_);
v___x_5045_ = l_Lean_instantiateMVarsCore(v_mctx_5044_, v_e_5038_);
v_fst_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_fst_5046_);
v_snd_5047_ = lean_ctor_get(v___x_5045_, 1);
lean_inc(v_snd_5047_);
lean_dec_ref(v___x_5045_);
v___x_5048_ = lean_st_ref_take(v___y_5039_);
v_cache_5049_ = lean_ctor_get(v___x_5048_, 1);
v_zetaDeltaFVarIds_5050_ = lean_ctor_get(v___x_5048_, 2);
v_postponed_5051_ = lean_ctor_get(v___x_5048_, 3);
v_diag_5052_ = lean_ctor_get(v___x_5048_, 4);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5061_ == 0)
{
lean_object* v_unused_5062_; 
v_unused_5062_ = lean_ctor_get(v___x_5048_, 0);
lean_dec(v_unused_5062_);
v___x_5054_ = v___x_5048_;
v_isShared_5055_ = v_isSharedCheck_5061_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_diag_5052_);
lean_inc(v_postponed_5051_);
lean_inc(v_zetaDeltaFVarIds_5050_);
lean_inc(v_cache_5049_);
lean_dec(v___x_5048_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5061_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v_snd_5047_);
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_snd_5047_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_cache_5049_);
lean_ctor_set(v_reuseFailAlloc_5060_, 2, v_zetaDeltaFVarIds_5050_);
lean_ctor_set(v_reuseFailAlloc_5060_, 3, v_postponed_5051_);
lean_ctor_set(v_reuseFailAlloc_5060_, 4, v_diag_5052_);
v___x_5057_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_st_ref_set(v___y_5039_, v___x_5057_);
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v_fst_5046_);
return v___x_5059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5063_, v___y_5064_);
lean_dec(v___y_5064_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_){
_start:
{
lean_object* v___x_5078_; 
v___x_5078_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5067_, v___y_5074_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
return v_res_5090_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5093_ = l_Lean_stringToMessageData(v___x_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5094_, lean_object* v_c_5095_, lean_object* v_a_5096_, lean_object* v_numCases_5097_, uint8_t v_isRec_5098_, lean_object* v_anchorInfo_x3f_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v_mvarIds_5112_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5094_, v___y_5100_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___y_5175_; lean_object* v___x_5226_; uint8_t v___y_5228_; uint8_t v___x_5230_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
v___x_5226_ = lean_unsigned_to_nat(1u);
v___x_5230_ = lean_nat_dec_lt(v___x_5226_, v_numCases_5097_);
if (v___x_5230_ == 0)
{
v___y_5228_ = v_isRec_5098_;
goto v___jp_5227_;
}
else
{
v___y_5228_ = v___x_5230_;
goto v___jp_5227_;
}
v___jp_5174_:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5176_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5095_);
lean_inc_ref(v___x_5094_);
v___x_5177_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5094_, v___y_5175_, v_numCases_5097_, v___x_5176_, v___y_5103_, v___y_5106_, v___y_5108_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v___x_5178_; 
lean_dec_ref_known(v___x_5177_, 1);
lean_inc_ref(v___x_5094_);
v___x_5178_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5094_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v_options_5179_; uint8_t v_hasTrace_5180_; 
lean_dec_ref_known(v___x_5178_, 1);
v_options_5179_ = lean_ctor_get(v___y_5108_, 2);
v_hasTrace_5180_ = lean_ctor_get_uint8(v_options_5179_, sizeof(void*)*1);
if (v_hasTrace_5180_ == 0)
{
lean_dec(v_a_5173_);
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
v___y_5121_ = v___y_5105_;
v___y_5122_ = v___y_5106_;
v___y_5123_ = v___y_5107_;
v___y_5124_ = v___y_5108_;
v___y_5125_ = v___y_5109_;
goto v___jp_5115_;
}
else
{
lean_object* v_inheritedTraceOptions_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; uint8_t v___x_5184_; 
v_inheritedTraceOptions_5181_ = lean_ctor_get(v___y_5108_, 13);
v___x_5182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5183_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5181_, v_options_5179_, v___x_5183_);
if (v___x_5184_ == 0)
{
lean_dec(v_a_5173_);
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
v___y_5121_ = v___y_5105_;
v___y_5122_ = v___y_5106_;
v___y_5123_ = v___y_5107_;
v___y_5124_ = v___y_5108_;
v___y_5125_ = v___y_5109_;
goto v___jp_5115_;
}
else
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_Meta_Grind_updateLastTag(v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
lean_dec_ref_known(v___x_5185_, 1);
lean_inc_ref(v___x_5094_);
v___x_5186_ = l_Lean_MessageData_ofExpr(v___x_5094_);
v___x_5187_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5186_);
lean_ctor_set(v___x_5188_, 1, v___x_5187_);
v___x_5189_ = l_Nat_reprFast(v_a_5173_);
v___x_5190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5189_);
v___x_5191_ = l_Lean_MessageData_ofFormat(v___x_5190_);
v___x_5192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5188_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5182_, v___x_5192_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_dec_ref_known(v___x_5193_, 1);
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
v___y_5121_ = v___y_5105_;
v___y_5122_ = v___y_5106_;
v___y_5123_ = v___y_5107_;
v___y_5124_ = v___y_5108_;
v___y_5125_ = v___y_5109_;
goto v___jp_5115_;
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_a_5096_);
lean_dec_ref(v_c_5095_);
lean_dec_ref(v___x_5094_);
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5193_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5193_);
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
lean_dec(v_a_5173_);
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_a_5096_);
lean_dec_ref(v_c_5095_);
lean_dec_ref(v___x_5094_);
v_a_5202_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5185_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5185_);
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
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_dec(v_a_5173_);
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_a_5096_);
lean_dec_ref(v_c_5095_);
lean_dec_ref(v___x_5094_);
v_a_5210_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5178_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5178_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_dec(v_a_5173_);
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_a_5096_);
lean_dec_ref(v_c_5095_);
lean_dec_ref(v___x_5094_);
v_a_5218_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5177_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5177_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
v___jp_5227_:
{
if (v___y_5228_ == 0)
{
lean_inc(v_a_5173_);
v___y_5175_ = v_a_5173_;
goto v___jp_5174_;
}
else
{
lean_object* v___x_5229_; 
v___x_5229_ = lean_nat_add(v_a_5173_, v___x_5226_);
v___y_5175_ = v___x_5229_;
goto v___jp_5174_;
}
}
}
else
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_numCases_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v_c_5095_);
lean_dec_ref(v___x_5094_);
v_a_5231_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5172_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5172_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
v___jp_5111_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5113_, 0, v_mvarIds_5112_);
lean_ctor_set(v___x_5113_, 1, v_anchorInfo_x3f_5099_);
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
}
v___jp_5115_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5094_, v___y_5125_);
if (lean_obj_tag(v_c_5095_) == 1)
{
lean_object* v_e_5127_; lean_object* v_binderType_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
lean_dec_ref(v___x_5126_);
lean_dec_ref(v___x_5094_);
v_e_5127_ = lean_ctor_get(v_c_5095_, 0);
lean_inc_ref(v_e_5127_);
lean_dec_ref_known(v_c_5095_, 2);
v_binderType_5128_ = lean_ctor_get(v_e_5127_, 1);
lean_inc_ref(v_binderType_5128_);
lean_dec_ref(v_e_5127_);
v___x_5129_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5128_);
v___x_5130_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5096_, v___x_5129_, v___y_5118_, v___y_5119_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
v_mvarIds_5112_ = v_a_5131_;
goto v___jp_5111_;
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec(v_anchorInfo_x3f_5099_);
v_a_5132_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5130_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5130_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
else
{
lean_object* v_a_5140_; uint8_t v___x_5141_; 
lean_dec_ref(v_c_5095_);
v_a_5140_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5140_);
lean_dec_ref(v___x_5126_);
v___x_5141_ = lean_unbox(v_a_5140_);
lean_dec(v_a_5140_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5094_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5144_; 
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5142_, 1);
v___x_5144_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5096_, v_a_5143_, v___y_5118_, v___y_5119_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v_mvarIds_5112_ = v_a_5145_;
goto v___jp_5111_;
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec(v_anchorInfo_x3f_5099_);
v_a_5146_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5144_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5144_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec(v_anchorInfo_x3f_5099_);
lean_dec(v_a_5096_);
v_a_5154_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5142_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5142_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
lean_object* v___x_5162_; 
v___x_5162_ = l_Lean_Meta_Grind_casesMatch(v_a_5096_, v___x_5094_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v_mvarIds_5112_ = v_a_5163_;
goto v___jp_5111_;
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec(v_anchorInfo_x3f_5099_);
v_a_5164_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5162_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5162_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5239_ = _args[0];
lean_object* v_c_5240_ = _args[1];
lean_object* v_a_5241_ = _args[2];
lean_object* v_numCases_5242_ = _args[3];
lean_object* v_isRec_5243_ = _args[4];
lean_object* v_anchorInfo_x3f_5244_ = _args[5];
lean_object* v___y_5245_ = _args[6];
lean_object* v___y_5246_ = _args[7];
lean_object* v___y_5247_ = _args[8];
lean_object* v___y_5248_ = _args[9];
lean_object* v___y_5249_ = _args[10];
lean_object* v___y_5250_ = _args[11];
lean_object* v___y_5251_ = _args[12];
lean_object* v___y_5252_ = _args[13];
lean_object* v___y_5253_ = _args[14];
lean_object* v___y_5254_ = _args[15];
lean_object* v___y_5255_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5256_; lean_object* v_res_5257_; 
v_isRec_boxed_5256_ = lean_unbox(v_isRec_5243_);
v_res_5257_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5239_, v_c_5240_, v_a_5241_, v_numCases_5242_, v_isRec_boxed_5256_, v_anchorInfo_x3f_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec(v___y_5245_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5258_, uint8_t v_trace_5259_, lean_object* v___f_5260_, lean_object* v_c_5261_, lean_object* v_candidates_x3f_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v___x_5273_; lean_object* v___y_5275_; 
v___x_5273_ = lean_st_mk_ref(v_goal_5258_);
if (v_trace_5259_ == 0)
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
lean_dec(v_candidates_x3f_5262_);
v___x_5294_ = lean_box(0);
lean_inc(v___x_5273_);
v___x_5295_ = lean_apply_12(v___f_5260_, v___x_5294_, v___x_5273_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, lean_box(0));
v___y_5275_ = v___x_5295_;
goto v___jp_5274_;
}
else
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5261_, v_candidates_x3f_5262_, v___x_5273_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_a_5297_);
lean_dec_ref_known(v___x_5296_, 1);
v___x_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5298_, 0, v_a_5297_);
lean_inc(v___x_5273_);
v___x_5299_ = lean_apply_12(v___f_5260_, v___x_5298_, v___x_5273_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, lean_box(0));
v___y_5275_ = v___x_5299_;
goto v___jp_5274_;
}
else
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
lean_dec(v___x_5273_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___f_5260_);
v_a_5300_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5296_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5296_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
v___jp_5274_:
{
if (lean_obj_tag(v___y_5275_) == 0)
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5285_; 
v_a_5276_ = lean_ctor_get(v___y_5275_, 0);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___y_5275_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5278_ = v___y_5275_;
v_isShared_5279_ = v_isSharedCheck_5285_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___y_5275_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5285_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5280_ = lean_st_ref_get(v___x_5273_);
lean_dec(v___x_5273_);
v___x_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5281_, 0, v_a_5276_);
lean_ctor_set(v___x_5281_, 1, v___x_5280_);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 0, v___x_5281_);
v___x_5283_ = v___x_5278_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
lean_dec(v___x_5273_);
v_a_5286_ = lean_ctor_get(v___y_5275_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___y_5275_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___y_5275_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___y_5275_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5308_, lean_object* v_trace_5309_, lean_object* v___f_5310_, lean_object* v_c_5311_, lean_object* v_candidates_x3f_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
uint8_t v_trace_boxed_5323_; lean_object* v_res_5324_; 
v_trace_boxed_5323_ = lean_unbox(v_trace_5309_);
v_res_5324_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5308_, v_trace_boxed_5323_, v___f_5310_, v_c_5311_, v_candidates_x3f_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
lean_dec_ref(v_c_5311_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5325_, lean_object* v_x_5326_, lean_object* v_x_5327_, lean_object* v_x_5328_){
_start:
{
lean_object* v_ks_5329_; lean_object* v_vs_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5354_; 
v_ks_5329_ = lean_ctor_get(v_x_5325_, 0);
v_vs_5330_ = lean_ctor_get(v_x_5325_, 1);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_x_5325_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5332_ = v_x_5325_;
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_vs_5330_);
lean_inc(v_ks_5329_);
lean_dec(v_x_5325_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5354_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5334_; uint8_t v___x_5335_; 
v___x_5334_ = lean_array_get_size(v_ks_5329_);
v___x_5335_ = lean_nat_dec_lt(v_x_5326_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5339_; 
lean_dec(v_x_5326_);
v___x_5336_ = lean_array_push(v_ks_5329_, v_x_5327_);
v___x_5337_ = lean_array_push(v_vs_5330_, v_x_5328_);
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 1, v___x_5337_);
lean_ctor_set(v___x_5332_, 0, v___x_5336_);
v___x_5339_ = v___x_5332_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___x_5337_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
else
{
lean_object* v_k_x27_5341_; uint8_t v___x_5342_; 
v_k_x27_5341_ = lean_array_fget_borrowed(v_ks_5329_, v_x_5326_);
v___x_5342_ = l_Lean_instBEqMVarId_beq(v_x_5327_, v_k_x27_5341_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5344_; 
if (v_isShared_5333_ == 0)
{
v___x_5344_ = v___x_5332_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_ks_5329_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v_vs_5330_);
v___x_5344_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5345_ = lean_unsigned_to_nat(1u);
v___x_5346_ = lean_nat_add(v_x_5326_, v___x_5345_);
lean_dec(v_x_5326_);
v_x_5325_ = v___x_5344_;
v_x_5326_ = v___x_5346_;
goto _start;
}
}
else
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5352_; 
v___x_5349_ = lean_array_fset(v_ks_5329_, v_x_5326_, v_x_5327_);
v___x_5350_ = lean_array_fset(v_vs_5330_, v_x_5326_, v_x_5328_);
lean_dec(v_x_5326_);
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 1, v___x_5350_);
lean_ctor_set(v___x_5332_, 0, v___x_5349_);
v___x_5352_ = v___x_5332_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v___x_5350_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5355_, lean_object* v_k_5356_, lean_object* v_v_5357_){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = lean_unsigned_to_nat(0u);
v___x_5359_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5355_, v___x_5358_, v_k_5356_, v_v_5357_);
return v___x_5359_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5361_, size_t v_x_5362_, size_t v_x_5363_, lean_object* v_x_5364_, lean_object* v_x_5365_){
_start:
{
if (lean_obj_tag(v_x_5361_) == 0)
{
lean_object* v_es_5366_; size_t v___x_5367_; size_t v___x_5368_; lean_object* v_j_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; 
v_es_5366_ = lean_ctor_get(v_x_5361_, 0);
v___x_5367_ = ((size_t)31ULL);
v___x_5368_ = lean_usize_land(v_x_5362_, v___x_5367_);
v_j_5369_ = lean_usize_to_nat(v___x_5368_);
v___x_5370_ = lean_array_get_size(v_es_5366_);
v___x_5371_ = lean_nat_dec_lt(v_j_5369_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_dec(v_j_5369_);
lean_dec(v_x_5365_);
lean_dec(v_x_5364_);
return v_x_5361_;
}
else
{
lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5410_; 
lean_inc_ref(v_es_5366_);
v_isSharedCheck_5410_ = !lean_is_exclusive(v_x_5361_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; 
v_unused_5411_ = lean_ctor_get(v_x_5361_, 0);
lean_dec(v_unused_5411_);
v___x_5373_ = v_x_5361_;
v_isShared_5374_ = v_isSharedCheck_5410_;
goto v_resetjp_5372_;
}
else
{
lean_dec(v_x_5361_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5410_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v_v_5375_; lean_object* v___x_5376_; lean_object* v_xs_x27_5377_; lean_object* v___y_5379_; 
v_v_5375_ = lean_array_fget(v_es_5366_, v_j_5369_);
v___x_5376_ = lean_box(0);
v_xs_x27_5377_ = lean_array_fset(v_es_5366_, v_j_5369_, v___x_5376_);
switch(lean_obj_tag(v_v_5375_))
{
case 0:
{
lean_object* v_key_5384_; lean_object* v_val_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5395_; 
v_key_5384_ = lean_ctor_get(v_v_5375_, 0);
v_val_5385_ = lean_ctor_get(v_v_5375_, 1);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_v_5375_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5387_ = v_v_5375_;
v_isShared_5388_ = v_isSharedCheck_5395_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_val_5385_);
lean_inc(v_key_5384_);
lean_dec(v_v_5375_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5395_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
uint8_t v___x_5389_; 
v___x_5389_ = l_Lean_instBEqMVarId_beq(v_x_5364_, v_key_5384_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5390_; lean_object* v___x_5391_; 
lean_del_object(v___x_5387_);
v___x_5390_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5384_, v_val_5385_, v_x_5364_, v_x_5365_);
v___x_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5390_);
v___y_5379_ = v___x_5391_;
goto v___jp_5378_;
}
else
{
lean_object* v___x_5393_; 
lean_dec(v_val_5385_);
lean_dec(v_key_5384_);
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v_x_5365_);
lean_ctor_set(v___x_5387_, 0, v_x_5364_);
v___x_5393_ = v___x_5387_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_x_5364_);
lean_ctor_set(v_reuseFailAlloc_5394_, 1, v_x_5365_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
v___y_5379_ = v___x_5393_;
goto v___jp_5378_;
}
}
}
}
case 1:
{
lean_object* v_node_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5408_; 
v_node_5396_ = lean_ctor_get(v_v_5375_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v_v_5375_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5398_ = v_v_5375_;
v_isShared_5399_ = v_isSharedCheck_5408_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_node_5396_);
lean_dec(v_v_5375_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5408_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
size_t v___x_5400_; size_t v___x_5401_; size_t v___x_5402_; size_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5400_ = ((size_t)5ULL);
v___x_5401_ = lean_usize_shift_right(v_x_5362_, v___x_5400_);
v___x_5402_ = ((size_t)1ULL);
v___x_5403_ = lean_usize_add(v_x_5363_, v___x_5402_);
v___x_5404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5396_, v___x_5401_, v___x_5403_, v_x_5364_, v_x_5365_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 0, v___x_5404_);
v___x_5406_ = v___x_5398_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
v___y_5379_ = v___x_5406_;
goto v___jp_5378_;
}
}
}
default: 
{
lean_object* v___x_5409_; 
v___x_5409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5409_, 0, v_x_5364_);
lean_ctor_set(v___x_5409_, 1, v_x_5365_);
v___y_5379_ = v___x_5409_;
goto v___jp_5378_;
}
}
v___jp_5378_:
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
v___x_5380_ = lean_array_fset(v_xs_x27_5377_, v_j_5369_, v___y_5379_);
lean_dec(v_j_5369_);
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 0, v___x_5380_);
v___x_5382_ = v___x_5373_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
else
{
lean_object* v_ks_5412_; lean_object* v_vs_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5433_; 
v_ks_5412_ = lean_ctor_get(v_x_5361_, 0);
v_vs_5413_ = lean_ctor_get(v_x_5361_, 1);
v_isSharedCheck_5433_ = !lean_is_exclusive(v_x_5361_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5415_ = v_x_5361_;
v_isShared_5416_ = v_isSharedCheck_5433_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_vs_5413_);
lean_inc(v_ks_5412_);
lean_dec(v_x_5361_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5433_;
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
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_ks_5412_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_vs_5413_);
v___x_5418_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
lean_object* v_newNode_5419_; uint8_t v___y_5421_; size_t v___x_5427_; uint8_t v___x_5428_; 
v_newNode_5419_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5418_, v_x_5364_, v_x_5365_);
v___x_5427_ = ((size_t)7ULL);
v___x_5428_ = lean_usize_dec_le(v___x_5427_, v_x_5363_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; lean_object* v___x_5430_; uint8_t v___x_5431_; 
v___x_5429_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5419_);
v___x_5430_ = lean_unsigned_to_nat(4u);
v___x_5431_ = lean_nat_dec_lt(v___x_5429_, v___x_5430_);
lean_dec(v___x_5429_);
v___y_5421_ = v___x_5431_;
goto v___jp_5420_;
}
else
{
v___y_5421_ = v___x_5428_;
goto v___jp_5420_;
}
v___jp_5420_:
{
if (v___y_5421_ == 0)
{
lean_object* v_ks_5422_; lean_object* v_vs_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v_ks_5422_ = lean_ctor_get(v_newNode_5419_, 0);
lean_inc_ref(v_ks_5422_);
v_vs_5423_ = lean_ctor_get(v_newNode_5419_, 1);
lean_inc_ref(v_vs_5423_);
lean_dec_ref(v_newNode_5419_);
v___x_5424_ = lean_unsigned_to_nat(0u);
v___x_5425_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5363_, v_ks_5422_, v_vs_5423_, v___x_5424_, v___x_5425_);
lean_dec_ref(v_vs_5423_);
lean_dec_ref(v_ks_5422_);
return v___x_5426_;
}
else
{
return v_newNode_5419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5434_, lean_object* v_keys_5435_, lean_object* v_vals_5436_, lean_object* v_i_5437_, lean_object* v_entries_5438_){
_start:
{
lean_object* v___x_5439_; uint8_t v___x_5440_; 
v___x_5439_ = lean_array_get_size(v_keys_5435_);
v___x_5440_ = lean_nat_dec_lt(v_i_5437_, v___x_5439_);
if (v___x_5440_ == 0)
{
lean_dec(v_i_5437_);
return v_entries_5438_;
}
else
{
lean_object* v_k_5441_; lean_object* v_v_5442_; uint64_t v___x_5443_; size_t v_h_5444_; size_t v___x_5445_; lean_object* v___x_5446_; size_t v___x_5447_; size_t v___x_5448_; size_t v___x_5449_; size_t v_h_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; 
v_k_5441_ = lean_array_fget_borrowed(v_keys_5435_, v_i_5437_);
v_v_5442_ = lean_array_fget_borrowed(v_vals_5436_, v_i_5437_);
v___x_5443_ = l_Lean_instHashableMVarId_hash(v_k_5441_);
v_h_5444_ = lean_uint64_to_usize(v___x_5443_);
v___x_5445_ = ((size_t)5ULL);
v___x_5446_ = lean_unsigned_to_nat(1u);
v___x_5447_ = ((size_t)1ULL);
v___x_5448_ = lean_usize_sub(v_depth_5434_, v___x_5447_);
v___x_5449_ = lean_usize_mul(v___x_5445_, v___x_5448_);
v_h_5450_ = lean_usize_shift_right(v_h_5444_, v___x_5449_);
v___x_5451_ = lean_nat_add(v_i_5437_, v___x_5446_);
lean_dec(v_i_5437_);
lean_inc(v_v_5442_);
lean_inc(v_k_5441_);
v___x_5452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5438_, v_h_5450_, v_depth_5434_, v_k_5441_, v_v_5442_);
v_i_5437_ = v___x_5451_;
v_entries_5438_ = v___x_5452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5454_, lean_object* v_keys_5455_, lean_object* v_vals_5456_, lean_object* v_i_5457_, lean_object* v_entries_5458_){
_start:
{
size_t v_depth_boxed_5459_; lean_object* v_res_5460_; 
v_depth_boxed_5459_ = lean_unbox_usize(v_depth_5454_);
lean_dec(v_depth_5454_);
v_res_5460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5459_, v_keys_5455_, v_vals_5456_, v_i_5457_, v_entries_5458_);
lean_dec_ref(v_vals_5456_);
lean_dec_ref(v_keys_5455_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5461_, lean_object* v_x_5462_, lean_object* v_x_5463_, lean_object* v_x_5464_, lean_object* v_x_5465_){
_start:
{
size_t v_x_77432__boxed_5466_; size_t v_x_77433__boxed_5467_; lean_object* v_res_5468_; 
v_x_77432__boxed_5466_ = lean_unbox_usize(v_x_5462_);
lean_dec(v_x_5462_);
v_x_77433__boxed_5467_ = lean_unbox_usize(v_x_5463_);
lean_dec(v_x_5463_);
v_res_5468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5461_, v_x_77432__boxed_5466_, v_x_77433__boxed_5467_, v_x_5464_, v_x_5465_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5469_, lean_object* v_x_5470_, lean_object* v_x_5471_){
_start:
{
uint64_t v___x_5472_; size_t v___x_5473_; size_t v___x_5474_; lean_object* v___x_5475_; 
v___x_5472_ = l_Lean_instHashableMVarId_hash(v_x_5470_);
v___x_5473_ = lean_uint64_to_usize(v___x_5472_);
v___x_5474_ = ((size_t)1ULL);
v___x_5475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5469_, v___x_5473_, v___x_5474_, v_x_5470_, v_x_5471_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5476_, lean_object* v_val_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v___x_5480_; lean_object* v_mctx_5481_; lean_object* v_cache_5482_; lean_object* v_zetaDeltaFVarIds_5483_; lean_object* v_postponed_5484_; lean_object* v_diag_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5513_; 
v___x_5480_ = lean_st_ref_take(v___y_5478_);
v_mctx_5481_ = lean_ctor_get(v___x_5480_, 0);
v_cache_5482_ = lean_ctor_get(v___x_5480_, 1);
v_zetaDeltaFVarIds_5483_ = lean_ctor_get(v___x_5480_, 2);
v_postponed_5484_ = lean_ctor_get(v___x_5480_, 3);
v_diag_5485_ = lean_ctor_get(v___x_5480_, 4);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5487_ = v___x_5480_;
v_isShared_5488_ = v_isSharedCheck_5513_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_diag_5485_);
lean_inc(v_postponed_5484_);
lean_inc(v_zetaDeltaFVarIds_5483_);
lean_inc(v_cache_5482_);
lean_inc(v_mctx_5481_);
lean_dec(v___x_5480_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5513_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v_depth_5489_; lean_object* v_levelAssignDepth_5490_; lean_object* v_lmvarCounter_5491_; lean_object* v_mvarCounter_5492_; lean_object* v_lDecls_5493_; lean_object* v_decls_5494_; lean_object* v_userNames_5495_; lean_object* v_lAssignment_5496_; lean_object* v_eAssignment_5497_; lean_object* v_dAssignment_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5512_; 
v_depth_5489_ = lean_ctor_get(v_mctx_5481_, 0);
v_levelAssignDepth_5490_ = lean_ctor_get(v_mctx_5481_, 1);
v_lmvarCounter_5491_ = lean_ctor_get(v_mctx_5481_, 2);
v_mvarCounter_5492_ = lean_ctor_get(v_mctx_5481_, 3);
v_lDecls_5493_ = lean_ctor_get(v_mctx_5481_, 4);
v_decls_5494_ = lean_ctor_get(v_mctx_5481_, 5);
v_userNames_5495_ = lean_ctor_get(v_mctx_5481_, 6);
v_lAssignment_5496_ = lean_ctor_get(v_mctx_5481_, 7);
v_eAssignment_5497_ = lean_ctor_get(v_mctx_5481_, 8);
v_dAssignment_5498_ = lean_ctor_get(v_mctx_5481_, 9);
v_isSharedCheck_5512_ = !lean_is_exclusive(v_mctx_5481_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5500_ = v_mctx_5481_;
v_isShared_5501_ = v_isSharedCheck_5512_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_dAssignment_5498_);
lean_inc(v_eAssignment_5497_);
lean_inc(v_lAssignment_5496_);
lean_inc(v_userNames_5495_);
lean_inc(v_decls_5494_);
lean_inc(v_lDecls_5493_);
lean_inc(v_mvarCounter_5492_);
lean_inc(v_lmvarCounter_5491_);
lean_inc(v_levelAssignDepth_5490_);
lean_inc(v_depth_5489_);
lean_dec(v_mctx_5481_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5512_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5502_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5497_, v_mvarId_5476_, v_val_5477_);
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 8, v___x_5502_);
v___x_5504_ = v___x_5500_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_depth_5489_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v_levelAssignDepth_5490_);
lean_ctor_set(v_reuseFailAlloc_5511_, 2, v_lmvarCounter_5491_);
lean_ctor_set(v_reuseFailAlloc_5511_, 3, v_mvarCounter_5492_);
lean_ctor_set(v_reuseFailAlloc_5511_, 4, v_lDecls_5493_);
lean_ctor_set(v_reuseFailAlloc_5511_, 5, v_decls_5494_);
lean_ctor_set(v_reuseFailAlloc_5511_, 6, v_userNames_5495_);
lean_ctor_set(v_reuseFailAlloc_5511_, 7, v_lAssignment_5496_);
lean_ctor_set(v_reuseFailAlloc_5511_, 8, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5511_, 9, v_dAssignment_5498_);
v___x_5504_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5506_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v___x_5504_);
v___x_5506_ = v___x_5487_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v_cache_5482_);
lean_ctor_set(v_reuseFailAlloc_5510_, 2, v_zetaDeltaFVarIds_5483_);
lean_ctor_set(v_reuseFailAlloc_5510_, 3, v_postponed_5484_);
lean_ctor_set(v_reuseFailAlloc_5510_, 4, v_diag_5485_);
v___x_5506_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5507_ = lean_st_ref_set(v___y_5478_, v___x_5506_);
v___x_5508_ = lean_box(0);
v___x_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5508_);
return v___x_5509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5514_, lean_object* v_val_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
lean_object* v_res_5518_; 
v_res_5518_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5514_, v_val_5515_, v___y_5516_);
lean_dec(v___y_5516_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5519_, lean_object* v_snd_5520_, uint8_t v___y_5521_, lean_object* v_as_x27_5522_, lean_object* v_b_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_){
_start:
{
if (lean_obj_tag(v_as_x27_5522_) == 0)
{
lean_object* v___x_5534_; 
lean_dec_ref(v_snd_5520_);
lean_dec_ref(v_kp_5519_);
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v_b_5523_);
return v___x_5534_;
}
else
{
lean_object* v_head_5535_; lean_object* v_tail_5536_; lean_object* v___x_5537_; 
v_head_5535_ = lean_ctor_get(v_as_x27_5522_, 0);
v_tail_5536_ = lean_ctor_get(v_as_x27_5522_, 1);
lean_inc_ref(v_kp_5519_);
lean_inc(v___y_5532_);
lean_inc_ref(v___y_5531_);
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
lean_inc(v___y_5526_);
lean_inc_ref(v___y_5525_);
lean_inc(v___y_5524_);
lean_inc(v_head_5535_);
v___x_5537_ = lean_apply_11(v_kp_5519_, v_head_5535_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, lean_box(0));
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_snd_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5633_; 
v_snd_5538_ = lean_ctor_get(v_b_5523_, 1);
v_isSharedCheck_5633_ = !lean_is_exclusive(v_b_5523_);
if (v_isSharedCheck_5633_ == 0)
{
lean_object* v_unused_5634_; 
v_unused_5634_ = lean_ctor_get(v_b_5523_, 0);
lean_dec(v_unused_5634_);
v___x_5540_ = v_b_5523_;
v_isShared_5541_ = v_isSharedCheck_5633_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_snd_5538_);
lean_dec(v_b_5523_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5633_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5632_; 
v_a_5542_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5544_ = v___x_5537_;
v_isShared_5545_ = v_isSharedCheck_5632_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5537_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5632_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v_fst_5546_; lean_object* v_snd_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5631_; 
v_fst_5546_ = lean_ctor_get(v_snd_5538_, 0);
v_snd_5547_ = lean_ctor_get(v_snd_5538_, 1);
v_isSharedCheck_5631_ = !lean_is_exclusive(v_snd_5538_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5549_ = v_snd_5538_;
v_isShared_5550_ = v_isSharedCheck_5631_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_snd_5547_);
lean_inc(v_fst_5546_);
lean_dec(v_snd_5538_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5631_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5551_; 
v___x_5551_ = lean_box(0);
if (lean_obj_tag(v_a_5542_) == 0)
{
lean_object* v_seq_5552_; lean_object* v_mvarId_5553_; lean_object* v___x_5554_; 
lean_del_object(v___x_5544_);
v_seq_5552_ = lean_ctor_get(v_a_5542_, 0);
v_mvarId_5553_ = lean_ctor_get(v_head_5535_, 1);
lean_inc(v_mvarId_5553_);
v___x_5554_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5553_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v_a_5555_; 
v_a_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_a_5555_);
lean_dec_ref_known(v___x_5554_, 1);
if (lean_obj_tag(v_a_5555_) == 1)
{
lean_object* v_val_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5587_; 
lean_dec_ref(v_kp_5519_);
v_val_5556_ = lean_ctor_get(v_a_5555_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_a_5555_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5558_ = v_a_5555_;
v_isShared_5559_ = v_isSharedCheck_5587_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_val_5556_);
lean_dec(v_a_5555_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5587_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v_mvarId_5560_; lean_object* v___x_5561_; 
v_mvarId_5560_ = lean_ctor_get(v_snd_5520_, 1);
lean_inc(v_mvarId_5560_);
lean_dec_ref(v_snd_5520_);
v___x_5561_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5560_, v_val_5556_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5561_) == 0)
{
lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5577_; 
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v___x_5561_, 0);
lean_dec(v_unused_5578_);
v___x_5563_ = v___x_5561_;
v_isShared_5564_ = v_isSharedCheck_5577_;
goto v_resetjp_5562_;
}
else
{
lean_dec(v___x_5561_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5577_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5559_ == 0)
{
lean_ctor_set(v___x_5558_, 0, v_a_5542_);
v___x_5566_ = v___x_5558_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5542_);
v___x_5566_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5550_ == 0)
{
v___x_5568_ = v___x_5549_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_fst_5546_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v_snd_5547_);
v___x_5568_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5568_);
lean_ctor_set(v___x_5540_, 0, v___x_5566_);
v___x_5570_ = v___x_5540_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5566_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5572_; 
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5570_);
v___x_5572_ = v___x_5563_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
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
}
else
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5586_; 
lean_del_object(v___x_5558_);
lean_dec_ref_known(v_a_5542_, 1);
lean_del_object(v___x_5549_);
lean_dec(v_snd_5547_);
lean_dec(v_fst_5546_);
lean_del_object(v___x_5540_);
v_a_5579_ = lean_ctor_get(v___x_5561_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5581_ = v___x_5561_;
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5561_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5582_ == 0)
{
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
else
{
uint8_t v___x_5588_; 
lean_inc(v_seq_5552_);
lean_dec(v_a_5555_);
lean_dec_ref_known(v_a_5542_, 1);
v___x_5588_ = l_List_isEmpty___redArg(v_seq_5552_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; lean_object* v___x_5591_; 
v___x_5589_ = lean_array_push(v_fst_5546_, v_seq_5552_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 0, v___x_5589_);
v___x_5591_ = v___x_5549_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_snd_5547_);
v___x_5591_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5593_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5591_);
lean_ctor_set(v___x_5540_, 0, v___x_5551_);
v___x_5593_ = v___x_5540_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
v_as_x27_5522_ = v_tail_5536_;
v_b_5523_ = v___x_5593_;
goto _start;
}
}
}
else
{
lean_object* v___x_5598_; 
lean_dec(v_seq_5552_);
if (v_isShared_5550_ == 0)
{
v___x_5598_ = v___x_5549_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_fst_5546_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_snd_5547_);
v___x_5598_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5598_);
lean_ctor_set(v___x_5540_, 0, v___x_5551_);
v___x_5600_ = v___x_5540_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v___x_5598_);
v___x_5600_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
v_as_x27_5522_ = v_tail_5536_;
v_b_5523_ = v___x_5600_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
lean_dec_ref_known(v_a_5542_, 1);
lean_del_object(v___x_5549_);
lean_dec(v_snd_5547_);
lean_dec(v_fst_5546_);
lean_del_object(v___x_5540_);
lean_dec_ref(v_snd_5520_);
lean_dec_ref(v_kp_5519_);
v_a_5604_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5554_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_a_5604_);
lean_dec(v___x_5554_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
else
{
if (v___y_5521_ == 0)
{
lean_object* v_gs_5612_; lean_object* v___x_5613_; lean_object* v___x_5615_; 
lean_del_object(v___x_5544_);
v_gs_5612_ = lean_ctor_get(v_a_5542_, 0);
lean_inc(v_gs_5612_);
lean_dec_ref_known(v_a_5542_, 1);
v___x_5613_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5547_, v_gs_5612_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 1, v___x_5613_);
v___x_5615_ = v___x_5549_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_fst_5546_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v___x_5613_);
v___x_5615_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
lean_object* v___x_5617_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5615_);
lean_ctor_set(v___x_5540_, 0, v___x_5551_);
v___x_5617_ = v___x_5540_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
v_as_x27_5522_ = v_tail_5536_;
v_b_5523_ = v___x_5617_;
goto _start;
}
}
}
else
{
lean_object* v___x_5621_; lean_object* v___x_5623_; 
lean_dec_ref(v_snd_5520_);
lean_dec_ref(v_kp_5519_);
v___x_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5621_, 0, v_a_5542_);
if (v_isShared_5550_ == 0)
{
v___x_5623_ = v___x_5549_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_fst_5546_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_snd_5547_);
v___x_5623_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
lean_object* v___x_5625_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 1, v___x_5623_);
lean_ctor_set(v___x_5540_, 0, v___x_5621_);
v___x_5625_ = v___x_5540_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5621_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v___x_5623_);
v___x_5625_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5627_; 
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v___x_5625_);
v___x_5627_ = v___x_5544_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v___x_5625_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
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
lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
lean_dec_ref(v_b_5523_);
lean_dec_ref(v_snd_5520_);
lean_dec_ref(v_kp_5519_);
v_a_5635_ = lean_ctor_get(v___x_5537_, 0);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5537_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_dec(v___x_5537_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5643_, lean_object* v_snd_5644_, lean_object* v___y_5645_, lean_object* v_as_x27_5646_, lean_object* v_b_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
uint8_t v___y_77646__boxed_5658_; lean_object* v_res_5659_; 
v___y_77646__boxed_5658_ = lean_unbox(v___y_5645_);
v_res_5659_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5643_, v_snd_5644_, v___y_77646__boxed_5658_, v_as_x27_5646_, v_b_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec(v___y_5648_);
lean_dec(v_as_x27_5646_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5660_, lean_object* v_c_5661_, lean_object* v___x_5662_, lean_object* v___x_5663_, uint8_t v_isRec_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
if (lean_obj_tag(v_a_5665_) == 0)
{
lean_object* v___x_5667_; 
lean_dec(v___x_5663_);
lean_dec_ref(v___x_5662_);
lean_dec_ref(v_snd_5660_);
v___x_5667_ = lean_array_to_list(v_a_5666_);
return v___x_5667_;
}
else
{
lean_object* v_toGoalState_5668_; lean_object* v_split_5669_; lean_object* v_head_5670_; lean_object* v_tail_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5731_; 
v_toGoalState_5668_ = lean_ctor_get(v_snd_5660_, 0);
lean_inc_ref(v_toGoalState_5668_);
v_split_5669_ = lean_ctor_get(v_toGoalState_5668_, 14);
lean_inc_ref(v_split_5669_);
v_head_5670_ = lean_ctor_get(v_a_5665_, 0);
v_tail_5671_ = lean_ctor_get(v_a_5665_, 1);
v_isSharedCheck_5731_ = !lean_is_exclusive(v_a_5665_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5673_ = v_a_5665_;
v_isShared_5674_ = v_isSharedCheck_5731_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_tail_5671_);
lean_inc(v_head_5670_);
lean_dec(v_a_5665_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5731_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v_nextDeclIdx_5675_; lean_object* v_enodeMap_5676_; lean_object* v_exprs_5677_; lean_object* v_parents_5678_; lean_object* v_congrTable_5679_; lean_object* v_appMap_5680_; lean_object* v_indicesFound_5681_; lean_object* v_newFacts_5682_; uint8_t v_inconsistent_5683_; lean_object* v_nextIdx_5684_; lean_object* v_newRawFacts_5685_; lean_object* v_facts_5686_; lean_object* v_extThms_5687_; lean_object* v_ematch_5688_; lean_object* v_inj_5689_; lean_object* v_clean_5690_; lean_object* v_sstates_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5729_; 
v_nextDeclIdx_5675_ = lean_ctor_get(v_toGoalState_5668_, 0);
v_enodeMap_5676_ = lean_ctor_get(v_toGoalState_5668_, 1);
v_exprs_5677_ = lean_ctor_get(v_toGoalState_5668_, 2);
v_parents_5678_ = lean_ctor_get(v_toGoalState_5668_, 3);
v_congrTable_5679_ = lean_ctor_get(v_toGoalState_5668_, 4);
v_appMap_5680_ = lean_ctor_get(v_toGoalState_5668_, 5);
v_indicesFound_5681_ = lean_ctor_get(v_toGoalState_5668_, 6);
v_newFacts_5682_ = lean_ctor_get(v_toGoalState_5668_, 7);
v_inconsistent_5683_ = lean_ctor_get_uint8(v_toGoalState_5668_, sizeof(void*)*17);
v_nextIdx_5684_ = lean_ctor_get(v_toGoalState_5668_, 8);
v_newRawFacts_5685_ = lean_ctor_get(v_toGoalState_5668_, 9);
v_facts_5686_ = lean_ctor_get(v_toGoalState_5668_, 10);
v_extThms_5687_ = lean_ctor_get(v_toGoalState_5668_, 11);
v_ematch_5688_ = lean_ctor_get(v_toGoalState_5668_, 12);
v_inj_5689_ = lean_ctor_get(v_toGoalState_5668_, 13);
v_clean_5690_ = lean_ctor_get(v_toGoalState_5668_, 15);
v_sstates_5691_ = lean_ctor_get(v_toGoalState_5668_, 16);
v_isSharedCheck_5729_ = !lean_is_exclusive(v_toGoalState_5668_);
if (v_isSharedCheck_5729_ == 0)
{
lean_object* v_unused_5730_; 
v_unused_5730_ = lean_ctor_get(v_toGoalState_5668_, 14);
lean_dec(v_unused_5730_);
v___x_5693_ = v_toGoalState_5668_;
v_isShared_5694_ = v_isSharedCheck_5729_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_sstates_5691_);
lean_inc(v_clean_5690_);
lean_inc(v_inj_5689_);
lean_inc(v_ematch_5688_);
lean_inc(v_extThms_5687_);
lean_inc(v_facts_5686_);
lean_inc(v_newRawFacts_5685_);
lean_inc(v_nextIdx_5684_);
lean_inc(v_newFacts_5682_);
lean_inc(v_indicesFound_5681_);
lean_inc(v_appMap_5680_);
lean_inc(v_congrTable_5679_);
lean_inc(v_parents_5678_);
lean_inc(v_exprs_5677_);
lean_inc(v_enodeMap_5676_);
lean_inc(v_nextDeclIdx_5675_);
lean_dec(v_toGoalState_5668_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5729_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v_num_5695_; lean_object* v_candidates_5696_; lean_object* v_added_5697_; lean_object* v_resolved_5698_; lean_object* v_trace_5699_; lean_object* v_lookaheads_5700_; lean_object* v_argPosMap_5701_; lean_object* v_argsAt_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5728_; 
v_num_5695_ = lean_ctor_get(v_split_5669_, 0);
v_candidates_5696_ = lean_ctor_get(v_split_5669_, 1);
v_added_5697_ = lean_ctor_get(v_split_5669_, 2);
v_resolved_5698_ = lean_ctor_get(v_split_5669_, 3);
v_trace_5699_ = lean_ctor_get(v_split_5669_, 4);
v_lookaheads_5700_ = lean_ctor_get(v_split_5669_, 5);
v_argPosMap_5701_ = lean_ctor_get(v_split_5669_, 6);
v_argsAt_5702_ = lean_ctor_get(v_split_5669_, 7);
v_isSharedCheck_5728_ = !lean_is_exclusive(v_split_5669_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5704_ = v_split_5669_;
v_isShared_5705_ = v_isSharedCheck_5728_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_argsAt_5702_);
lean_inc(v_argPosMap_5701_);
lean_inc(v_lookaheads_5700_);
lean_inc(v_trace_5699_);
lean_inc(v_resolved_5698_);
lean_inc(v_added_5697_);
lean_inc(v_candidates_5696_);
lean_inc(v_num_5695_);
lean_dec(v_split_5669_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5728_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5706_; lean_object* v___y_5708_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v___x_5706_ = lean_array_get_size(v_a_5666_);
v___x_5726_ = lean_unsigned_to_nat(0u);
v___x_5727_ = lean_nat_dec_lt(v___x_5726_, v___x_5706_);
if (v___x_5727_ == 0)
{
if (v_isRec_5664_ == 0)
{
v___y_5708_ = v_num_5695_;
goto v___jp_5707_;
}
else
{
goto v___jp_5723_;
}
}
else
{
goto v___jp_5723_;
}
v___jp_5707_:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5712_; 
v___x_5709_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5661_);
lean_inc(v___x_5663_);
lean_inc_ref(v___x_5662_);
v___x_5710_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5662_);
lean_ctor_set(v___x_5710_, 1, v___x_5706_);
lean_ctor_set(v___x_5710_, 2, v___x_5663_);
lean_ctor_set(v___x_5710_, 3, v___x_5709_);
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 1, v_trace_5699_);
lean_ctor_set(v___x_5673_, 0, v___x_5710_);
v___x_5712_ = v___x_5673_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v___x_5710_);
lean_ctor_set(v_reuseFailAlloc_5722_, 1, v_trace_5699_);
v___x_5712_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
lean_object* v___x_5714_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 4, v___x_5712_);
lean_ctor_set(v___x_5704_, 0, v___y_5708_);
v___x_5714_ = v___x_5704_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___y_5708_);
lean_ctor_set(v_reuseFailAlloc_5721_, 1, v_candidates_5696_);
lean_ctor_set(v_reuseFailAlloc_5721_, 2, v_added_5697_);
lean_ctor_set(v_reuseFailAlloc_5721_, 3, v_resolved_5698_);
lean_ctor_set(v_reuseFailAlloc_5721_, 4, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5721_, 5, v_lookaheads_5700_);
lean_ctor_set(v_reuseFailAlloc_5721_, 6, v_argPosMap_5701_);
lean_ctor_set(v_reuseFailAlloc_5721_, 7, v_argsAt_5702_);
v___x_5714_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
lean_object* v___x_5716_; 
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 14, v___x_5714_);
v___x_5716_ = v___x_5693_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5720_; 
v_reuseFailAlloc_5720_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5720_, 0, v_nextDeclIdx_5675_);
lean_ctor_set(v_reuseFailAlloc_5720_, 1, v_enodeMap_5676_);
lean_ctor_set(v_reuseFailAlloc_5720_, 2, v_exprs_5677_);
lean_ctor_set(v_reuseFailAlloc_5720_, 3, v_parents_5678_);
lean_ctor_set(v_reuseFailAlloc_5720_, 4, v_congrTable_5679_);
lean_ctor_set(v_reuseFailAlloc_5720_, 5, v_appMap_5680_);
lean_ctor_set(v_reuseFailAlloc_5720_, 6, v_indicesFound_5681_);
lean_ctor_set(v_reuseFailAlloc_5720_, 7, v_newFacts_5682_);
lean_ctor_set(v_reuseFailAlloc_5720_, 8, v_nextIdx_5684_);
lean_ctor_set(v_reuseFailAlloc_5720_, 9, v_newRawFacts_5685_);
lean_ctor_set(v_reuseFailAlloc_5720_, 10, v_facts_5686_);
lean_ctor_set(v_reuseFailAlloc_5720_, 11, v_extThms_5687_);
lean_ctor_set(v_reuseFailAlloc_5720_, 12, v_ematch_5688_);
lean_ctor_set(v_reuseFailAlloc_5720_, 13, v_inj_5689_);
lean_ctor_set(v_reuseFailAlloc_5720_, 14, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5720_, 15, v_clean_5690_);
lean_ctor_set(v_reuseFailAlloc_5720_, 16, v_sstates_5691_);
lean_ctor_set_uint8(v_reuseFailAlloc_5720_, sizeof(void*)*17, v_inconsistent_5683_);
v___x_5716_ = v_reuseFailAlloc_5720_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
lean_object* v___x_5717_; lean_object* v___x_5718_; 
v___x_5717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
lean_ctor_set(v___x_5717_, 1, v_head_5670_);
v___x_5718_ = lean_array_push(v_a_5666_, v___x_5717_);
v_a_5665_ = v_tail_5671_;
v_a_5666_ = v___x_5718_;
goto _start;
}
}
}
}
v___jp_5723_:
{
lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___x_5724_ = lean_unsigned_to_nat(1u);
v___x_5725_ = lean_nat_add(v_num_5695_, v___x_5724_);
lean_dec(v_num_5695_);
v___y_5708_ = v___x_5725_;
goto v___jp_5707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5732_, lean_object* v_c_5733_, lean_object* v___x_5734_, lean_object* v___x_5735_, lean_object* v_isRec_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_){
_start:
{
uint8_t v_isRec_boxed_5739_; lean_object* v_res_5740_; 
v_isRec_boxed_5739_ = lean_unbox(v_isRec_5736_);
v_res_5740_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5732_, v_c_5733_, v___x_5734_, v___x_5735_, v_isRec_boxed_5739_, v_a_5737_, v_a_5738_);
lean_dec_ref(v_c_5733_);
return v_res_5740_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5752_ = lean_box(0);
v___x_5753_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5754_ = l_Lean_mkConst(v___x_5753_, v___x_5752_);
return v___x_5754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5755_, lean_object* v_numCases_5756_, uint8_t v_isRec_5757_, uint8_t v_stopAtFirstFailure_5758_, uint8_t v_compress_5759_, lean_object* v_candidates_x3f_5760_, lean_object* v_goal_5761_, lean_object* v_kp_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_){
_start:
{
lean_object* v___x_5773_; 
v___x_5773_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5764_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5775_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc(v_a_5774_);
lean_dec_ref_known(v___x_5773_, 1);
lean_inc_ref(v_goal_5761_);
v___x_5775_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5761_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; uint8_t v_trace_5777_; lean_object* v_mvarId_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___f_5781_; lean_object* v___x_5782_; lean_object* v___f_5783_; lean_object* v___x_5784_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
lean_inc_n(v_a_5776_, 2);
lean_dec_ref_known(v___x_5775_, 1);
v_trace_5777_ = lean_ctor_get_uint8(v_a_5774_, sizeof(void*)*13);
lean_dec(v_a_5774_);
v_mvarId_5778_ = lean_ctor_get(v_goal_5761_, 1);
lean_inc(v_mvarId_5778_);
v___x_5779_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5755_);
v___x_5780_ = lean_box(v_isRec_5757_);
lean_inc_ref_n(v_c_5755_, 2);
lean_inc_ref(v___x_5779_);
v___f_5781_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5781_, 0, v___x_5779_);
lean_closure_set(v___f_5781_, 1, v_c_5755_);
lean_closure_set(v___f_5781_, 2, v_a_5776_);
lean_closure_set(v___f_5781_, 3, v_numCases_5756_);
lean_closure_set(v___f_5781_, 4, v___x_5780_);
v___x_5782_ = lean_box(v_trace_5777_);
v___f_5783_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5783_, 0, v_goal_5761_);
lean_closure_set(v___f_5783_, 1, v___x_5782_);
lean_closure_set(v___f_5783_, 2, v___f_5781_);
lean_closure_set(v___f_5783_, 3, v_c_5755_);
lean_closure_set(v___f_5783_, 4, v_candidates_x3f_5760_);
v___x_5784_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5778_, v___f_5783_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_object* v_a_5785_; lean_object* v_fst_5786_; lean_object* v_snd_5787_; lean_object* v_fst_5788_; lean_object* v_snd_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v_a_5785_ = lean_ctor_get(v___x_5784_, 0);
lean_inc(v_a_5785_);
lean_dec_ref_known(v___x_5784_, 1);
v_fst_5786_ = lean_ctor_get(v_a_5785_, 0);
lean_inc(v_fst_5786_);
v_snd_5787_ = lean_ctor_get(v_a_5785_, 1);
lean_inc_n(v_snd_5787_, 3);
lean_dec(v_a_5785_);
v_fst_5788_ = lean_ctor_get(v_fst_5786_, 0);
lean_inc(v_fst_5788_);
v_snd_5789_ = lean_ctor_get(v_fst_5786_, 1);
lean_inc(v_snd_5789_);
lean_dec(v_fst_5786_);
v___x_5790_ = l_List_lengthTR___redArg(v_fst_5788_);
v___x_5791_ = lean_unsigned_to_nat(0u);
v___x_5792_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5793_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5787_, v_c_5755_, v___x_5779_, v___x_5790_, v_isRec_5757_, v_fst_5788_, v___x_5792_);
lean_dec_ref(v_c_5755_);
v___x_5794_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5795_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5762_, v_snd_5787_, v_stopAtFirstFailure_5758_, v___x_5793_, v___x_5794_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
lean_dec(v___x_5793_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5883_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5883_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5883_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v_fst_5800_; 
v_fst_5800_ = lean_ctor_get(v_a_5796_, 0);
if (lean_obj_tag(v_fst_5800_) == 0)
{
lean_object* v_snd_5801_; lean_object* v_mvarId_5802_; lean_object* v___x_5803_; 
lean_del_object(v___x_5798_);
v_snd_5801_ = lean_ctor_get(v_a_5796_, 1);
lean_inc(v_snd_5801_);
lean_dec(v_a_5796_);
v_mvarId_5802_ = lean_ctor_get(v_snd_5787_, 1);
lean_inc_n(v_mvarId_5802_, 2);
lean_dec(v_snd_5787_);
v___x_5803_ = l_Lean_MVarId_getType(v_mvarId_5802_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5870_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5806_ = v___x_5803_;
v_isShared_5807_ = v_isSharedCheck_5870_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_a_5804_);
lean_dec(v___x_5803_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5870_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v_fst_5808_; lean_object* v_snd_5809_; lean_object* v___y_5811_; lean_object* v___y_5812_; uint8_t v___x_5859_; 
v_fst_5808_ = lean_ctor_get(v_snd_5801_, 0);
lean_inc(v_fst_5808_);
v_snd_5809_ = lean_ctor_get(v_snd_5801_, 1);
lean_inc(v_snd_5809_);
lean_dec(v_snd_5801_);
v___x_5859_ = l_Lean_Expr_isFalse(v_a_5804_);
if (v___x_5859_ == 0)
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v_a_5862_; lean_object* v___x_5863_; 
v___x_5860_ = l_Lean_mkMVar(v_a_5776_);
v___x_5861_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5860_, v_a_5769_);
v_a_5862_ = lean_ctor_get(v___x_5861_, 0);
lean_inc(v_a_5862_);
lean_dec_ref(v___x_5861_);
v___x_5863_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5802_, v_a_5862_, v_a_5769_);
lean_dec_ref(v___x_5863_);
v___y_5811_ = v_a_5770_;
v___y_5812_ = v_a_5771_;
goto v___jp_5810_;
}
else
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v_a_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5864_ = l_Lean_mkMVar(v_a_5776_);
v___x_5865_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5864_, v_a_5769_);
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref(v___x_5865_);
v___x_5867_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5868_ = l_Lean_Meta_mkExpectedPropHint(v_a_5866_, v___x_5867_);
v___x_5869_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5802_, v___x_5868_, v_a_5769_);
lean_dec_ref(v___x_5869_);
v___y_5811_ = v_a_5770_;
v___y_5812_ = v_a_5771_;
goto v___jp_5810_;
}
v___jp_5810_:
{
lean_object* v___x_5813_; uint8_t v___x_5814_; 
v___x_5813_ = lean_array_get_size(v_snd_5809_);
v___x_5814_ = lean_nat_dec_eq(v___x_5813_, v___x_5791_);
if (v___x_5814_ == 0)
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5818_; 
lean_dec(v_fst_5808_);
lean_dec(v_snd_5789_);
v___x_5815_ = lean_array_to_list(v_snd_5809_);
v___x_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5816_, 0, v___x_5815_);
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 0, v___x_5816_);
v___x_5818_ = v___x_5806_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v___x_5816_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
else
{
lean_dec(v_snd_5809_);
if (lean_obj_tag(v_snd_5789_) == 1)
{
lean_object* v_val_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5854_; 
lean_del_object(v___x_5806_);
v_val_5820_ = lean_ctor_get(v_snd_5789_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_snd_5789_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5822_ = v_snd_5789_;
v_isShared_5823_ = v_isSharedCheck_5854_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_val_5820_);
lean_dec(v_snd_5789_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5854_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5824_; 
v___x_5824_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5820_, v___y_5811_);
lean_dec(v_val_5820_);
if (lean_obj_tag(v___x_5824_) == 0)
{
lean_object* v_a_5825_; lean_object* v___x_5826_; 
v_a_5825_ = lean_ctor_get(v___x_5824_, 0);
lean_inc(v_a_5825_);
lean_dec_ref_known(v___x_5824_, 1);
v___x_5826_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5825_, v_fst_5808_, v_compress_5759_, v___y_5811_, v___y_5812_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v_a_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5837_; 
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5829_ = v___x_5826_;
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_a_5827_);
lean_dec(v___x_5826_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v___x_5832_; 
if (v_isShared_5823_ == 0)
{
lean_ctor_set_tag(v___x_5822_, 0);
lean_ctor_set(v___x_5822_, 0, v_a_5827_);
v___x_5832_ = v___x_5822_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5827_);
v___x_5832_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
lean_object* v___x_5834_; 
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 0, v___x_5832_);
v___x_5834_ = v___x_5829_;
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
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
lean_del_object(v___x_5822_);
v_a_5838_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5826_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5826_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5841_ == 0)
{
v___x_5843_ = v___x_5840_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
else
{
lean_object* v_a_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5853_; 
lean_del_object(v___x_5822_);
lean_dec(v_fst_5808_);
v_a_5846_ = lean_ctor_get(v___x_5824_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5824_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5848_ = v___x_5824_;
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_a_5846_);
lean_dec(v___x_5824_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5846_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
}
}
else
{
lean_object* v___x_5855_; lean_object* v___x_5857_; 
lean_dec(v_fst_5808_);
lean_dec(v_snd_5789_);
v___x_5855_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 0, v___x_5855_);
v___x_5857_ = v___x_5806_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v___x_5855_);
v___x_5857_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
return v___x_5857_;
}
}
}
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec(v_mvarId_5802_);
lean_dec(v_snd_5801_);
lean_dec(v_snd_5789_);
lean_dec(v_a_5776_);
v_a_5871_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5803_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5803_);
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
lean_object* v_val_5879_; lean_object* v___x_5881_; 
lean_inc_ref(v_fst_5800_);
lean_dec(v_a_5796_);
lean_dec(v_snd_5789_);
lean_dec(v_snd_5787_);
lean_dec(v_a_5776_);
v_val_5879_ = lean_ctor_get(v_fst_5800_, 0);
lean_inc(v_val_5879_);
lean_dec_ref_known(v_fst_5800_, 1);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v_val_5879_);
v___x_5881_ = v___x_5798_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_val_5879_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_dec(v_snd_5789_);
lean_dec(v_snd_5787_);
lean_dec(v_a_5776_);
v_a_5884_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5795_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5795_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
v___x_5889_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
return v___x_5889_;
}
}
}
}
else
{
lean_object* v_a_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5899_; 
lean_dec_ref(v___x_5779_);
lean_dec(v_a_5776_);
lean_dec_ref(v_kp_5762_);
lean_dec_ref(v_c_5755_);
v_a_5892_ = lean_ctor_get(v___x_5784_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5784_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5894_ = v___x_5784_;
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_a_5892_);
lean_dec(v___x_5784_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v___x_5897_; 
if (v_isShared_5895_ == 0)
{
v___x_5897_ = v___x_5894_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_dec(v_a_5774_);
lean_dec_ref(v_kp_5762_);
lean_dec_ref(v_goal_5761_);
lean_dec(v_candidates_x3f_5760_);
lean_dec(v_numCases_5756_);
lean_dec_ref(v_c_5755_);
v_a_5900_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5775_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5775_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
}
else
{
lean_object* v_a_5908_; lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_5915_; 
lean_dec_ref(v_kp_5762_);
lean_dec_ref(v_goal_5761_);
lean_dec(v_candidates_x3f_5760_);
lean_dec(v_numCases_5756_);
lean_dec_ref(v_c_5755_);
v_a_5908_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5910_ = v___x_5773_;
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_a_5908_);
lean_dec(v___x_5773_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5913_; 
if (v_isShared_5911_ == 0)
{
v___x_5913_ = v___x_5910_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_a_5908_);
v___x_5913_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
return v___x_5913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5916_ = _args[0];
lean_object* v_numCases_5917_ = _args[1];
lean_object* v_isRec_5918_ = _args[2];
lean_object* v_stopAtFirstFailure_5919_ = _args[3];
lean_object* v_compress_5920_ = _args[4];
lean_object* v_candidates_x3f_5921_ = _args[5];
lean_object* v_goal_5922_ = _args[6];
lean_object* v_kp_5923_ = _args[7];
lean_object* v_a_5924_ = _args[8];
lean_object* v_a_5925_ = _args[9];
lean_object* v_a_5926_ = _args[10];
lean_object* v_a_5927_ = _args[11];
lean_object* v_a_5928_ = _args[12];
lean_object* v_a_5929_ = _args[13];
lean_object* v_a_5930_ = _args[14];
lean_object* v_a_5931_ = _args[15];
lean_object* v_a_5932_ = _args[16];
lean_object* v_a_5933_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5934_; uint8_t v_stopAtFirstFailure_boxed_5935_; uint8_t v_compress_boxed_5936_; lean_object* v_res_5937_; 
v_isRec_boxed_5934_ = lean_unbox(v_isRec_5918_);
v_stopAtFirstFailure_boxed_5935_ = lean_unbox(v_stopAtFirstFailure_5919_);
v_compress_boxed_5936_ = lean_unbox(v_compress_5920_);
v_res_5937_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5916_, v_numCases_5917_, v_isRec_boxed_5934_, v_stopAtFirstFailure_boxed_5935_, v_compress_boxed_5936_, v_candidates_x3f_5921_, v_goal_5922_, v_kp_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
lean_dec(v_a_5932_);
lean_dec_ref(v_a_5931_);
lean_dec(v_a_5930_);
lean_dec_ref(v_a_5929_);
lean_dec(v_a_5928_);
lean_dec_ref(v_a_5927_);
lean_dec(v_a_5926_);
lean_dec_ref(v_a_5925_);
lean_dec(v_a_5924_);
return v_res_5937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5938_, lean_object* v_numCases_5939_, uint8_t v_isRec_5940_, uint8_t v_stopAtFirstFailure_5941_, uint8_t v_compress_5942_, lean_object* v_candidates_x3f_5943_, lean_object* v_goal_5944_, lean_object* v_x_5945_, lean_object* v_kp_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_){
_start:
{
lean_object* v___x_5957_; 
v___x_5957_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5938_, v_numCases_5939_, v_isRec_5940_, v_stopAtFirstFailure_5941_, v_compress_5942_, v_candidates_x3f_5943_, v_goal_5944_, v_kp_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5958_ = _args[0];
lean_object* v_numCases_5959_ = _args[1];
lean_object* v_isRec_5960_ = _args[2];
lean_object* v_stopAtFirstFailure_5961_ = _args[3];
lean_object* v_compress_5962_ = _args[4];
lean_object* v_candidates_x3f_5963_ = _args[5];
lean_object* v_goal_5964_ = _args[6];
lean_object* v_x_5965_ = _args[7];
lean_object* v_kp_5966_ = _args[8];
lean_object* v_a_5967_ = _args[9];
lean_object* v_a_5968_ = _args[10];
lean_object* v_a_5969_ = _args[11];
lean_object* v_a_5970_ = _args[12];
lean_object* v_a_5971_ = _args[13];
lean_object* v_a_5972_ = _args[14];
lean_object* v_a_5973_ = _args[15];
lean_object* v_a_5974_ = _args[16];
lean_object* v_a_5975_ = _args[17];
lean_object* v_a_5976_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5977_; uint8_t v_stopAtFirstFailure_boxed_5978_; uint8_t v_compress_boxed_5979_; lean_object* v_res_5980_; 
v_isRec_boxed_5977_ = lean_unbox(v_isRec_5960_);
v_stopAtFirstFailure_boxed_5978_ = lean_unbox(v_stopAtFirstFailure_5961_);
v_compress_boxed_5979_ = lean_unbox(v_compress_5962_);
v_res_5980_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5958_, v_numCases_5959_, v_isRec_boxed_5977_, v_stopAtFirstFailure_boxed_5978_, v_compress_boxed_5979_, v_candidates_x3f_5963_, v_goal_5964_, v_x_5965_, v_kp_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_);
lean_dec(v_a_5975_);
lean_dec_ref(v_a_5974_);
lean_dec(v_a_5973_);
lean_dec_ref(v_a_5972_);
lean_dec(v_a_5971_);
lean_dec_ref(v_a_5970_);
lean_dec(v_a_5969_);
lean_dec_ref(v_a_5968_);
lean_dec(v_a_5967_);
lean_dec_ref(v_x_5965_);
return v_res_5980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5981_, lean_object* v_snd_5982_, uint8_t v___y_5983_, lean_object* v_as_5984_, lean_object* v_as_x27_5985_, lean_object* v_b_5986_, lean_object* v_a_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_){
_start:
{
lean_object* v___x_5998_; 
v___x_5998_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5981_, v_snd_5982_, v___y_5983_, v_as_x27_5985_, v_b_5986_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
return v___x_5998_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5999_ = _args[0];
lean_object* v_snd_6000_ = _args[1];
lean_object* v___y_6001_ = _args[2];
lean_object* v_as_6002_ = _args[3];
lean_object* v_as_x27_6003_ = _args[4];
lean_object* v_b_6004_ = _args[5];
lean_object* v_a_6005_ = _args[6];
lean_object* v___y_6006_ = _args[7];
lean_object* v___y_6007_ = _args[8];
lean_object* v___y_6008_ = _args[9];
lean_object* v___y_6009_ = _args[10];
lean_object* v___y_6010_ = _args[11];
lean_object* v___y_6011_ = _args[12];
lean_object* v___y_6012_ = _args[13];
lean_object* v___y_6013_ = _args[14];
lean_object* v___y_6014_ = _args[15];
lean_object* v___y_6015_ = _args[16];
_start:
{
uint8_t v___y_78316__boxed_6016_; lean_object* v_res_6017_; 
v___y_78316__boxed_6016_ = lean_unbox(v___y_6001_);
v_res_6017_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5999_, v_snd_6000_, v___y_78316__boxed_6016_, v_as_6002_, v_as_x27_6003_, v_b_6004_, v_a_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v___y_6012_);
lean_dec_ref(v___y_6011_);
lean_dec(v___y_6010_);
lean_dec_ref(v___y_6009_);
lean_dec(v___y_6008_);
lean_dec_ref(v___y_6007_);
lean_dec(v___y_6006_);
lean_dec(v_as_x27_6003_);
lean_dec(v_as_6002_);
return v_res_6017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6018_, lean_object* v_val_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_){
_start:
{
lean_object* v___x_6030_; 
v___x_6030_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6018_, v_val_6019_, v___y_6026_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6031_, lean_object* v_val_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v_res_6043_; 
v_res_6043_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6031_, v_val_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_);
lean_dec(v___y_6041_);
lean_dec_ref(v___y_6040_);
lean_dec(v___y_6039_);
lean_dec_ref(v___y_6038_);
lean_dec(v___y_6037_);
lean_dec_ref(v___y_6036_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec(v___y_6033_);
return v_res_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6044_, lean_object* v_x_6045_, lean_object* v_x_6046_, lean_object* v_x_6047_){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6045_, v_x_6046_, v_x_6047_);
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6049_, lean_object* v_x_6050_, size_t v_x_6051_, size_t v_x_6052_, lean_object* v_x_6053_, lean_object* v_x_6054_){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6050_, v_x_6051_, v_x_6052_, v_x_6053_, v_x_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6056_, lean_object* v_x_6057_, lean_object* v_x_6058_, lean_object* v_x_6059_, lean_object* v_x_6060_, lean_object* v_x_6061_){
_start:
{
size_t v_x_78397__boxed_6062_; size_t v_x_78398__boxed_6063_; lean_object* v_res_6064_; 
v_x_78397__boxed_6062_ = lean_unbox_usize(v_x_6058_);
lean_dec(v_x_6058_);
v_x_78398__boxed_6063_ = lean_unbox_usize(v_x_6059_);
lean_dec(v_x_6059_);
v_res_6064_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6056_, v_x_6057_, v_x_78397__boxed_6062_, v_x_78398__boxed_6063_, v_x_6060_, v_x_6061_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6065_, lean_object* v_n_6066_, lean_object* v_k_6067_, lean_object* v_v_6068_){
_start:
{
lean_object* v___x_6069_; 
v___x_6069_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6066_, v_k_6067_, v_v_6068_);
return v___x_6069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6070_, size_t v_depth_6071_, lean_object* v_keys_6072_, lean_object* v_vals_6073_, lean_object* v_heq_6074_, lean_object* v_i_6075_, lean_object* v_entries_6076_){
_start:
{
lean_object* v___x_6077_; 
v___x_6077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6071_, v_keys_6072_, v_vals_6073_, v_i_6075_, v_entries_6076_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6078_, lean_object* v_depth_6079_, lean_object* v_keys_6080_, lean_object* v_vals_6081_, lean_object* v_heq_6082_, lean_object* v_i_6083_, lean_object* v_entries_6084_){
_start:
{
size_t v_depth_boxed_6085_; lean_object* v_res_6086_; 
v_depth_boxed_6085_ = lean_unbox_usize(v_depth_6079_);
lean_dec(v_depth_6079_);
v_res_6086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6078_, v_depth_boxed_6085_, v_keys_6080_, v_vals_6081_, v_heq_6082_, v_i_6083_, v_entries_6084_);
lean_dec_ref(v_vals_6081_);
lean_dec_ref(v_keys_6080_);
return v_res_6086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6087_, lean_object* v_x_6088_, lean_object* v_x_6089_, lean_object* v_x_6090_, lean_object* v_x_6091_){
_start:
{
lean_object* v___x_6092_; 
v___x_6092_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6088_, v_x_6089_, v_x_6090_, v_x_6091_);
return v___x_6092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = lean_st_mk_ref(v_goal_6093_);
v___x_6105_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6104_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6115_; 
v_a_6106_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6115_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6115_ == 0)
{
v___x_6108_ = v___x_6105_;
v_isShared_6109_ = v_isSharedCheck_6115_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6105_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6115_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6113_; 
v___x_6110_ = lean_st_ref_get(v___x_6104_);
lean_dec(v___x_6104_);
v___x_6111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6111_, 0, v_a_6106_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v___x_6111_);
v___x_6113_ = v___x_6108_;
goto v_reusejp_6112_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v___x_6111_);
v___x_6113_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6112_;
}
v_reusejp_6112_:
{
return v___x_6113_;
}
}
}
else
{
lean_object* v_a_6116_; lean_object* v___x_6118_; uint8_t v_isShared_6119_; uint8_t v_isSharedCheck_6123_; 
lean_dec(v___x_6104_);
v_a_6116_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6123_ == 0)
{
v___x_6118_ = v___x_6105_;
v_isShared_6119_ = v_isSharedCheck_6123_;
goto v_resetjp_6117_;
}
else
{
lean_inc(v_a_6116_);
lean_dec(v___x_6105_);
v___x_6118_ = lean_box(0);
v_isShared_6119_ = v_isSharedCheck_6123_;
goto v_resetjp_6117_;
}
v_resetjp_6117_:
{
lean_object* v___x_6121_; 
if (v_isShared_6119_ == 0)
{
v___x_6121_ = v___x_6118_;
goto v_reusejp_6120_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v_a_6116_);
v___x_6121_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6120_;
}
v_reusejp_6120_:
{
return v___x_6121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_){
_start:
{
lean_object* v_res_6135_; 
v_res_6135_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
lean_dec(v___y_6125_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_){
_start:
{
lean_object* v___x_6149_; 
v___x_6149_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6136_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
return v___x_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_){
_start:
{
lean_object* v_res_6163_; 
v_res_6163_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
lean_dec(v___y_6155_);
lean_dec_ref(v___y_6154_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6151_);
return v_res_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6164_, lean_object* v___f_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_){
_start:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; 
v___x_6179_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6179_, 0, v___y_6164_);
v___x_6180_ = l_Lean_Meta_Grind_Action_andThen(v___x_6179_, v___f_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
return v___x_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6181_, lean_object* v___f_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_){
_start:
{
lean_object* v_res_6196_; 
v_res_6196_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6181_, v___f_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec(v___y_6186_);
return v_res_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6198_, uint8_t v_compress_6199_, lean_object* v_goal_6200_, lean_object* v_kna_6201_, lean_object* v_kp_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_, lean_object* v_a_6211_){
_start:
{
lean_object* v_toGoalState_6213_; lean_object* v_mvarId_6214_; lean_object* v___f_6215_; lean_object* v___x_6216_; 
v_toGoalState_6213_ = lean_ctor_get(v_goal_6200_, 0);
lean_inc_ref(v_toGoalState_6213_);
v_mvarId_6214_ = lean_ctor_get(v_goal_6200_, 1);
lean_inc(v_mvarId_6214_);
v___f_6215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_6215_, 0, v_goal_6200_);
v___x_6216_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6214_, v___f_6215_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_);
if (lean_obj_tag(v___x_6216_) == 0)
{
lean_object* v_a_6217_; lean_object* v_fst_6218_; 
v_a_6217_ = lean_ctor_get(v___x_6216_, 0);
lean_inc(v_a_6217_);
lean_dec_ref_known(v___x_6216_, 1);
v_fst_6218_ = lean_ctor_get(v_a_6217_, 0);
if (lean_obj_tag(v_fst_6218_) == 1)
{
lean_object* v_split_6219_; lean_object* v_snd_6220_; lean_object* v_c_6221_; lean_object* v_numCases_6222_; uint8_t v_isRec_6223_; lean_object* v_candidates_6224_; lean_object* v___f_6225_; lean_object* v___y_6227_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; uint8_t v___y_6239_; uint8_t v___x_6241_; 
lean_inc_ref(v_fst_6218_);
v_split_6219_ = lean_ctor_get(v_toGoalState_6213_, 14);
lean_inc_ref(v_split_6219_);
lean_dec_ref(v_toGoalState_6213_);
v_snd_6220_ = lean_ctor_get(v_a_6217_, 1);
lean_inc(v_snd_6220_);
lean_dec(v_a_6217_);
v_c_6221_ = lean_ctor_get(v_fst_6218_, 0);
lean_inc_ref(v_c_6221_);
v_numCases_6222_ = lean_ctor_get(v_fst_6218_, 1);
lean_inc(v_numCases_6222_);
v_isRec_6223_ = lean_ctor_get_uint8(v_fst_6218_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6218_, 2);
v_candidates_6224_ = lean_ctor_get(v_split_6219_, 1);
lean_inc(v_candidates_6224_);
lean_dec_ref(v_split_6219_);
v___f_6225_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_6235_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6221_);
v___x_6236_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6220_, v___x_6235_);
lean_dec_ref(v___x_6235_);
v___x_6237_ = lean_unsigned_to_nat(1u);
v___x_6241_ = lean_nat_dec_lt(v___x_6237_, v_numCases_6222_);
if (v___x_6241_ == 0)
{
v___y_6239_ = v_isRec_6223_;
goto v___jp_6238_;
}
else
{
v___y_6239_ = v___x_6241_;
goto v___jp_6238_;
}
v___jp_6226_:
{
lean_object* v___f_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___f_6228_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6228_, 0, v___y_6227_);
lean_closure_set(v___f_6228_, 1, v___f_6225_);
v___x_6229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6229_, 0, v_candidates_6224_);
v___x_6230_ = lean_box(v_isRec_6223_);
v___x_6231_ = lean_box(v_stopAtFirstFailure_6198_);
v___x_6232_ = lean_box(v_compress_6199_);
v___x_6233_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6233_, 0, v_c_6221_);
lean_closure_set(v___x_6233_, 1, v_numCases_6222_);
lean_closure_set(v___x_6233_, 2, v___x_6230_);
lean_closure_set(v___x_6233_, 3, v___x_6231_);
lean_closure_set(v___x_6233_, 4, v___x_6232_);
lean_closure_set(v___x_6233_, 5, v___x_6229_);
v___x_6234_ = l_Lean_Meta_Grind_Action_andThen(v___x_6233_, v___f_6228_, v_snd_6220_, v_kna_6201_, v_kp_6202_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_);
return v___x_6234_;
}
v___jp_6238_:
{
if (v___y_6239_ == 0)
{
v___y_6227_ = v___x_6236_;
goto v___jp_6226_;
}
else
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_nat_add(v___x_6236_, v___x_6237_);
lean_dec(v___x_6236_);
v___y_6227_ = v___x_6240_;
goto v___jp_6226_;
}
}
}
else
{
lean_object* v_snd_6242_; lean_object* v___x_6243_; 
lean_dec_ref(v_toGoalState_6213_);
lean_dec_ref(v_kp_6202_);
v_snd_6242_ = lean_ctor_get(v_a_6217_, 1);
lean_inc(v_snd_6242_);
lean_dec(v_a_6217_);
lean_inc(v_a_6211_);
lean_inc_ref(v_a_6210_);
lean_inc(v_a_6209_);
lean_inc_ref(v_a_6208_);
lean_inc(v_a_6207_);
lean_inc_ref(v_a_6206_);
lean_inc(v_a_6205_);
lean_inc_ref(v_a_6204_);
lean_inc(v_a_6203_);
v___x_6243_ = lean_apply_11(v_kna_6201_, v_snd_6242_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_, lean_box(0));
return v___x_6243_;
}
}
else
{
lean_object* v_a_6244_; lean_object* v___x_6246_; uint8_t v_isShared_6247_; uint8_t v_isSharedCheck_6251_; 
lean_dec_ref(v_toGoalState_6213_);
lean_dec_ref(v_kp_6202_);
lean_dec_ref(v_kna_6201_);
v_a_6244_ = lean_ctor_get(v___x_6216_, 0);
v_isSharedCheck_6251_ = !lean_is_exclusive(v___x_6216_);
if (v_isSharedCheck_6251_ == 0)
{
v___x_6246_ = v___x_6216_;
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
else
{
lean_inc(v_a_6244_);
lean_dec(v___x_6216_);
v___x_6246_ = lean_box(0);
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
v_resetjp_6245_:
{
lean_object* v___x_6249_; 
if (v_isShared_6247_ == 0)
{
v___x_6249_ = v___x_6246_;
goto v_reusejp_6248_;
}
else
{
lean_object* v_reuseFailAlloc_6250_; 
v_reuseFailAlloc_6250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
v___x_6249_ = v_reuseFailAlloc_6250_;
goto v_reusejp_6248_;
}
v_reusejp_6248_:
{
return v___x_6249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6252_, lean_object* v_compress_6253_, lean_object* v_goal_6254_, lean_object* v_kna_6255_, lean_object* v_kp_6256_, lean_object* v_a_6257_, lean_object* v_a_6258_, lean_object* v_a_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_, lean_object* v_a_6265_, lean_object* v_a_6266_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6267_; uint8_t v_compress_boxed_6268_; lean_object* v_res_6269_; 
v_stopAtFirstFailure_boxed_6267_ = lean_unbox(v_stopAtFirstFailure_6252_);
v_compress_boxed_6268_ = lean_unbox(v_compress_6253_);
v_res_6269_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6267_, v_compress_boxed_6268_, v_goal_6254_, v_kna_6255_, v_kp_6256_, v_a_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_, v_a_6264_, v_a_6265_);
lean_dec(v_a_6265_);
lean_dec_ref(v_a_6264_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
lean_dec(v_a_6259_);
lean_dec_ref(v_a_6258_);
lean_dec(v_a_6257_);
return v_res_6269_;
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
