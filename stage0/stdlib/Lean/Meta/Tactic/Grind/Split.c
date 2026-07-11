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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_9463__boxed_668_; uint8_t v_d_boxed_669_; lean_object* v_res_670_; 
v___x_9463__boxed_668_ = lean_unbox(v___x_653_);
v_d_boxed_669_ = lean_unbox(v_d_654_);
v_res_670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_652_, v___x_9463__boxed_668_, v_d_boxed_669_, v_a_655_, v_x_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
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
lean_object* v___x_1084_; lean_object* v_env_1085_; uint8_t v___y_1087_; uint8_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1084_ = lean_st_ref_get(v___y_1082_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1143_ = l_Lean_Name_isAnonymous(v_declHint_1081_);
v___x_1144_ = lean_bool_not(v___x_1143_);
if (v___x_1144_ == 0)
{
v___y_1087_ = v___x_1144_;
goto v___jp_1086_;
}
else
{
uint8_t v_isExporting_1145_; 
v_isExporting_1145_ = lean_ctor_get_uint8(v_env_1085_, sizeof(void*)*8);
v___y_1087_ = v_isExporting_1145_;
goto v___jp_1086_;
}
v___jp_1086_:
{
if (v___y_1087_ == 0)
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
uint8_t v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = 0;
lean_inc_ref(v_env_1085_);
v___x_1090_ = l_Lean_Environment_setExporting(v_env_1085_, v___x_1089_);
lean_inc(v_declHint_1081_);
lean_inc_ref(v___x_1090_);
v___x_1091_ = l_Lean_Environment_contains(v___x_1090_, v_declHint_1081_, v___y_1087_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v___x_1090_);
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_msg_1080_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_c_1098_; lean_object* v___x_1099_; 
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1094_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1095_ = l_Lean_Options_empty;
v___x_1096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1090_);
lean_ctor_set(v___x_1096_, 1, v___x_1093_);
lean_ctor_set(v___x_1096_, 2, v___x_1094_);
lean_ctor_set(v___x_1096_, 3, v___x_1095_);
lean_inc(v_declHint_1081_);
v___x_1097_ = l_Lean_MessageData_ofConstName(v_declHint_1081_, v___x_1089_);
v_c_1098_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1098_, 0, v___x_1096_);
lean_ctor_set(v_c_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1085_, v_declHint_1081_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec_ref(v_env_1085_);
lean_dec(v_declHint_1081_);
v___x_1100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_c_1098_);
v___x_1102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_MessageData_note(v___x_1103_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v_msg_1080_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v_val_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1142_; 
v_val_1107_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1109_ = v___x_1099_;
v_isShared_1110_ = v_isSharedCheck_1142_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_val_1107_);
lean_dec(v___x_1099_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1142_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_mod_1114_; uint8_t v___x_1115_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Lean_Environment_header(v_env_1085_);
lean_dec_ref(v_env_1085_);
v___x_1113_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1112_);
v_mod_1114_ = lean_array_get(v___x_1111_, v___x_1113_, v_val_1107_);
lean_dec(v_val_1107_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_Lean_isPrivateName(v_declHint_1081_);
lean_dec(v_declHint_1081_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_c_1098_);
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_ofName(v_mod_1114_);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_MessageData_note(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1080_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1125_);
v___x_1127_ = v___x_1109_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v_c_1098_);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_MessageData_ofName(v_mod_1114_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_MessageData_note(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_msg_1080_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1138_);
v___x_1140_ = v___x_1109_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1146_, lean_object* v_declHint_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1146_, v_declHint_1147_, v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1151_, lean_object* v_declHint_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v___x_1164_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1151_, v_declHint_1152_, v___y_1162_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = l_Lean_unknownIdentifierMessageTag;
v___x_1170_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v___y_1177_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; lean_object* v___x_1197_; lean_object* v_mctx_1198_; lean_object* v_lctx_1199_; lean_object* v_options_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1197_ = lean_st_ref_get(v___y_1191_);
v_mctx_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc_ref(v_mctx_1198_);
lean_dec(v___x_1197_);
v_lctx_1199_ = lean_ctor_get(v___y_1190_, 2);
v_options_1200_ = lean_ctor_get(v___y_1192_, 2);
lean_inc_ref(v_options_1200_);
lean_inc_ref(v_lctx_1199_);
v___x_1201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1201_, 0, v_env_1196_);
lean_ctor_set(v___x_1201_, 1, v_mctx_1198_);
lean_ctor_set(v___x_1201_, 2, v_lctx_1199_);
lean_ctor_set(v___x_1201_, 3, v_options_1200_);
v___x_1202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_msgData_1189_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_ref_1217_; lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_ref_1217_ = lean_ctor_get(v___y_1214_, 5);
v___x_1218_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_inc(v_ref_1217_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_ref_1217_);
lean_ctor_set(v___x_1223_, 1, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_fileName_1248_; lean_object* v_fileMap_1249_; lean_object* v_options_1250_; lean_object* v_currRecDepth_1251_; lean_object* v_maxRecDepth_1252_; lean_object* v_ref_1253_; lean_object* v_currNamespace_1254_; lean_object* v_openDecls_1255_; lean_object* v_initHeartbeats_1256_; lean_object* v_maxHeartbeats_1257_; lean_object* v_quotContext_1258_; lean_object* v_currMacroScope_1259_; uint8_t v_diag_1260_; lean_object* v_cancelTk_x3f_1261_; uint8_t v_suppressElabErrors_1262_; lean_object* v_inheritedTraceOptions_1263_; lean_object* v_ref_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_fileName_1248_ = lean_ctor_get(v___y_1245_, 0);
v_fileMap_1249_ = lean_ctor_get(v___y_1245_, 1);
v_options_1250_ = lean_ctor_get(v___y_1245_, 2);
v_currRecDepth_1251_ = lean_ctor_get(v___y_1245_, 3);
v_maxRecDepth_1252_ = lean_ctor_get(v___y_1245_, 4);
v_ref_1253_ = lean_ctor_get(v___y_1245_, 5);
v_currNamespace_1254_ = lean_ctor_get(v___y_1245_, 6);
v_openDecls_1255_ = lean_ctor_get(v___y_1245_, 7);
v_initHeartbeats_1256_ = lean_ctor_get(v___y_1245_, 8);
v_maxHeartbeats_1257_ = lean_ctor_get(v___y_1245_, 9);
v_quotContext_1258_ = lean_ctor_get(v___y_1245_, 10);
v_currMacroScope_1259_ = lean_ctor_get(v___y_1245_, 11);
v_diag_1260_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*14);
v_cancelTk_x3f_1261_ = lean_ctor_get(v___y_1245_, 12);
v_suppressElabErrors_1262_ = lean_ctor_get_uint8(v___y_1245_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1263_ = lean_ctor_get(v___y_1245_, 13);
v_ref_1264_ = l_Lean_replaceRef(v_ref_1235_, v_ref_1253_);
lean_inc_ref(v_inheritedTraceOptions_1263_);
lean_inc(v_cancelTk_x3f_1261_);
lean_inc(v_currMacroScope_1259_);
lean_inc(v_quotContext_1258_);
lean_inc(v_maxHeartbeats_1257_);
lean_inc(v_initHeartbeats_1256_);
lean_inc(v_openDecls_1255_);
lean_inc(v_currNamespace_1254_);
lean_inc(v_maxRecDepth_1252_);
lean_inc(v_currRecDepth_1251_);
lean_inc_ref(v_options_1250_);
lean_inc_ref(v_fileMap_1249_);
lean_inc_ref(v_fileName_1248_);
v___x_1265_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1265_, 0, v_fileName_1248_);
lean_ctor_set(v___x_1265_, 1, v_fileMap_1249_);
lean_ctor_set(v___x_1265_, 2, v_options_1250_);
lean_ctor_set(v___x_1265_, 3, v_currRecDepth_1251_);
lean_ctor_set(v___x_1265_, 4, v_maxRecDepth_1252_);
lean_ctor_set(v___x_1265_, 5, v_ref_1264_);
lean_ctor_set(v___x_1265_, 6, v_currNamespace_1254_);
lean_ctor_set(v___x_1265_, 7, v_openDecls_1255_);
lean_ctor_set(v___x_1265_, 8, v_initHeartbeats_1256_);
lean_ctor_set(v___x_1265_, 9, v_maxHeartbeats_1257_);
lean_ctor_set(v___x_1265_, 10, v_quotContext_1258_);
lean_ctor_set(v___x_1265_, 11, v_currMacroScope_1259_);
lean_ctor_set(v___x_1265_, 12, v_cancelTk_x3f_1261_);
lean_ctor_set(v___x_1265_, 13, v_inheritedTraceOptions_1263_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*14, v_diag_1260_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*14 + 1, v_suppressElabErrors_1262_);
v___x_1266_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1236_, v___y_1243_, v___y_1244_, v___x_1265_, v___y_1246_);
lean_dec_ref_known(v___x_1265_, 14);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1267_, lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1267_, v_msg_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v_ref_1267_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1281_, lean_object* v_msg_1282_, lean_object* v_declHint_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_a_1296_; lean_object* v___x_1297_; 
v___x_1295_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1282_, v_declHint_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1281_, v_a_1296_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1298_, lean_object* v_msg_1299_, lean_object* v_declHint_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1298_, v_msg_1299_, v_declHint_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v_ref_1298_);
return v_res_1312_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1319_, lean_object* v_constName_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1332_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1333_ = 0;
lean_inc(v_constName_1320_);
v___x_1334_ = l_Lean_MessageData_ofConstName(v_constName_1320_, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1332_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1319_, v___x_1337_, v_constName_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1339_, lean_object* v_constName_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1339_, v_constName_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec(v_ref_1339_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_ref_1365_; lean_object* v___x_1366_; 
v_ref_1365_ = lean_ctor_get(v___y_1362_, 5);
v___x_1366_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1365_, v_constName_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec(v___y_1368_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v_env_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_st_ref_get(v___y_1390_);
v_env_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_env_1393_);
lean_dec(v___x_1392_);
v___x_1394_ = 0;
lean_inc(v_constName_1380_);
v___x_1395_ = l_Lean_Environment_find_x3f(v_env_1393_, v_constName_1380_, v___x_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1396_;
}
else
{
lean_object* v_val_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_constName_1380_);
v_val_1397_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1395_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_val_1397_);
lean_dec(v___x_1395_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 0);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1417_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1418_; double v___x_1419_; 
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = lean_float_of_nat(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1423_, lean_object* v_msg_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_ref_1430_; lean_object* v___x_1431_; lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1476_; 
v_ref_1430_ = lean_ctor_get(v___y_1427_, 5);
v___x_1431_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1476_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1476_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v_traceState_1437_; lean_object* v_env_1438_; lean_object* v_nextMacroScope_1439_; lean_object* v_ngen_1440_; lean_object* v_auxDeclNGen_1441_; lean_object* v_cache_1442_; lean_object* v_messages_1443_; lean_object* v_infoState_1444_; lean_object* v_snapshotTasks_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1475_; 
v___x_1436_ = lean_st_ref_take(v___y_1428_);
v_traceState_1437_ = lean_ctor_get(v___x_1436_, 4);
v_env_1438_ = lean_ctor_get(v___x_1436_, 0);
v_nextMacroScope_1439_ = lean_ctor_get(v___x_1436_, 1);
v_ngen_1440_ = lean_ctor_get(v___x_1436_, 2);
v_auxDeclNGen_1441_ = lean_ctor_get(v___x_1436_, 3);
v_cache_1442_ = lean_ctor_get(v___x_1436_, 5);
v_messages_1443_ = lean_ctor_get(v___x_1436_, 6);
v_infoState_1444_ = lean_ctor_get(v___x_1436_, 7);
v_snapshotTasks_1445_ = lean_ctor_get(v___x_1436_, 8);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1447_ = v___x_1436_;
v_isShared_1448_ = v_isSharedCheck_1475_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_snapshotTasks_1445_);
lean_inc(v_infoState_1444_);
lean_inc(v_messages_1443_);
lean_inc(v_cache_1442_);
lean_inc(v_traceState_1437_);
lean_inc(v_auxDeclNGen_1441_);
lean_inc(v_ngen_1440_);
lean_inc(v_nextMacroScope_1439_);
lean_inc(v_env_1438_);
lean_dec(v___x_1436_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1475_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
uint64_t v_tid_1449_; lean_object* v_traces_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1474_; 
v_tid_1449_ = lean_ctor_get_uint64(v_traceState_1437_, sizeof(void*)*1);
v_traces_1450_ = lean_ctor_get(v_traceState_1437_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_traceState_1437_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1452_ = v_traceState_1437_;
v_isShared_1453_ = v_isSharedCheck_1474_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_traces_1450_);
lean_dec(v_traceState_1437_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1474_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; double v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1454_ = lean_box(0);
v___x_1455_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1456_ = 0;
v___x_1457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1458_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1458_, 0, v_cls_1423_);
lean_ctor_set(v___x_1458_, 1, v___x_1454_);
lean_ctor_set(v___x_1458_, 2, v___x_1457_);
lean_ctor_set_float(v___x_1458_, sizeof(void*)*3, v___x_1455_);
lean_ctor_set_float(v___x_1458_, sizeof(void*)*3 + 8, v___x_1455_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*3 + 16, v___x_1456_);
v___x_1459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1460_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v_a_1432_);
lean_ctor_set(v___x_1460_, 2, v___x_1459_);
lean_inc(v_ref_1430_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_ref_1430_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_PersistentArray_push___redArg(v_traces_1450_, v___x_1461_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1462_);
v___x_1464_ = v___x_1452_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1462_);
lean_ctor_set_uint64(v_reuseFailAlloc_1473_, sizeof(void*)*1, v_tid_1449_);
v___x_1464_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v___x_1464_);
v___x_1466_ = v___x_1447_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_env_1438_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_nextMacroScope_1439_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_ngen_1440_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_auxDeclNGen_1441_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_cache_1442_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_messages_1443_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_infoState_1444_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_snapshotTasks_1445_);
v___x_1466_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_st_ref_set(v___y_1428_, v___x_1466_);
v___x_1468_ = lean_box(0);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1468_);
v___x_1470_ = v___x_1434_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1477_, v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1503_ = l_Lean_Name_append(v___x_1502_, v___x_1501_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
uint8_t v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; uint8_t v___y_1654_; lean_object* v___x_1768_; 
lean_inc_ref(v_e_1516_);
v___x_1768_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1516_, v_a_1524_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1810_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1810_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1810_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = l_Lean_Expr_cleanupAnnotations(v_a_1769_);
v___x_1787_ = l_Lean_Expr_isApp(v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1786_);
lean_del_object(v___x_1771_);
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
v___y_1781_ = v_a_1524_;
v___y_1782_ = v_a_1525_;
v___y_1783_ = v_a_1526_;
goto v___jp_1773_;
}
else
{
lean_object* v_arg_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_arg_1788_ = lean_ctor_get(v___x_1786_, 1);
lean_inc_ref(v_arg_1788_);
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1786_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1788_);
lean_del_object(v___x_1771_);
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
v___y_1781_ = v_a_1524_;
v___y_1782_ = v_a_1525_;
v___y_1783_ = v_a_1526_;
goto v___jp_1773_;
}
else
{
lean_object* v_arg_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_arg_1791_ = lean_ctor_get(v___x_1789_, 1);
lean_inc_ref(v_arg_1791_);
v___x_1792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1794_ = l_Lean_Expr_isConstOf(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1796_ = l_Lean_Expr_isConstOf(v___x_1792_, v___x_1795_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Expr_isApp(v___x_1792_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_del_object(v___x_1771_);
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
v___y_1781_ = v_a_1524_;
v___y_1782_ = v_a_1525_;
v___y_1783_ = v_a_1526_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1792_);
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1800_ = l_Lean_Expr_isConstOf(v___x_1798_, v___x_1799_);
lean_dec_ref(v___x_1798_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_del_object(v___x_1771_);
v___y_1774_ = v_a_1517_;
v___y_1775_ = v_a_1518_;
v___y_1776_ = v_a_1519_;
v___y_1777_ = v_a_1520_;
v___y_1778_ = v_a_1521_;
v___y_1779_ = v_a_1522_;
v___y_1780_ = v_a_1523_;
v___y_1781_ = v_a_1524_;
v___y_1782_ = v_a_1525_;
v___y_1783_ = v_a_1526_;
goto v___jp_1773_;
}
else
{
uint8_t v___x_1801_; 
lean_inc_ref(v_e_1516_);
v___x_1801_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1516_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_e_1516_);
v___x_1802_ = lean_unsigned_to_nat(2u);
v___x_1803_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*1, v___x_1801_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*1 + 1, v___x_1801_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1803_);
v___x_1805_ = v___x_1771_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1771_);
v___x_1807_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1516_, v_arg_1791_, v_arg_1788_, v_a_1517_, v_a_1521_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1807_;
}
}
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v___x_1792_);
lean_del_object(v___x_1771_);
v___x_1808_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1516_, v_arg_1791_, v_arg_1788_, v_a_1517_, v_a_1521_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1808_;
}
}
else
{
lean_object* v___x_1809_; 
lean_dec_ref(v___x_1792_);
lean_del_object(v___x_1771_);
v___x_1809_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1516_, v_arg_1791_, v_arg_1788_, v_a_1517_, v_a_1521_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1809_;
}
}
}
v___jp_1773_:
{
uint8_t v___x_1784_; 
v___x_1784_ = l_Lean_Meta_Grind_isIte(v_e_1516_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Lean_Meta_Grind_isDIte(v_e_1516_);
v___y_1644_ = v___y_1781_;
v___y_1645_ = v___y_1777_;
v___y_1646_ = v___y_1776_;
v___y_1647_ = v___y_1783_;
v___y_1648_ = v___y_1778_;
v___y_1649_ = v___y_1774_;
v___y_1650_ = v___y_1775_;
v___y_1651_ = v___y_1782_;
v___y_1652_ = v___y_1780_;
v___y_1653_ = v___y_1779_;
v___y_1654_ = v___x_1785_;
goto v___jp_1643_;
}
else
{
v___y_1644_ = v___y_1781_;
v___y_1645_ = v___y_1777_;
v___y_1646_ = v___y_1776_;
v___y_1647_ = v___y_1783_;
v___y_1648_ = v___y_1778_;
v___y_1649_ = v___y_1774_;
v___y_1650_ = v___y_1775_;
v___y_1651_ = v___y_1782_;
v___y_1652_ = v___y_1780_;
v___y_1653_ = v___y_1779_;
v___y_1654_ = v___x_1784_;
goto v___jp_1643_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_e_1516_);
v_a_1811_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1768_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1768_);
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
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
v___jp_1534_:
{
uint8_t v___x_1546_; 
v___x_1546_ = l_Lean_Expr_isFVar(v_e_1516_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref(v_e_1516_);
v___x_1547_ = lean_box(1);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; 
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc_ref(v_e_1516_);
v___x_1549_ = lean_infer_type(v_e_1516_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = l_Lean_Meta_whnfD(v_a_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_n(v_a_1552_, 2);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1554_ = l_Lean_MessageData_ofExpr(v_e_1516_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_indentExpr(v_a_1552_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_Expr_getAppFn(v_a_1552_);
lean_dec(v_a_1552_);
if (lean_obj_tag(v___x_1560_) == 4)
{
lean_object* v_declName_1561_; lean_object* v___x_1562_; 
v_declName_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_declName_1561_);
lean_dec_ref_known(v___x_1560_, 2);
v___x_1562_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1561_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1595_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1595_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1595_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
if (lean_obj_tag(v_a_1563_) == 5)
{
lean_object* v_val_1567_; lean_object* v_ctors_1568_; uint8_t v_isRec_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1559_, 2);
v_val_1567_ = lean_ctor_get(v_a_1563_, 0);
lean_inc_ref(v_val_1567_);
lean_dec_ref_known(v_a_1563_, 1);
v_ctors_1568_ = lean_ctor_get(v_val_1567_, 4);
lean_inc(v_ctors_1568_);
v_isRec_1569_ = lean_ctor_get_uint8(v_val_1567_, sizeof(void*)*6);
lean_dec_ref(v_val_1567_);
v___x_1570_ = l_List_lengthTR___redArg(v_ctors_1568_);
lean_dec(v_ctors_1568_);
v___x_1571_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*1, v_isRec_1569_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*1 + 1, v___y_1535_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1571_);
v___x_1573_ = v___x_1565_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1575_; 
lean_del_object(v___x_1565_);
lean_dec(v_a_1563_);
v___x_1575_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1540_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; uint8_t v_verbose_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v_verbose_1577_ = lean_ctor_get_uint8(v_a_1576_, 0);
lean_dec(v_a_1576_);
if (v_verbose_1577_ == 0)
{
lean_dec_ref_known(v___x_1559_, 2);
goto v___jp_1531_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_Sym_reportIssue(v___x_1559_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_dec_ref_known(v___x_1578_, 1);
goto v___jp_1531_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref_known(v___x_1559_, 2);
v_a_1587_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1575_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1575_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref_known(v___x_1559_, 2);
v_a_1596_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1562_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1562_);
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
else
{
lean_object* v___x_1604_; 
lean_dec_ref(v___x_1560_);
v___x_1604_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1540_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; uint8_t v_verbose_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v_verbose_1606_ = lean_ctor_get_uint8(v_a_1605_, 0);
lean_dec(v_a_1605_);
if (v_verbose_1606_ == 0)
{
lean_dec_ref_known(v___x_1559_, 2);
goto v___jp_1528_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Meta_Sym_reportIssue(v___x_1559_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_dec_ref_known(v___x_1607_, 1);
goto v___jp_1528_;
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref_known(v___x_1559_, 2);
v_a_1616_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1604_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1604_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_e_1516_);
v_a_1624_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1551_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1551_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_e_1516_);
v_a_1632_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1549_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1549_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
v___jp_1643_:
{
if (v___y_1654_ == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1516_, v___y_1649_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; uint8_t v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = lean_unbox(v_a_1656_);
lean_dec(v_a_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_inc_ref(v_e_1516_);
v___x_1658_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1516_, v___y_1649_, v___y_1650_, v___y_1646_, v___y_1645_, v___y_1648_, v___y_1653_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1718_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1718_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1718_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_unbox(v_a_1659_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v_env_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_st_ref_get(v___y_1647_);
v_env_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref(v_env_1665_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1665_, v_e_1516_);
if (lean_obj_tag(v___x_1666_) == 1)
{
lean_object* v_val_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1673_; 
lean_dec_ref(v_e_1516_);
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1667_);
lean_dec(v_val_1667_);
v___x_1669_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_unbox(v_a_1659_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1, v___x_1670_);
v___x_1671_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1 + 1, v___x_1671_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1669_);
v___x_1673_ = v___x_1661_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1669_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v___x_1666_);
lean_del_object(v___x_1661_);
v___x_1675_ = l_Lean_Expr_getAppFn(v_e_1516_);
if (lean_obj_tag(v___x_1675_) == 4)
{
lean_object* v_declName_1676_; lean_object* v___x_1677_; 
v_declName_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_declName_1676_);
lean_dec_ref_known(v___x_1675_, 2);
v___x_1677_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1676_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
if (lean_obj_tag(v_a_1678_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1680_; 
v_val_1679_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v_a_1678_, 1);
lean_inc_ref(v_e_1516_);
v___x_1680_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1516_, v___y_1649_, v___y_1648_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1695_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
if (v___x_1685_ == 0)
{
uint8_t v___x_1686_; 
lean_del_object(v___x_1683_);
lean_dec(v_val_1679_);
v___x_1686_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
v___y_1535_ = v___x_1686_;
v___y_1536_ = v___y_1649_;
v___y_1537_ = v___y_1650_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1648_;
v___y_1541_ = v___y_1653_;
v___y_1542_ = v___y_1652_;
v___y_1543_ = v___y_1644_;
v___y_1544_ = v___y_1651_;
v___y_1545_ = v___y_1647_;
goto v___jp_1534_;
}
else
{
lean_object* v_ctors_1687_; uint8_t v_isRec_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1693_; 
lean_dec_ref(v_e_1516_);
v_ctors_1687_ = lean_ctor_get(v_val_1679_, 4);
lean_inc(v_ctors_1687_);
v_isRec_1688_ = lean_ctor_get_uint8(v_val_1679_, sizeof(void*)*6);
lean_dec(v_val_1679_);
v___x_1689_ = l_List_lengthTR___redArg(v_ctors_1687_);
lean_dec(v_ctors_1687_);
v___x_1690_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*1, v_isRec_1688_);
v___x_1691_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*1 + 1, v___x_1691_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1690_);
v___x_1693_ = v___x_1683_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
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
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_val_1679_);
lean_dec(v_a_1659_);
lean_dec_ref(v_e_1516_);
v_a_1696_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1680_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1680_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
uint8_t v___x_1704_; 
lean_dec(v_a_1678_);
v___x_1704_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
v___y_1535_ = v___x_1704_;
v___y_1536_ = v___y_1649_;
v___y_1537_ = v___y_1650_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1648_;
v___y_1541_ = v___y_1653_;
v___y_1542_ = v___y_1652_;
v___y_1543_ = v___y_1644_;
v___y_1544_ = v___y_1651_;
v___y_1545_ = v___y_1647_;
goto v___jp_1534_;
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_a_1659_);
lean_dec_ref(v_e_1516_);
v_a_1705_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1677_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1677_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
uint8_t v___x_1713_; 
lean_dec_ref(v___x_1675_);
v___x_1713_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
v___y_1535_ = v___x_1713_;
v___y_1536_ = v___y_1649_;
v___y_1537_ = v___y_1650_;
v___y_1538_ = v___y_1646_;
v___y_1539_ = v___y_1645_;
v___y_1540_ = v___y_1648_;
v___y_1541_ = v___y_1653_;
v___y_1542_ = v___y_1652_;
v___y_1543_ = v___y_1644_;
v___y_1544_ = v___y_1651_;
v___y_1545_ = v___y_1647_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_a_1659_);
lean_dec_ref(v_e_1516_);
v___x_1714_ = lean_box(0);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1714_);
v___x_1716_ = v___x_1661_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_e_1516_);
v_a_1719_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1658_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1658_);
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
lean_object* v_options_1727_; uint8_t v_hasTrace_1728_; 
v_options_1727_ = lean_ctor_get(v___y_1651_, 2);
v_hasTrace_1728_ = lean_ctor_get_uint8(v_options_1727_, sizeof(void*)*1);
if (v_hasTrace_1728_ == 0)
{
lean_dec_ref(v_e_1516_);
goto v___jp_1640_;
}
else
{
lean_object* v_inheritedTraceOptions_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_inheritedTraceOptions_1729_ = lean_ctor_get(v___y_1651_, 13);
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1729_, v_options_1727_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_dec_ref(v_e_1516_);
goto v___jp_1640_;
}
else
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Meta_Grind_updateLastTag(v___y_1649_, v___y_1650_, v___y_1646_, v___y_1645_, v___y_1648_, v___y_1653_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1735_ = l_Lean_MessageData_ofExpr(v_e_1516_);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1730_, v___x_1736_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_dec_ref_known(v___x_1737_, 1);
goto v___jp_1640_;
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
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
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_e_1516_);
v_a_1746_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1733_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1733_);
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
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_e_1516_);
v_a_1754_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1655_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1655_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = l_Lean_Expr_getAppNumArgs(v_e_1516_);
v___x_1764_ = lean_nat_sub(v___x_1763_, v___x_1762_);
lean_dec(v___x_1763_);
v___x_1765_ = lean_nat_sub(v___x_1764_, v___x_1762_);
lean_dec(v___x_1764_);
v___x_1766_ = l_Lean_Expr_getRevArg_x21(v_e_1516_, v___x_1765_);
lean_dec_ref(v_e_1516_);
v___x_1767_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1766_, v___y_1649_, v___y_1648_, v___y_1652_, v___y_1644_, v___y_1651_, v___y_1647_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec(v_a_1820_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1832_, lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1832_, v_msg_1833_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1846_, lean_object* v_msg_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1846_, v_msg_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1860_, lean_object* v_constName_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_constName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1874_, v_constName_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1888_, lean_object* v_ref_1889_, lean_object* v_constName_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1889_, v_constName_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_ref_1904_, lean_object* v_constName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1903_, v_ref_1904_, v_constName_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec(v_ref_1904_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1918_, lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v_declHint_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1919_, v_msg_1920_, v_declHint_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_ref_1935_, lean_object* v_msg_1936_, lean_object* v_declHint_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1934_, v_ref_1935_, v_msg_1936_, v_declHint_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v_ref_1935_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1950_, lean_object* v_declHint_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1950_, v_declHint_1951_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1964_, lean_object* v_declHint_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1964_, v_declHint_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec(v___y_1966_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1978_, lean_object* v_ref_1979_, lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1979_, v_msg_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_ref_1994_, lean_object* v_msg_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1993_, v_ref_1994_, v_msg_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec(v_ref_1994_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2008_, lean_object* v_msg_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2009_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2022_, v_msg_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_box(0);
return v___x_2038_;
}
else
{
lean_object* v_key_2039_; lean_object* v_value_2040_; lean_object* v_tail_2041_; uint8_t v___y_2043_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; uint8_t v___x_2050_; 
v_key_2039_ = lean_ctor_get(v_x_2037_, 0);
v_value_2040_ = lean_ctor_get(v_x_2037_, 1);
v_tail_2041_ = lean_ctor_get(v_x_2037_, 2);
v_fst_2046_ = lean_ctor_get(v_key_2039_, 0);
v_snd_2047_ = lean_ctor_get(v_key_2039_, 1);
v_fst_2048_ = lean_ctor_get(v_a_2036_, 0);
v_snd_2049_ = lean_ctor_get(v_a_2036_, 1);
v___x_2050_ = lean_expr_eqv(v_fst_2046_, v_fst_2048_);
if (v___x_2050_ == 0)
{
v___y_2043_ = v___x_2050_;
goto v___jp_2042_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_expr_eqv(v_snd_2047_, v_snd_2049_);
v___y_2043_ = v___x_2051_;
goto v___jp_2042_;
}
v___jp_2042_:
{
if (v___y_2043_ == 0)
{
v_x_2037_ = v_tail_2041_;
goto _start;
}
else
{
lean_object* v___x_2045_; 
lean_inc(v_value_2040_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_value_2040_);
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2052_, lean_object* v_x_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2052_, v_x_2053_);
lean_dec(v_x_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_buckets_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v___x_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v_fold_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_buckets_2057_ = lean_ctor_get(v_m_2055_, 1);
v_fst_2058_ = lean_ctor_get(v_a_2056_, 0);
v_snd_2059_ = lean_ctor_get(v_a_2056_, 1);
v___x_2060_ = lean_array_get_size(v_buckets_2057_);
v___x_2061_ = l_Lean_Expr_hash(v_fst_2058_);
v___x_2062_ = l_Lean_Expr_hash(v_snd_2059_);
v___x_2063_ = lean_uint64_mix_hash(v___x_2061_, v___x_2062_);
v___x_2064_ = 32ULL;
v___x_2065_ = lean_uint64_shift_right(v___x_2063_, v___x_2064_);
v_fold_2066_ = lean_uint64_xor(v___x_2063_, v___x_2065_);
v___x_2067_ = 16ULL;
v___x_2068_ = lean_uint64_shift_right(v_fold_2066_, v___x_2067_);
v___x_2069_ = lean_uint64_xor(v_fold_2066_, v___x_2068_);
v___x_2070_ = lean_uint64_to_usize(v___x_2069_);
v___x_2071_ = lean_usize_of_nat(v___x_2060_);
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_sub(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_usize_land(v___x_2070_, v___x_2073_);
v___x_2075_ = lean_array_uget_borrowed(v_buckets_2057_, v___x_2074_);
v___x_2076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2056_, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2077_, v_a_2078_);
lean_dec_ref(v_a_2078_);
lean_dec_ref(v_m_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2080_, uint8_t v___x_2081_, lean_object* v_fst_2082_, lean_object* v_snd_2083_, lean_object* v___x_2084_, lean_object* v_____r_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2097_ = lean_unsigned_to_nat(2u);
v___x_2098_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*1, v_a_2080_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*1 + 1, v___x_2081_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_fst_2082_);
lean_ctor_set(v___x_2100_, 1, v_snd_2083_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2084_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2099_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2105_ = _args[0];
lean_object* v___x_2106_ = _args[1];
lean_object* v_fst_2107_ = _args[2];
lean_object* v_snd_2108_ = _args[3];
lean_object* v___x_2109_ = _args[4];
lean_object* v_____r_2110_ = _args[5];
lean_object* v___y_2111_ = _args[6];
lean_object* v___y_2112_ = _args[7];
lean_object* v___y_2113_ = _args[8];
lean_object* v___y_2114_ = _args[9];
lean_object* v___y_2115_ = _args[10];
lean_object* v___y_2116_ = _args[11];
lean_object* v___y_2117_ = _args[12];
lean_object* v___y_2118_ = _args[13];
lean_object* v___y_2119_ = _args[14];
lean_object* v___y_2120_ = _args[15];
lean_object* v___y_2121_ = _args[16];
_start:
{
uint8_t v_a_45157__boxed_2122_; uint8_t v___x_45158__boxed_2123_; lean_object* v_res_2124_; 
v_a_45157__boxed_2122_ = lean_unbox(v_a_2105_);
v___x_45158__boxed_2123_ = lean_unbox(v___x_2106_);
v_res_2124_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_45157__boxed_2122_, v___x_45158__boxed_2123_, v_fst_2107_, v_snd_2108_, v___x_2109_, v_____r_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec(v___y_2111_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2125_, lean_object* v_snd_2126_, lean_object* v___x_2127_, lean_object* v___x_2128_, lean_object* v_____r_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2141_ = l_Lean_Expr_appFn_x21(v_fst_2125_);
v___x_2142_ = l_Lean_Expr_appFn_x21(v_snd_2126_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2127_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2128_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2148_, lean_object* v_snd_2149_, lean_object* v___x_2150_, lean_object* v___x_2151_, lean_object* v_____r_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2148_, v_snd_2149_, v___x_2150_, v___x_2151_, v_____r_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
return v_res_2164_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___f_2166_; 
v___x_2165_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2166_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2166_, 0, v___x_2165_);
return v___f_2166_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2172_ = l_Lean_Name_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object* v___y_2191_, lean_object* v_eq_2192_, lean_object* v_a_2193_, lean_object* v_b_2194_, lean_object* v_a_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___y_2208_; lean_object* v___y_2229_; lean_object* v_snd_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2352_; 
v_snd_2232_ = lean_ctor_get(v_a_2195_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_a_2195_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_a_2195_, 0);
lean_dec(v_unused_2353_);
v___x_2234_ = v_a_2195_;
v_isShared_2235_ = v_isSharedCheck_2352_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_snd_2232_);
lean_dec(v_a_2195_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2352_;
goto v_resetjp_2233_;
}
v___jp_2207_:
{
if (lean_obj_tag(v___y_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2219_; 
v_a_2209_ = lean_ctor_get(v___y_2208_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___y_2208_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2211_ = v___y_2208_;
v_isShared_2212_ = v_isSharedCheck_2219_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___y_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2219_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
if (lean_obj_tag(v_a_2209_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; 
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2213_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v_a_2209_, 1);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_a_2213_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v_a_2217_; 
lean_del_object(v___x_2211_);
v_a_2217_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v_a_2209_, 1);
v_a_2195_ = v_a_2217_;
goto _start;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2220_ = lean_ctor_get(v___y_2208_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___y_2208_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___y_2208_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___y_2208_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
v___jp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_box(0);
lean_inc(v___y_2205_);
lean_inc_ref(v___y_2204_);
lean_inc(v___y_2203_);
lean_inc_ref(v___y_2202_);
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
lean_inc(v___y_2197_);
lean_inc(v___y_2196_);
v___x_2231_ = lean_apply_12(v___y_2229_, v___x_2230_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, lean_box(0));
v___y_2208_ = v___x_2231_;
goto v___jp_2207_;
}
v_resetjp_2233_:
{
lean_object* v_snd_2236_; lean_object* v_fst_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2351_; 
v_snd_2236_ = lean_ctor_get(v_snd_2232_, 1);
v_fst_2237_ = lean_ctor_get(v_snd_2232_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_snd_2232_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2239_ = v_snd_2232_;
v_isShared_2240_ = v_isSharedCheck_2351_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_snd_2236_);
lean_inc(v_fst_2237_);
lean_dec(v_snd_2232_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2351_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_fst_2241_; lean_object* v_snd_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2350_; 
v_fst_2241_ = lean_ctor_get(v_snd_2236_, 0);
v_snd_2242_ = lean_ctor_get(v_snd_2236_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_snd_2236_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2244_ = v_snd_2236_;
v_isShared_2245_ = v_isSharedCheck_2350_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_dec(v_snd_2236_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2350_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; uint8_t v___x_2247_; uint8_t v___y_2249_; uint8_t v___x_2348_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = 1;
v___x_2348_ = l_Lean_Expr_isApp(v_fst_2241_);
if (v___x_2348_ == 0)
{
v___y_2249_ = v___x_2348_;
goto v___jp_2248_;
}
else
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Expr_isApp(v_snd_2242_);
v___y_2249_ = v___x_2349_;
goto v___jp_2248_;
}
v___jp_2248_:
{
if (v___y_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v___x_2250_ = lean_unsigned_to_nat(2u);
v___x_2251_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*1, v___y_2249_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*1 + 1, v___y_2249_);
v___x_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
if (v_isShared_2245_ == 0)
{
v___x_2254_ = v___x_2244_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_fst_2241_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_snd_2242_);
v___x_2254_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v___x_2254_);
v___x_2256_ = v___x_2239_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_fst_2237_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2258_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2256_);
lean_ctor_set(v___x_2234_, 0, v___x_2252_);
v___x_2258_ = v___x_2234_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; uint8_t v___x_2266_; 
lean_del_object(v___x_2244_);
lean_del_object(v___x_2239_);
lean_del_object(v___x_2234_);
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_sub(v_fst_2237_, v___x_2263_);
lean_dec(v_fst_2237_);
v___f_2265_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2191_);
lean_inc(v___x_2264_);
v___x_2266_ = l_List_elem___redArg(v___f_2265_, v___x_2264_, v___y_2191_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = l_Lean_Expr_appArg_x21(v_fst_2241_);
v___x_2268_ = l_Lean_Expr_appArg_x21(v_snd_2242_);
v___x_2269_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2267_, v___x_2268_, v___y_2196_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; uint8_t v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = lean_unbox(v_a_2270_);
if (v___x_2271_ == 0)
{
lean_object* v_options_2272_; lean_object* v_inheritedTraceOptions_2273_; uint8_t v_hasTrace_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; 
v_options_2272_ = lean_ctor_get(v___y_2204_, 2);
v_inheritedTraceOptions_2273_ = lean_ctor_get(v___y_2204_, 13);
v_hasTrace_2274_ = lean_ctor_get_uint8(v_options_2272_, sizeof(void*)*1);
v___x_2275_ = lean_box(v___x_2247_);
lean_inc(v___x_2264_);
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_inc(v_a_2270_);
v___f_2276_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed), 17, 5);
lean_closure_set(v___f_2276_, 0, v_a_2270_);
lean_closure_set(v___f_2276_, 1, v___x_2275_);
lean_closure_set(v___f_2276_, 2, v_fst_2241_);
lean_closure_set(v___f_2276_, 3, v_snd_2242_);
lean_closure_set(v___f_2276_, 4, v___x_2264_);
if (v_hasTrace_2274_ == 0)
{
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
v___y_2229_ = v___f_2276_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2277_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2278_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2273_, v_options_2272_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
v___y_2229_ = v___f_2276_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2280_; 
lean_dec_ref(v___f_2276_);
v___x_2280_ = l_Lean_Meta_Grind_updateLastTag(v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v___x_2281_; 
lean_dec_ref_known(v___x_2280_, 1);
v___x_2281_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2192_, v___y_2196_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2193_);
v___x_2284_ = l_Lean_MessageData_ofExpr(v_a_2193_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
lean_inc_ref(v_b_2194_);
v___x_2288_ = l_Lean_MessageData_ofExpr(v_b_2194_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_inc_ref(v_eq_2192_);
v___x_2292_ = l_Lean_MessageData_ofExpr(v_eq_2192_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = l_Lean_MessageData_ofExpr(v___x_2267_);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v___x_2268_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Nat_reprFast(v_a_2282_);
v___x_2305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = l_Lean_MessageData_ofFormat(v___x_2305_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2303_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2277_, v___x_2307_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
v___x_2311_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2310_, v___x_2247_, v_fst_2241_, v_snd_2242_, v___x_2264_, v_a_2309_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
v___y_2208_ = v___x_2311_;
goto v___jp_2207_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2270_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2312_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2308_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2308_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2320_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2281_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2281_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2328_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2280_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2280_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_a_2270_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
v___x_2336_ = lean_box(0);
v___x_2337_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2241_, v_snd_2242_, v___x_2264_, v___x_2246_, v___x_2336_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
v___y_2208_ = v___x_2337_;
goto v___jp_2207_;
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___x_2268_);
lean_dec_ref(v___x_2267_);
lean_dec(v___x_2264_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
lean_dec_ref(v_b_2194_);
lean_dec_ref(v_a_2193_);
lean_dec_ref(v_eq_2192_);
lean_dec(v___y_2191_);
v_a_2338_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2269_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2269_);
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
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_box(0);
v___x_2347_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2241_, v_snd_2242_, v___x_2264_, v___x_2246_, v___x_2346_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v_snd_2242_);
lean_dec(v_fst_2241_);
v___y_2208_ = v___x_2347_;
goto v___jp_2207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object* v___y_2354_, lean_object* v_eq_2355_, lean_object* v_a_2356_, lean_object* v_b_2357_, lean_object* v_a_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2354_, v_eq_2355_, v_a_2356_, v_b_2357_, v_a_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec(v___y_2359_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2371_, lean_object* v_b_2372_, lean_object* v_eq_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
uint8_t v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2418_; lean_object* v___x_2454_; 
lean_inc_ref(v_eq_2373_);
v___x_2454_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2373_, v_a_2374_, v_a_2378_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; uint8_t v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
v___x_2456_ = lean_unbox(v_a_2455_);
lean_dec(v_a_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref_known(v___x_2454_, 1);
lean_inc_ref(v_eq_2373_);
v___x_2457_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2373_, v_a_2374_, v_a_2378_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
v___y_2418_ = v___x_2457_;
goto v___jp_2417_;
}
else
{
v___y_2418_ = v___x_2454_;
goto v___jp_2417_;
}
}
else
{
v___y_2418_ = v___x_2454_;
goto v___jp_2417_;
}
v___jp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2388_ = l_Lean_Expr_getAppNumArgs(v_a_2371_);
v___x_2389_ = lean_box(0);
lean_inc_ref(v_b_2372_);
lean_inc_ref(v_a_2371_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_a_2371_);
lean_ctor_set(v___x_2390_, 1, v_b_2372_);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2388_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2387_, v_eq_2373_, v_a_2371_, v_b_2372_, v___x_2392_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2408_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_fst_2398_; 
v_fst_2398_ = lean_ctor_get(v_a_2394_, 0);
lean_inc(v_fst_2398_);
lean_dec(v_a_2394_);
if (lean_obj_tag(v_fst_2398_) == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2399_ = lean_unsigned_to_nat(2u);
v___x_2400_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*1, v___y_2386_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*1 + 1, v___y_2386_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2400_);
v___x_2402_ = v___x_2396_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
else
{
lean_object* v_val_2404_; lean_object* v___x_2406_; 
v_val_2404_ = lean_ctor_get(v_fst_2398_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v_fst_2398_, 1);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v_val_2404_);
v___x_2406_ = v___x_2396_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_val_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2393_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2393_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
v___jp_2417_:
{
if (lean_obj_tag(v___y_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2445_; 
v_a_2419_ = lean_ctor_get(v___y_2418_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___y_2418_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2421_ = v___y_2418_;
v_isShared_2422_ = v_isSharedCheck_2445_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___y_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2445_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_unbox(v_a_2419_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v_toGoalState_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2439_; 
lean_del_object(v___x_2421_);
v___x_2424_ = lean_st_ref_get(v_a_2374_);
v_toGoalState_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2424_, 1);
lean_dec(v_unused_2440_);
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2439_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_toGoalState_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2439_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_split_2429_; lean_object* v_argPosMap_2430_; lean_object* v___x_2432_; 
v_split_2429_ = lean_ctor_get(v_toGoalState_2425_, 14);
lean_inc_ref(v_split_2429_);
lean_dec_ref(v_toGoalState_2425_);
v_argPosMap_2430_ = lean_ctor_get(v_split_2429_, 6);
lean_inc_ref(v_argPosMap_2430_);
lean_dec_ref(v_split_2429_);
lean_inc_ref(v_b_2372_);
lean_inc_ref(v_a_2371_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v_b_2372_);
lean_ctor_set(v___x_2427_, 0, v_a_2371_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2371_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_b_2372_);
v___x_2432_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2430_, v___x_2432_);
lean_dec_ref(v___x_2432_);
lean_dec_ref(v_argPosMap_2430_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_unbox(v_a_2419_);
lean_dec(v_a_2419_);
v___y_2386_ = v___x_2435_;
v___y_2387_ = v___x_2434_;
goto v___jp_2385_;
}
else
{
lean_object* v_val_2436_; uint8_t v___x_2437_; 
v_val_2436_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2436_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2437_ = lean_unbox(v_a_2419_);
lean_dec(v_a_2419_);
v___y_2386_ = v___x_2437_;
v___y_2387_ = v_val_2436_;
goto v___jp_2385_;
}
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_dec(v_a_2419_);
lean_dec_ref(v_eq_2373_);
lean_dec_ref(v_b_2372_);
lean_dec_ref(v_a_2371_);
v___x_2441_ = lean_box(0);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2441_);
v___x_2443_ = v___x_2421_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v_eq_2373_);
lean_dec_ref(v_b_2372_);
lean_dec_ref(v_a_2371_);
v_a_2446_ = lean_ctor_get(v___y_2418_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___y_2418_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___y_2418_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___y_2418_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2458_, lean_object* v_b_2459_, lean_object* v_eq_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2458_, v_b_2459_, v_eq_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec(v_a_2461_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* v___y_2473_, lean_object* v_eq_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_, lean_object* v_inst_2477_, lean_object* v_a_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2473_, v_eq_2474_, v_a_2475_, v_b_2476_, v_a_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v___y_2491_ = _args[0];
lean_object* v_eq_2492_ = _args[1];
lean_object* v_a_2493_ = _args[2];
lean_object* v_b_2494_ = _args[3];
lean_object* v_inst_2495_ = _args[4];
lean_object* v_a_2496_ = _args[5];
lean_object* v___y_2497_ = _args[6];
lean_object* v___y_2498_ = _args[7];
lean_object* v___y_2499_ = _args[8];
lean_object* v___y_2500_ = _args[9];
lean_object* v___y_2501_ = _args[10];
lean_object* v___y_2502_ = _args[11];
lean_object* v___y_2503_ = _args[12];
lean_object* v___y_2504_ = _args[13];
lean_object* v___y_2505_ = _args[14];
lean_object* v___y_2506_ = _args[15];
lean_object* v___y_2507_ = _args[16];
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v___y_2491_, v_eq_2492_, v_a_2493_, v_b_2494_, v_inst_2495_, v_a_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2509_, lean_object* v_m_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2510_, v_a_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2513_, lean_object* v_m_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2513_, v_m_2514_, v_a_2515_);
lean_dec_ref(v_a_2515_);
lean_dec_ref(v_m_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2517_, lean_object* v_a_2518_, lean_object* v_x_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2518_, v_x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2521_, lean_object* v_a_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2521_, v_a_2522_, v_x_2523_);
lean_dec(v_x_2523_);
lean_dec_ref(v_a_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
uint8_t v___y_2534_; uint8_t v___y_2539_; lean_object* v___y_2540_; lean_object* v___x_2559_; 
lean_inc_ref(v_imp_2525_);
v___x_2559_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; uint8_t v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2576_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2576_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2576_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; 
v___x_2567_ = lean_unbox(v_a_2563_);
lean_dec(v_a_2563_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_box(1);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2568_);
v___x_2570_ = v___x_2565_;
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
else
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_box(0);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2572_);
v___x_2574_ = v___x_2565_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2562_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2562_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_binderType_2585_; lean_object* v_body_2586_; lean_object* v___y_2588_; lean_object* v___x_2616_; 
v_binderType_2585_ = lean_ctor_get(v_imp_2525_, 1);
lean_inc_ref_n(v_binderType_2585_, 2);
v_body_2586_ = lean_ctor_get(v_imp_2525_, 2);
lean_inc_ref(v_body_2586_);
lean_dec_ref(v_imp_2525_);
v___x_2616_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2585_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
v___x_2618_ = lean_unbox(v_a_2617_);
lean_dec(v_a_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref_known(v___x_2616_, 1);
v___x_2619_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2585_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
v___y_2588_ = v___x_2619_;
goto v___jp_2587_;
}
else
{
lean_dec_ref(v_binderType_2585_);
v___y_2588_ = v___x_2616_;
goto v___jp_2587_;
}
}
else
{
lean_dec_ref(v_binderType_2585_);
v___y_2588_ = v___x_2616_;
goto v___jp_2587_;
}
v___jp_2587_:
{
if (lean_obj_tag(v___y_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2607_; 
v_a_2589_ = lean_ctor_get(v___y_2588_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___y_2588_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2591_ = v___y_2588_;
v_isShared_2592_ = v_isSharedCheck_2607_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___y_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2607_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_unbox(v_a_2589_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; 
lean_del_object(v___x_2591_);
v___x_2594_ = l_Lean_Expr_hasLooseBVars(v_body_2586_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_inc_ref(v_body_2586_);
v___x_2595_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2586_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; uint8_t v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
v___x_2597_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
lean_dec_ref_known(v___x_2595_, 1);
v___x_2598_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2586_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
v___x_2599_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
v___y_2539_ = v___x_2599_;
v___y_2540_ = v___x_2598_;
goto v___jp_2538_;
}
else
{
uint8_t v___x_2600_; 
lean_dec_ref(v_body_2586_);
v___x_2600_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
v___y_2539_ = v___x_2600_;
v___y_2540_ = v___x_2595_;
goto v___jp_2538_;
}
}
else
{
uint8_t v___x_2601_; 
lean_dec_ref(v_body_2586_);
v___x_2601_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
v___y_2539_ = v___x_2601_;
v___y_2540_ = v___x_2595_;
goto v___jp_2538_;
}
}
else
{
uint8_t v___x_2602_; 
lean_dec_ref(v_body_2586_);
v___x_2602_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
v___y_2534_ = v___x_2602_;
goto v___jp_2533_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec(v_a_2589_);
lean_dec_ref(v_body_2586_);
v___x_2603_ = lean_box(0);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2603_);
v___x_2605_ = v___x_2591_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v_body_2586_);
v_a_2608_ = lean_ctor_get(v___y_2588_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___y_2588_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___y_2588_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___y_2588_);
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
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_imp_2525_);
v_a_2620_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2559_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2559_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
v___jp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_unsigned_to_nat(2u);
v___x_2536_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*1, v___y_2534_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*1 + 1, v___y_2534_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
v___jp_2538_:
{
if (lean_obj_tag(v___y_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2550_; 
v_a_2541_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2543_ = v___y_2540_;
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___y_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2550_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_unbox(v_a_2541_);
lean_dec(v_a_2541_);
if (v___x_2545_ == 0)
{
lean_del_object(v___x_2543_);
v___y_2534_ = v___y_2539_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2546_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___y_2540_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___y_2540_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2637_, lean_object* v_h_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2637_, v_a_2639_, v_a_2643_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2651_, lean_object* v_h_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2651_, v_h_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
switch(lean_obj_tag(v_s_2665_))
{
case 0:
{
lean_object* v_e_2677_; lean_object* v___x_2678_; 
v_e_2677_ = lean_ctor_get(v_s_2665_, 0);
lean_inc_ref(v_e_2677_);
lean_dec_ref_known(v_s_2665_, 2);
v___x_2678_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2677_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2678_;
}
case 1:
{
lean_object* v_e_2679_; lean_object* v___x_2680_; 
v_e_2679_ = lean_ctor_get(v_s_2665_, 0);
lean_inc_ref(v_e_2679_);
lean_dec_ref_known(v_s_2665_, 2);
v___x_2680_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2679_, v_a_2666_, v_a_2670_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2680_;
}
default: 
{
lean_object* v_a_2681_; lean_object* v_b_2682_; lean_object* v_eq_2683_; lean_object* v___x_2684_; 
v_a_2681_ = lean_ctor_get(v_s_2665_, 0);
lean_inc_ref(v_a_2681_);
v_b_2682_ = lean_ctor_get(v_s_2665_, 1);
lean_inc_ref(v_b_2682_);
v_eq_2683_ = lean_ctor_get(v_s_2665_, 3);
lean_inc_ref(v_eq_2683_);
lean_dec_ref_known(v_s_2665_, 5);
v___x_2684_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2681_, v_b_2682_, v_eq_2683_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec(v_a_2686_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2698_) == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
return v___x_2699_;
}
else
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_unsigned_to_nat(1u);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2701_);
lean_dec(v_x_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2703_, lean_object* v_k_2704_){
_start:
{
if (lean_obj_tag(v_t_2703_) == 0)
{
return v_k_2704_;
}
else
{
lean_object* v_c_2705_; lean_object* v_numCases_2706_; uint8_t v_isRec_2707_; uint8_t v_tryPostpone_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_c_2705_ = lean_ctor_get(v_t_2703_, 0);
lean_inc_ref(v_c_2705_);
v_numCases_2706_ = lean_ctor_get(v_t_2703_, 1);
lean_inc(v_numCases_2706_);
v_isRec_2707_ = lean_ctor_get_uint8(v_t_2703_, sizeof(void*)*2);
v_tryPostpone_2708_ = lean_ctor_get_uint8(v_t_2703_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2703_, 2);
v___x_2709_ = lean_box(v_isRec_2707_);
v___x_2710_ = lean_box(v_tryPostpone_2708_);
v___x_2711_ = lean_apply_4(v_k_2704_, v_c_2705_, v_numCases_2706_, v___x_2709_, v___x_2710_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2712_, lean_object* v_ctorIdx_2713_, lean_object* v_t_2714_, lean_object* v_h_2715_, lean_object* v_k_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2714_, v_k_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2718_, lean_object* v_ctorIdx_2719_, lean_object* v_t_2720_, lean_object* v_h_2721_, lean_object* v_k_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2718_, v_ctorIdx_2719_, v_t_2720_, v_h_2721_, v_k_2722_);
lean_dec(v_ctorIdx_2719_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2724_, lean_object* v_none_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2724_, v_none_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2727_, lean_object* v_t_2728_, lean_object* v_h_2729_, lean_object* v_none_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2728_, v_none_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2732_, lean_object* v_some_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2732_, v_some_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2735_, lean_object* v_t_2736_, lean_object* v_h_2737_, lean_object* v_some_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2736_, v_some_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2740_, lean_object* v_as_2741_, size_t v_i_2742_, size_t v_stop_2743_){
_start:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_eq(v_i_2742_, v_stop_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = lean_array_uget_borrowed(v_as_2741_, v_i_2742_);
v___x_2746_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2745_, v_a_2740_);
if (v___x_2746_ == 0)
{
size_t v___x_2747_; size_t v___x_2748_; 
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_add(v_i_2742_, v___x_2747_);
v_i_2742_ = v___x_2748_;
goto _start;
}
else
{
return v___x_2746_;
}
}
else
{
uint8_t v___x_2750_; 
v___x_2750_ = 0;
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2751_, lean_object* v_as_2752_, lean_object* v_i_2753_, lean_object* v_stop_2754_){
_start:
{
uint64_t v_a_2749__boxed_2755_; size_t v_i_boxed_2756_; size_t v_stop_boxed_2757_; uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_a_2749__boxed_2755_ = lean_unbox_uint64(v_a_2751_);
lean_dec_ref(v_a_2751_);
v_i_boxed_2756_ = lean_unbox_usize(v_i_2753_);
lean_dec(v_i_2753_);
v_stop_boxed_2757_ = lean_unbox_usize(v_stop_2754_);
lean_dec(v_stop_2754_);
v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2749__boxed_2755_, v_as_2752_, v_i_boxed_2756_, v_stop_boxed_2757_);
lean_dec_ref(v_as_2752_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2762_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2815_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2815_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2815_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
if (lean_obj_tag(v_a_2772_) == 1)
{
lean_object* v_val_2776_; lean_object* v___x_2777_; 
lean_del_object(v___x_2774_);
v_val_2776_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v_a_2772_, 1);
v___x_2777_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2801_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2801_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2801_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = lean_array_get_size(v_val_2776_);
v___x_2784_ = lean_nat_dec_lt(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_dec(v_a_2778_);
lean_dec(v_val_2776_);
v___x_2785_ = lean_box(v___x_2784_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2785_);
v___x_2787_ = v___x_2780_;
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
else
{
if (v___x_2784_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_dec(v_a_2778_);
lean_dec(v_val_2776_);
v___x_2789_ = lean_box(v___x_2784_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2789_);
v___x_2791_ = v___x_2780_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
else
{
size_t v___x_2793_; size_t v___x_2794_; uint64_t v___x_2795_; uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = lean_usize_of_nat(v___x_2783_);
v___x_2795_ = lean_unbox_uint64(v_a_2778_);
lean_dec(v_a_2778_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2795_, v_val_2776_, v___x_2793_, v___x_2794_);
lean_dec(v_val_2776_);
v___x_2797_ = lean_box(v___x_2796_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2797_);
v___x_2799_ = v___x_2780_;
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
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_val_2776_);
v_a_2802_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2777_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2777_);
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
else
{
uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec(v_a_2772_);
v___x_2810_ = 1;
v___x_2811_ = lean_box(v___x_2810_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2811_);
v___x_2813_ = v___x_2774_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2771_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2771_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_c_2824_);
return v_res_2835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2838_ = l_Lean_stringToMessageData(v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2839_, lean_object* v_c_x3f_2840_, lean_object* v_cs_x27_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
if (lean_obj_tag(v_cs_2839_) == 0)
{
lean_object* v___x_2853_; lean_object* v_toGoalState_2854_; lean_object* v_split_2855_; lean_object* v_mvarId_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2964_; 
v___x_2853_ = lean_st_ref_take(v_a_2842_);
v_toGoalState_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_ref(v_toGoalState_2854_);
v_split_2855_ = lean_ctor_get(v_toGoalState_2854_, 14);
lean_inc_ref(v_split_2855_);
v_mvarId_2856_ = lean_ctor_get(v___x_2853_, 1);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2964_ == 0)
{
lean_object* v_unused_2965_; 
v_unused_2965_ = lean_ctor_get(v___x_2853_, 0);
lean_dec(v_unused_2965_);
v___x_2858_ = v___x_2853_;
v_isShared_2859_ = v_isSharedCheck_2964_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_mvarId_2856_);
lean_dec(v___x_2853_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2964_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_nextDeclIdx_2860_; lean_object* v_enodeMap_2861_; lean_object* v_exprs_2862_; lean_object* v_parents_2863_; lean_object* v_congrTable_2864_; lean_object* v_appMap_2865_; lean_object* v_indicesFound_2866_; lean_object* v_newFacts_2867_; uint8_t v_inconsistent_2868_; lean_object* v_nextIdx_2869_; lean_object* v_newRawFacts_2870_; lean_object* v_facts_2871_; lean_object* v_extThms_2872_; lean_object* v_ematch_2873_; lean_object* v_inj_2874_; lean_object* v_clean_2875_; lean_object* v_sstates_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2962_; 
v_nextDeclIdx_2860_ = lean_ctor_get(v_toGoalState_2854_, 0);
v_enodeMap_2861_ = lean_ctor_get(v_toGoalState_2854_, 1);
v_exprs_2862_ = lean_ctor_get(v_toGoalState_2854_, 2);
v_parents_2863_ = lean_ctor_get(v_toGoalState_2854_, 3);
v_congrTable_2864_ = lean_ctor_get(v_toGoalState_2854_, 4);
v_appMap_2865_ = lean_ctor_get(v_toGoalState_2854_, 5);
v_indicesFound_2866_ = lean_ctor_get(v_toGoalState_2854_, 6);
v_newFacts_2867_ = lean_ctor_get(v_toGoalState_2854_, 7);
v_inconsistent_2868_ = lean_ctor_get_uint8(v_toGoalState_2854_, sizeof(void*)*17);
v_nextIdx_2869_ = lean_ctor_get(v_toGoalState_2854_, 8);
v_newRawFacts_2870_ = lean_ctor_get(v_toGoalState_2854_, 9);
v_facts_2871_ = lean_ctor_get(v_toGoalState_2854_, 10);
v_extThms_2872_ = lean_ctor_get(v_toGoalState_2854_, 11);
v_ematch_2873_ = lean_ctor_get(v_toGoalState_2854_, 12);
v_inj_2874_ = lean_ctor_get(v_toGoalState_2854_, 13);
v_clean_2875_ = lean_ctor_get(v_toGoalState_2854_, 15);
v_sstates_2876_ = lean_ctor_get(v_toGoalState_2854_, 16);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_toGoalState_2854_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_toGoalState_2854_, 14);
lean_dec(v_unused_2963_);
v___x_2878_ = v_toGoalState_2854_;
v_isShared_2879_ = v_isSharedCheck_2962_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_sstates_2876_);
lean_inc(v_clean_2875_);
lean_inc(v_inj_2874_);
lean_inc(v_ematch_2873_);
lean_inc(v_extThms_2872_);
lean_inc(v_facts_2871_);
lean_inc(v_newRawFacts_2870_);
lean_inc(v_nextIdx_2869_);
lean_inc(v_newFacts_2867_);
lean_inc(v_indicesFound_2866_);
lean_inc(v_appMap_2865_);
lean_inc(v_congrTable_2864_);
lean_inc(v_parents_2863_);
lean_inc(v_exprs_2862_);
lean_inc(v_enodeMap_2861_);
lean_inc(v_nextDeclIdx_2860_);
lean_dec(v_toGoalState_2854_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2962_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_num_2880_; lean_object* v_added_2881_; lean_object* v_resolved_2882_; lean_object* v_trace_2883_; lean_object* v_lookaheads_2884_; lean_object* v_argPosMap_2885_; lean_object* v_argsAt_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2960_; 
v_num_2880_ = lean_ctor_get(v_split_2855_, 0);
v_added_2881_ = lean_ctor_get(v_split_2855_, 2);
v_resolved_2882_ = lean_ctor_get(v_split_2855_, 3);
v_trace_2883_ = lean_ctor_get(v_split_2855_, 4);
v_lookaheads_2884_ = lean_ctor_get(v_split_2855_, 5);
v_argPosMap_2885_ = lean_ctor_get(v_split_2855_, 6);
v_argsAt_2886_ = lean_ctor_get(v_split_2855_, 7);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_split_2855_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_split_2855_, 1);
lean_dec(v_unused_2961_);
v___x_2888_ = v_split_2855_;
v_isShared_2889_ = v_isSharedCheck_2960_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_argsAt_2886_);
lean_inc(v_argPosMap_2885_);
lean_inc(v_lookaheads_2884_);
lean_inc(v_trace_2883_);
lean_inc(v_resolved_2882_);
lean_inc(v_added_2881_);
lean_inc(v_num_2880_);
lean_dec(v_split_2855_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2960_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = l_List_reverse___redArg(v_cs_x27_2841_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_num_2880_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_added_2881_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v_resolved_2882_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v_trace_2883_);
lean_ctor_set(v_reuseFailAlloc_2959_, 5, v_lookaheads_2884_);
lean_ctor_set(v_reuseFailAlloc_2959_, 6, v_argPosMap_2885_);
lean_ctor_set(v_reuseFailAlloc_2959_, 7, v_argsAt_2886_);
v___x_2892_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 14, v___x_2892_);
v___x_2894_ = v___x_2878_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_nextDeclIdx_2860_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_enodeMap_2861_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_exprs_2862_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_parents_2863_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_congrTable_2864_);
lean_ctor_set(v_reuseFailAlloc_2958_, 5, v_appMap_2865_);
lean_ctor_set(v_reuseFailAlloc_2958_, 6, v_indicesFound_2866_);
lean_ctor_set(v_reuseFailAlloc_2958_, 7, v_newFacts_2867_);
lean_ctor_set(v_reuseFailAlloc_2958_, 8, v_nextIdx_2869_);
lean_ctor_set(v_reuseFailAlloc_2958_, 9, v_newRawFacts_2870_);
lean_ctor_set(v_reuseFailAlloc_2958_, 10, v_facts_2871_);
lean_ctor_set(v_reuseFailAlloc_2958_, 11, v_extThms_2872_);
lean_ctor_set(v_reuseFailAlloc_2958_, 12, v_ematch_2873_);
lean_ctor_set(v_reuseFailAlloc_2958_, 13, v_inj_2874_);
lean_ctor_set(v_reuseFailAlloc_2958_, 14, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2958_, 15, v_clean_2875_);
lean_ctor_set(v_reuseFailAlloc_2958_, 16, v_sstates_2876_);
lean_ctor_set_uint8(v_reuseFailAlloc_2958_, sizeof(void*)*17, v_inconsistent_2868_);
v___x_2894_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2896_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2894_);
v___x_2896_ = v___x_2858_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_mvarId_2856_);
v___x_2896_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_st_ref_set(v_a_2842_, v___x_2896_);
if (lean_obj_tag(v_c_x3f_2840_) == 1)
{
lean_object* v___x_2898_; lean_object* v_toGoalState_2899_; lean_object* v_ematch_2900_; lean_object* v_mvarId_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2954_; 
v___x_2898_ = lean_st_ref_take(v_a_2842_);
v_toGoalState_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_toGoalState_2899_);
v_ematch_2900_ = lean_ctor_get(v_toGoalState_2899_, 12);
lean_inc_ref(v_ematch_2900_);
v_mvarId_2901_ = lean_ctor_get(v___x_2898_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2898_, 0);
lean_dec(v_unused_2955_);
v___x_2903_ = v___x_2898_;
v_isShared_2904_ = v_isSharedCheck_2954_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_mvarId_2901_);
lean_dec(v___x_2898_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2954_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_nextDeclIdx_2905_; lean_object* v_enodeMap_2906_; lean_object* v_exprs_2907_; lean_object* v_parents_2908_; lean_object* v_congrTable_2909_; lean_object* v_appMap_2910_; lean_object* v_indicesFound_2911_; lean_object* v_newFacts_2912_; uint8_t v_inconsistent_2913_; lean_object* v_nextIdx_2914_; lean_object* v_newRawFacts_2915_; lean_object* v_facts_2916_; lean_object* v_extThms_2917_; lean_object* v_inj_2918_; lean_object* v_split_2919_; lean_object* v_clean_2920_; lean_object* v_sstates_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2952_; 
v_nextDeclIdx_2905_ = lean_ctor_get(v_toGoalState_2899_, 0);
v_enodeMap_2906_ = lean_ctor_get(v_toGoalState_2899_, 1);
v_exprs_2907_ = lean_ctor_get(v_toGoalState_2899_, 2);
v_parents_2908_ = lean_ctor_get(v_toGoalState_2899_, 3);
v_congrTable_2909_ = lean_ctor_get(v_toGoalState_2899_, 4);
v_appMap_2910_ = lean_ctor_get(v_toGoalState_2899_, 5);
v_indicesFound_2911_ = lean_ctor_get(v_toGoalState_2899_, 6);
v_newFacts_2912_ = lean_ctor_get(v_toGoalState_2899_, 7);
v_inconsistent_2913_ = lean_ctor_get_uint8(v_toGoalState_2899_, sizeof(void*)*17);
v_nextIdx_2914_ = lean_ctor_get(v_toGoalState_2899_, 8);
v_newRawFacts_2915_ = lean_ctor_get(v_toGoalState_2899_, 9);
v_facts_2916_ = lean_ctor_get(v_toGoalState_2899_, 10);
v_extThms_2917_ = lean_ctor_get(v_toGoalState_2899_, 11);
v_inj_2918_ = lean_ctor_get(v_toGoalState_2899_, 13);
v_split_2919_ = lean_ctor_get(v_toGoalState_2899_, 14);
v_clean_2920_ = lean_ctor_get(v_toGoalState_2899_, 15);
v_sstates_2921_ = lean_ctor_get(v_toGoalState_2899_, 16);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_toGoalState_2899_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v_toGoalState_2899_, 12);
lean_dec(v_unused_2953_);
v___x_2923_ = v_toGoalState_2899_;
v_isShared_2924_ = v_isSharedCheck_2952_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_sstates_2921_);
lean_inc(v_clean_2920_);
lean_inc(v_split_2919_);
lean_inc(v_inj_2918_);
lean_inc(v_extThms_2917_);
lean_inc(v_facts_2916_);
lean_inc(v_newRawFacts_2915_);
lean_inc(v_nextIdx_2914_);
lean_inc(v_newFacts_2912_);
lean_inc(v_indicesFound_2911_);
lean_inc(v_appMap_2910_);
lean_inc(v_congrTable_2909_);
lean_inc(v_parents_2908_);
lean_inc(v_exprs_2907_);
lean_inc(v_enodeMap_2906_);
lean_inc(v_nextDeclIdx_2905_);
lean_dec(v_toGoalState_2899_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2952_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_thmMap_2925_; lean_object* v_gmt_2926_; lean_object* v_thms_2927_; lean_object* v_newThms_2928_; lean_object* v_numInstances_2929_; lean_object* v_numDelayedInstances_2930_; lean_object* v_preInstances_2931_; lean_object* v_nextThmIdx_2932_; lean_object* v_matchEqNames_2933_; lean_object* v_delayedThmInsts_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2950_; 
v_thmMap_2925_ = lean_ctor_get(v_ematch_2900_, 0);
v_gmt_2926_ = lean_ctor_get(v_ematch_2900_, 1);
v_thms_2927_ = lean_ctor_get(v_ematch_2900_, 2);
v_newThms_2928_ = lean_ctor_get(v_ematch_2900_, 3);
v_numInstances_2929_ = lean_ctor_get(v_ematch_2900_, 4);
v_numDelayedInstances_2930_ = lean_ctor_get(v_ematch_2900_, 5);
v_preInstances_2931_ = lean_ctor_get(v_ematch_2900_, 7);
v_nextThmIdx_2932_ = lean_ctor_get(v_ematch_2900_, 8);
v_matchEqNames_2933_ = lean_ctor_get(v_ematch_2900_, 9);
v_delayedThmInsts_2934_ = lean_ctor_get(v_ematch_2900_, 10);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_ematch_2900_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_ematch_2900_, 6);
lean_dec(v_unused_2951_);
v___x_2936_ = v_ematch_2900_;
v_isShared_2937_ = v_isSharedCheck_2950_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_delayedThmInsts_2934_);
lean_inc(v_matchEqNames_2933_);
lean_inc(v_nextThmIdx_2932_);
lean_inc(v_preInstances_2931_);
lean_inc(v_numDelayedInstances_2930_);
lean_inc(v_numInstances_2929_);
lean_inc(v_newThms_2928_);
lean_inc(v_thms_2927_);
lean_inc(v_gmt_2926_);
lean_inc(v_thmMap_2925_);
lean_dec(v_ematch_2900_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2950_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = lean_unsigned_to_nat(0u);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 6, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_thmMap_2925_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_gmt_2926_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v_thms_2927_);
lean_ctor_set(v_reuseFailAlloc_2949_, 3, v_newThms_2928_);
lean_ctor_set(v_reuseFailAlloc_2949_, 4, v_numInstances_2929_);
lean_ctor_set(v_reuseFailAlloc_2949_, 5, v_numDelayedInstances_2930_);
lean_ctor_set(v_reuseFailAlloc_2949_, 6, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2949_, 7, v_preInstances_2931_);
lean_ctor_set(v_reuseFailAlloc_2949_, 8, v_nextThmIdx_2932_);
lean_ctor_set(v_reuseFailAlloc_2949_, 9, v_matchEqNames_2933_);
lean_ctor_set(v_reuseFailAlloc_2949_, 10, v_delayedThmInsts_2934_);
v___x_2940_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2942_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 12, v___x_2940_);
v___x_2942_ = v___x_2923_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_nextDeclIdx_2905_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_enodeMap_2906_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v_exprs_2907_);
lean_ctor_set(v_reuseFailAlloc_2948_, 3, v_parents_2908_);
lean_ctor_set(v_reuseFailAlloc_2948_, 4, v_congrTable_2909_);
lean_ctor_set(v_reuseFailAlloc_2948_, 5, v_appMap_2910_);
lean_ctor_set(v_reuseFailAlloc_2948_, 6, v_indicesFound_2911_);
lean_ctor_set(v_reuseFailAlloc_2948_, 7, v_newFacts_2912_);
lean_ctor_set(v_reuseFailAlloc_2948_, 8, v_nextIdx_2914_);
lean_ctor_set(v_reuseFailAlloc_2948_, 9, v_newRawFacts_2915_);
lean_ctor_set(v_reuseFailAlloc_2948_, 10, v_facts_2916_);
lean_ctor_set(v_reuseFailAlloc_2948_, 11, v_extThms_2917_);
lean_ctor_set(v_reuseFailAlloc_2948_, 12, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2948_, 13, v_inj_2918_);
lean_ctor_set(v_reuseFailAlloc_2948_, 14, v_split_2919_);
lean_ctor_set(v_reuseFailAlloc_2948_, 15, v_clean_2920_);
lean_ctor_set(v_reuseFailAlloc_2948_, 16, v_sstates_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_2948_, sizeof(void*)*17, v_inconsistent_2913_);
v___x_2942_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2944_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2942_);
v___x_2944_ = v___x_2903_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_mvarId_2901_);
v___x_2944_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_st_ref_set(v_a_2842_, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_c_x3f_2840_);
return v___x_2946_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_c_x3f_2840_);
return v___x_2956_;
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
lean_object* v_head_2966_; lean_object* v_tail_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3203_; 
v_head_2966_ = lean_ctor_get(v_cs_2839_, 0);
v_tail_2967_ = lean_ctor_get(v_cs_2839_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_cs_2839_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_2969_ = v_cs_2839_;
v_isShared_2970_ = v_isSharedCheck_3203_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_tail_2967_);
lean_inc(v_head_2966_);
lean_dec(v_cs_2839_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3203_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; uint8_t v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; uint8_t v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; uint8_t v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; uint8_t v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3081_; uint8_t v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; uint8_t v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___x_3162_; 
v___x_3162_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2966_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; uint8_t v___x_3164_; uint8_t v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = lean_unbox(v_a_3163_);
lean_dec(v_a_3163_);
v___x_3165_ = lean_bool_not(v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v_options_3166_; uint8_t v_hasTrace_3167_; 
v_options_3166_ = lean_ctor_get(v_a_2850_, 2);
v_hasTrace_3167_ = lean_ctor_get_uint8(v_options_3166_, sizeof(void*)*1);
if (v_hasTrace_3167_ == 0)
{
v___y_3121_ = v_a_2842_;
v___y_3122_ = v_a_2843_;
v___y_3123_ = v_a_2844_;
v___y_3124_ = v_a_2845_;
v___y_3125_ = v_a_2846_;
v___y_3126_ = v_a_2847_;
v___y_3127_ = v_a_2848_;
v___y_3128_ = v_a_2849_;
v___y_3129_ = v_a_2850_;
v___y_3130_ = v_a_2851_;
goto v___jp_3120_;
}
else
{
lean_object* v_inheritedTraceOptions_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_inheritedTraceOptions_3168_ = lean_ctor_get(v_a_2850_, 13);
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3168_, v_options_3166_, v___x_3170_);
if (v___x_3171_ == 0)
{
v___y_3121_ = v_a_2842_;
v___y_3122_ = v_a_2843_;
v___y_3123_ = v_a_2844_;
v___y_3124_ = v_a_2845_;
v___y_3125_ = v_a_2846_;
v___y_3126_ = v_a_2847_;
v___y_3127_ = v_a_2848_;
v___y_3128_ = v_a_2849_;
v___y_3129_ = v_a_2850_;
v___y_3130_ = v_a_2851_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Meta_Grind_updateLastTag(v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref_known(v___x_3172_, 1);
v___x_3173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3174_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2966_);
v___x_3175_ = l_Lean_MessageData_ofExpr(v___x_3174_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3173_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3169_, v___x_3176_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
v___y_3121_ = v_a_2842_;
v___y_3122_ = v_a_2843_;
v___y_3123_ = v_a_2844_;
v___y_3124_ = v_a_2845_;
v___y_3125_ = v_a_2846_;
v___y_3126_ = v_a_2847_;
v___y_3127_ = v_a_2848_;
v___y_3128_ = v_a_2849_;
v___y_3129_ = v_a_2850_;
v___y_3130_ = v_a_2851_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
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
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3186_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3172_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3172_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2969_);
lean_dec(v_head_2966_);
v_cs_2839_ = v_tail_2967_;
goto _start;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3195_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3162_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3162_);
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
v___jp_2971_:
{
lean_object* v___x_2983_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v_cs_x27_2841_);
v___x_2983_ = v___x_2969_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_head_2966_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_cs_x27_2841_);
v___x_2983_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v_cs_2839_ = v_tail_2967_;
v_cs_x27_2841_ = v___x_2983_;
v_a_2842_ = v___y_2974_;
v_a_2843_ = v___y_2973_;
v_a_2844_ = v___y_2979_;
v_a_2845_ = v___y_2978_;
v_a_2846_ = v___y_2980_;
v_a_2847_ = v___y_2977_;
v_a_2848_ = v___y_2976_;
v_a_2849_ = v___y_2975_;
v_a_2850_ = v___y_2981_;
v_a_2851_ = v___y_2972_;
goto _start;
}
}
v___jp_2986_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3001_, 0, v_head_2966_);
lean_ctor_set(v___x_3001_, 1, v___y_2991_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*2, v___y_2997_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*2 + 1, v___y_2987_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___y_2993_);
lean_ctor_set(v___x_3002_, 1, v_cs_x27_2841_);
v_cs_2839_ = v_tail_2967_;
v_c_x3f_2840_ = v___x_3001_;
v_cs_x27_2841_ = v___x_3002_;
v_a_2842_ = v___y_2996_;
v_a_2843_ = v___y_2995_;
v_a_2844_ = v___y_2988_;
v_a_2845_ = v___y_2989_;
v_a_2846_ = v___y_2992_;
v_a_2847_ = v___y_2990_;
v_a_2848_ = v___y_2999_;
v_a_2849_ = v___y_2998_;
v_a_2850_ = v___y_3000_;
v_a_2851_ = v___y_2994_;
goto _start;
}
v___jp_3004_:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2966_, v___y_3015_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3011_, v___y_3015_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; uint8_t v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = lean_nat_dec_lt(v_a_3021_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec(v_a_3021_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_nat_dec_lt(v___y_3009_, v___y_3012_);
lean_dec(v___y_3012_);
if (v___x_3025_ == 0)
{
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3009_);
v___y_2972_ = v___y_3013_;
v___y_2973_ = v___y_3014_;
v___y_2974_ = v___y_3015_;
v___y_2975_ = v___y_3017_;
v___y_2976_ = v___y_3018_;
v___y_2977_ = v___y_3006_;
v___y_2978_ = v___y_3007_;
v___y_2979_ = v___y_3008_;
v___y_2980_ = v___y_3010_;
v___y_2981_ = v___y_3019_;
goto v___jp_2971_;
}
else
{
lean_del_object(v___x_2969_);
lean_dec(v_c_x3f_2840_);
v___y_2987_ = v___y_3005_;
v___y_2988_ = v___y_3008_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
v___y_2998_ = v___y_3017_;
v___y_2999_ = v___y_3018_;
v___y_3000_ = v___y_3019_;
goto v___jp_2986_;
}
}
else
{
lean_dec(v___y_3012_);
lean_del_object(v___x_2969_);
lean_dec(v_c_x3f_2840_);
v___y_2987_ = v___y_3005_;
v___y_2988_ = v___y_3008_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___y_3014_;
v___y_2996_ = v___y_3015_;
v___y_2997_ = v___y_3016_;
v___y_2998_ = v___y_3017_;
v___y_2999_ = v___y_3018_;
v___y_3000_ = v___y_3019_;
goto v___jp_2986_;
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_a_3021_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3009_);
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3026_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3022_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3022_);
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
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3009_);
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
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
v___jp_3042_:
{
if (v___y_3058_ == 0)
{
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
v___y_3015_ = v___y_3053_;
v___y_3016_ = v___y_3054_;
v___y_3017_ = v___y_3055_;
v___y_3018_ = v___y_3056_;
v___y_3019_ = v___y_3057_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_nat_dec_lt(v___x_3059_, v___y_3050_);
if (v___x_3060_ == 0)
{
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
v___y_3015_ = v___y_3053_;
v___y_3016_ = v___y_3054_;
v___y_3017_ = v___y_3055_;
v___y_3018_ = v___y_3056_;
v___y_3019_ = v___y_3057_;
goto v___jp_3004_;
}
else
{
lean_dec(v___y_3050_);
lean_del_object(v___x_2969_);
lean_dec(v_c_x3f_2840_);
v___y_2987_ = v___y_3043_;
v___y_2988_ = v___y_3046_;
v___y_2989_ = v___y_3045_;
v___y_2990_ = v___y_3044_;
v___y_2991_ = v___y_3047_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3051_;
v___y_2995_ = v___y_3052_;
v___y_2996_ = v___y_3053_;
v___y_2997_ = v___y_3054_;
v___y_2998_ = v___y_3055_;
v___y_2999_ = v___y_3056_;
v___y_3000_ = v___y_3057_;
goto v___jp_2986_;
}
}
}
v___jp_3061_:
{
lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = lean_nat_dec_eq(v___y_3066_, v___x_3077_);
if (v___x_3078_ == 0)
{
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
v___y_3053_ = v___y_3072_;
v___y_3054_ = v___y_3073_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___y_3075_;
v___y_3057_ = v___y_3076_;
v___y_3058_ = v___x_3078_;
goto v___jp_3042_;
}
else
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_bool_not(v___y_3073_);
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
v___y_3053_ = v___y_3072_;
v___y_3054_ = v___y_3073_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___y_3075_;
v___y_3057_ = v___y_3076_;
v___y_3058_ = v___x_3079_;
goto v___jp_3042_;
}
}
v___jp_3080_:
{
if (v___y_3081_ == 0)
{
v___y_3062_ = v___y_3081_;
v___y_3063_ = v___y_3083_;
v___y_3064_ = v___y_3084_;
v___y_3065_ = v___y_3085_;
v___y_3066_ = v___y_3086_;
v___y_3067_ = v___y_3087_;
v___y_3068_ = v___y_3088_;
v___y_3069_ = v___y_3089_;
v___y_3070_ = v___y_3090_;
v___y_3071_ = v___y_3091_;
v___y_3072_ = v___y_3092_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
goto v___jp_3061_;
}
else
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_bool_not(v___y_3082_);
if (v___x_3097_ == 0)
{
v___y_3062_ = v___y_3081_;
v___y_3063_ = v___y_3083_;
v___y_3064_ = v___y_3084_;
v___y_3065_ = v___y_3085_;
v___y_3066_ = v___y_3086_;
v___y_3067_ = v___y_3087_;
v___y_3068_ = v___y_3088_;
v___y_3069_ = v___y_3089_;
v___y_3070_ = v___y_3090_;
v___y_3071_ = v___y_3091_;
v___y_3072_ = v___y_3092_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
goto v___jp_3061_;
}
else
{
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3086_);
v___y_2972_ = v___y_3090_;
v___y_2973_ = v___y_3091_;
v___y_2974_ = v___y_3092_;
v___y_2975_ = v___y_3094_;
v___y_2976_ = v___y_3095_;
v___y_2977_ = v___y_3083_;
v___y_2978_ = v___y_3084_;
v___y_2979_ = v___y_3085_;
v___y_2980_ = v___y_3087_;
v___y_2981_ = v___y_3096_;
goto v___jp_2971_;
}
}
}
v___jp_3098_:
{
if (lean_obj_tag(v_c_x3f_2840_) == 0)
{
lean_object* v___x_3112_; 
lean_del_object(v___x_2969_);
v___x_3112_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3112_, 0, v_head_2966_);
lean_ctor_set(v___x_3112_, 1, v___y_3103_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2, v___y_3108_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2 + 1, v___y_3099_);
v_cs_2839_ = v_tail_2967_;
v_c_x3f_2840_ = v___x_3112_;
v_a_2842_ = v___y_3107_;
v_a_2843_ = v___y_3106_;
v_a_2844_ = v___y_3100_;
v_a_2845_ = v___y_3101_;
v_a_2846_ = v___y_3104_;
v_a_2847_ = v___y_3102_;
v_a_2848_ = v___y_3110_;
v_a_2849_ = v___y_3109_;
v_a_2850_ = v___y_3111_;
v_a_2851_ = v___y_3105_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3114_; 
v_tryPostpone_3114_ = lean_ctor_get_uint8(v_c_x3f_2840_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3114_ == 0)
{
lean_object* v_c_3115_; lean_object* v_numCases_3116_; 
v_c_3115_ = lean_ctor_get(v_c_x3f_2840_, 0);
v_numCases_3116_ = lean_ctor_get(v_c_x3f_2840_, 1);
lean_inc(v_numCases_3116_);
lean_inc_ref(v_c_3115_);
v___y_3081_ = v___y_3099_;
v___y_3082_ = v_tryPostpone_3114_;
v___y_3083_ = v___y_3102_;
v___y_3084_ = v___y_3101_;
v___y_3085_ = v___y_3100_;
v___y_3086_ = v___y_3103_;
v___y_3087_ = v___y_3104_;
v___y_3088_ = v_c_3115_;
v___y_3089_ = v_numCases_3116_;
v___y_3090_ = v___y_3105_;
v___y_3091_ = v___y_3106_;
v___y_3092_ = v___y_3107_;
v___y_3093_ = v___y_3108_;
v___y_3094_ = v___y_3109_;
v___y_3095_ = v___y_3110_;
v___y_3096_ = v___y_3111_;
goto v___jp_3080_;
}
else
{
lean_object* v_c_3117_; lean_object* v_numCases_3118_; uint8_t v___x_3119_; 
v_c_3117_ = lean_ctor_get(v_c_x3f_2840_, 0);
v_numCases_3118_ = lean_ctor_get(v_c_x3f_2840_, 1);
v___x_3119_ = lean_bool_not(v___y_3099_);
if (v___x_3119_ == 0)
{
lean_inc(v_numCases_3118_);
lean_inc_ref(v_c_3117_);
v___y_3081_ = v___y_3099_;
v___y_3082_ = v_tryPostpone_3114_;
v___y_3083_ = v___y_3102_;
v___y_3084_ = v___y_3101_;
v___y_3085_ = v___y_3100_;
v___y_3086_ = v___y_3103_;
v___y_3087_ = v___y_3104_;
v___y_3088_ = v_c_3117_;
v___y_3089_ = v_numCases_3118_;
v___y_3090_ = v___y_3105_;
v___y_3091_ = v___y_3106_;
v___y_3092_ = v___y_3107_;
v___y_3093_ = v___y_3108_;
v___y_3094_ = v___y_3109_;
v___y_3095_ = v___y_3110_;
v___y_3096_ = v___y_3111_;
goto v___jp_3080_;
}
else
{
lean_inc_ref(v_c_3117_);
lean_dec_ref_known(v_c_x3f_2840_, 2);
lean_del_object(v___x_2969_);
v___y_2987_ = v___y_3099_;
v___y_2988_ = v___y_3100_;
v___y_2989_ = v___y_3101_;
v___y_2990_ = v___y_3102_;
v___y_2991_ = v___y_3103_;
v___y_2992_ = v___y_3104_;
v___y_2993_ = v_c_3117_;
v___y_2994_ = v___y_3105_;
v___y_2995_ = v___y_3106_;
v___y_2996_ = v___y_3107_;
v___y_2997_ = v___y_3108_;
v___y_2998_ = v___y_3109_;
v___y_2999_ = v___y_3110_;
v___y_3000_ = v___y_3111_;
goto v___jp_2986_;
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3131_; 
lean_inc(v_head_2966_);
v___x_3131_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2966_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
switch(lean_obj_tag(v_a_3132_))
{
case 0:
{
lean_del_object(v___x_2969_);
lean_dec(v_head_2966_);
v_cs_2839_ = v_tail_2967_;
v_a_2842_ = v___y_3121_;
v_a_2843_ = v___y_3122_;
v_a_2844_ = v___y_3123_;
v_a_2845_ = v___y_3124_;
v_a_2846_ = v___y_3125_;
v_a_2847_ = v___y_3126_;
v_a_2848_ = v___y_3127_;
v_a_2849_ = v___y_3128_;
v_a_2850_ = v___y_3129_;
v_a_2851_ = v___y_3130_;
goto _start;
}
case 1:
{
lean_object* v___x_3134_; 
lean_del_object(v___x_2969_);
v___x_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_head_2966_);
lean_ctor_set(v___x_3134_, 1, v_cs_x27_2841_);
v_cs_2839_ = v_tail_2967_;
v_cs_x27_2841_ = v___x_3134_;
v_a_2842_ = v___y_3121_;
v_a_2843_ = v___y_3122_;
v_a_2844_ = v___y_3123_;
v_a_2845_ = v___y_3124_;
v_a_2846_ = v___y_3125_;
v_a_2847_ = v___y_3126_;
v_a_2848_ = v___y_3127_;
v_a_2849_ = v___y_3128_;
v_a_2850_ = v___y_3129_;
v_a_2851_ = v___y_3130_;
goto _start;
}
default: 
{
lean_object* v_numCases_3136_; uint8_t v_isRec_3137_; uint8_t v_tryPostpone_3138_; lean_object* v___x_3139_; 
v_numCases_3136_ = lean_ctor_get(v_a_3132_, 0);
lean_inc(v_numCases_3136_);
v_isRec_3137_ = lean_ctor_get_uint8(v_a_3132_, sizeof(void*)*1);
v_tryPostpone_3138_ = lean_ctor_get_uint8(v_a_3132_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3132_, 1);
v___x_3139_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3123_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; uint8_t v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = lean_unbox(v_a_3140_);
lean_dec(v_a_3140_);
if (v___x_3141_ == 0)
{
v___y_3099_ = v_tryPostpone_3138_;
v___y_3100_ = v___y_3123_;
v___y_3101_ = v___y_3124_;
v___y_3102_ = v___y_3126_;
v___y_3103_ = v_numCases_3136_;
v___y_3104_ = v___y_3125_;
v___y_3105_ = v___y_3130_;
v___y_3106_ = v___y_3122_;
v___y_3107_ = v___y_3121_;
v___y_3108_ = v_isRec_3137_;
v___y_3109_ = v___y_3128_;
v___y_3110_ = v___y_3127_;
v___y_3111_ = v___y_3129_;
goto v___jp_3098_;
}
else
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_dec_lt(v___x_3142_, v_numCases_3136_);
if (v___x_3143_ == 0)
{
v___y_3099_ = v_tryPostpone_3138_;
v___y_3100_ = v___y_3123_;
v___y_3101_ = v___y_3124_;
v___y_3102_ = v___y_3126_;
v___y_3103_ = v_numCases_3136_;
v___y_3104_ = v___y_3125_;
v___y_3105_ = v___y_3130_;
v___y_3106_ = v___y_3122_;
v___y_3107_ = v___y_3121_;
v___y_3108_ = v_isRec_3137_;
v___y_3109_ = v___y_3128_;
v___y_3110_ = v___y_3127_;
v___y_3111_ = v___y_3129_;
goto v___jp_3098_;
}
else
{
lean_object* v___x_3144_; 
lean_dec(v_numCases_3136_);
lean_del_object(v___x_2969_);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_head_2966_);
lean_ctor_set(v___x_3144_, 1, v_cs_x27_2841_);
v_cs_2839_ = v_tail_2967_;
v_cs_x27_2841_ = v___x_3144_;
v_a_2842_ = v___y_3121_;
v_a_2843_ = v___y_3122_;
v_a_2844_ = v___y_3123_;
v_a_2845_ = v___y_3124_;
v_a_2846_ = v___y_3125_;
v_a_2847_ = v___y_3126_;
v_a_2848_ = v___y_3127_;
v_a_2849_ = v___y_3128_;
v_a_2850_ = v___y_3129_;
v_a_2851_ = v___y_3130_;
goto _start;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_numCases_3136_);
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3146_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3139_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3139_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
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
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_del_object(v___x_2969_);
lean_dec(v_tail_2967_);
lean_dec(v_head_2966_);
lean_dec(v_cs_x27_2841_);
lean_dec(v_c_x3f_2840_);
v_a_3154_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3131_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3131_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3204_, lean_object* v_c_x3f_3205_, lean_object* v_cs_x27_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3204_, v_c_x3f_3205_, v_cs_x27_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3219_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3266_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
uint8_t v___x_3235_; 
v___x_3235_ = lean_unbox(v_a_3231_);
lean_dec(v_a_3231_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; 
lean_del_object(v___x_3233_);
v___x_3236_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3219_, v_a_3221_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3253_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v_toGoalState_3243_; lean_object* v_split_3244_; lean_object* v_candidates_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_del_object(v___x_3239_);
v___x_3242_ = lean_st_ref_get(v_a_3219_);
v_toGoalState_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_toGoalState_3243_);
lean_dec(v___x_3242_);
v_split_3244_ = lean_ctor_get(v_toGoalState_3243_, 14);
lean_inc_ref(v_split_3244_);
lean_dec_ref(v_toGoalState_3243_);
v_candidates_3245_ = lean_ctor_get(v_split_3244_, 1);
lean_inc(v_candidates_3245_);
lean_dec_ref(v_split_3244_);
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_box(0);
v___x_3248_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3245_, v___x_3246_, v___x_3247_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
return v___x_3248_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3249_);
v___x_3251_ = v___x_3239_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
v_a_3254_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3236_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3236_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = lean_box(0);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3262_);
v___x_3264_ = v___x_3233_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
v_a_3267_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3230_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3230_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_a_3275_);
return v_res_3286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3296_ = l_Lean_mkConst(v___x_3295_, v___x_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3297_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3299_ = l_Lean_Expr_app___override(v___x_3298_, v_c_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3310_ = l_Lean_mkConst(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3318_ = l_Lean_mkConst(v___x_3317_, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3326_ = l_Lean_mkConst(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; uint8_t v___y_3350_; lean_object* v___x_3386_; 
lean_inc_ref(v_c_3327_);
v___x_3386_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3327_, v_a_3335_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3472_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3472_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3472_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3404_ = l_Lean_Expr_cleanupAnnotations(v_a_3387_);
v___x_3405_ = l_Lean_Expr_isApp(v___x_3404_);
if (v___x_3405_ == 0)
{
lean_dec_ref(v___x_3404_);
lean_del_object(v___x_3389_);
v___y_3392_ = v_a_3328_;
v___y_3393_ = v_a_3329_;
v___y_3394_ = v_a_3330_;
v___y_3395_ = v_a_3331_;
v___y_3396_ = v_a_3332_;
v___y_3397_ = v_a_3333_;
v___y_3398_ = v_a_3334_;
v___y_3399_ = v_a_3335_;
v___y_3400_ = v_a_3336_;
v___y_3401_ = v_a_3337_;
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v_arg_3406_ = lean_ctor_get(v___x_3404_, 1);
lean_inc_ref(v_arg_3406_);
v___x_3407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3404_);
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3409_ = l_Lean_Expr_isConstOf(v___x_3407_, v___x_3408_);
if (v___x_3409_ == 0)
{
uint8_t v___x_3410_; 
v___x_3410_ = l_Lean_Expr_isApp(v___x_3407_);
if (v___x_3410_ == 0)
{
lean_dec_ref(v___x_3407_);
lean_dec_ref(v_arg_3406_);
lean_del_object(v___x_3389_);
v___y_3392_ = v_a_3328_;
v___y_3393_ = v_a_3329_;
v___y_3394_ = v_a_3330_;
v___y_3395_ = v_a_3331_;
v___y_3396_ = v_a_3332_;
v___y_3397_ = v_a_3333_;
v___y_3398_ = v_a_3334_;
v___y_3399_ = v_a_3335_;
v___y_3400_ = v_a_3336_;
v___y_3401_ = v_a_3337_;
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_arg_3411_ = lean_ctor_get(v___x_3407_, 1);
lean_inc_ref(v_arg_3411_);
v___x_3412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3407_);
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3414_ = l_Lean_Expr_isConstOf(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
uint8_t v___x_3415_; 
v___x_3415_ = l_Lean_Expr_isApp(v___x_3412_);
if (v___x_3415_ == 0)
{
lean_dec_ref(v___x_3412_);
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
lean_del_object(v___x_3389_);
v___y_3392_ = v_a_3328_;
v___y_3393_ = v_a_3329_;
v___y_3394_ = v_a_3330_;
v___y_3395_ = v_a_3331_;
v___y_3396_ = v_a_3332_;
v___y_3397_ = v_a_3333_;
v___y_3398_ = v_a_3334_;
v___y_3399_ = v_a_3335_;
v___y_3400_ = v_a_3336_;
v___y_3401_ = v_a_3337_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3412_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3418_ = l_Lean_Expr_isConstOf(v___x_3416_, v___x_3417_);
lean_dec_ref(v___x_3416_);
if (v___x_3418_ == 0)
{
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
lean_del_object(v___x_3389_);
v___y_3392_ = v_a_3328_;
v___y_3393_ = v_a_3329_;
v___y_3394_ = v_a_3330_;
v___y_3395_ = v_a_3331_;
v___y_3396_ = v_a_3332_;
v___y_3397_ = v_a_3333_;
v___y_3398_ = v_a_3334_;
v___y_3399_ = v_a_3335_;
v___y_3400_ = v_a_3336_;
v___y_3401_ = v_a_3337_;
goto v___jp_3391_;
}
else
{
uint8_t v___x_3419_; 
lean_inc_ref(v_c_3327_);
v___x_3419_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3327_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
v___x_3420_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3327_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3420_);
v___x_3422_ = v___x_3389_;
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
else
{
lean_object* v___x_3424_; 
lean_del_object(v___x_3389_);
lean_inc_ref(v_c_3327_);
v___x_3424_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3327_, v_a_3328_, v_a_3332_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; uint8_t v___x_3426_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = lean_unbox(v_a_3425_);
lean_dec(v_a_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3437_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3433_ = l_Lean_mkApp3(v___x_3432_, v_arg_3411_, v_arg_3406_, v_a_3428_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3435_ = v___x_3430_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
return v___x_3427_;
}
}
else
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
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
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3444_ = l_Lean_mkApp3(v___x_3443_, v_arg_3411_, v_arg_3406_, v_a_3439_);
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
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
return v___x_3438_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
lean_dec_ref(v_c_3327_);
v_a_3449_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3424_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3424_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec_ref(v___x_3412_);
lean_del_object(v___x_3389_);
v___x_3457_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3467_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3467_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3467_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3463_ = l_Lean_mkApp3(v___x_3462_, v_arg_3411_, v_arg_3406_, v_a_3458_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3463_);
v___x_3465_ = v___x_3460_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3406_);
return v___x_3457_;
}
}
}
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec_ref(v___x_3407_);
lean_dec_ref(v_c_3327_);
v___x_3468_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3406_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3468_);
v___x_3470_ = v___x_3389_;
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
v___jp_3391_:
{
uint8_t v___x_3402_; 
v___x_3402_ = l_Lean_Meta_Grind_isIte(v_c_3327_);
if (v___x_3402_ == 0)
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Meta_Grind_isDIte(v_c_3327_);
v___y_3340_ = v___y_3395_;
v___y_3341_ = v___y_3393_;
v___y_3342_ = v___y_3396_;
v___y_3343_ = v___y_3401_;
v___y_3344_ = v___y_3399_;
v___y_3345_ = v___y_3398_;
v___y_3346_ = v___y_3392_;
v___y_3347_ = v___y_3394_;
v___y_3348_ = v___y_3397_;
v___y_3349_ = v___y_3400_;
v___y_3350_ = v___x_3403_;
goto v___jp_3339_;
}
else
{
v___y_3340_ = v___y_3395_;
v___y_3341_ = v___y_3393_;
v___y_3342_ = v___y_3396_;
v___y_3343_ = v___y_3401_;
v___y_3344_ = v___y_3399_;
v___y_3345_ = v___y_3398_;
v___y_3346_ = v___y_3392_;
v___y_3347_ = v___y_3394_;
v___y_3348_ = v___y_3397_;
v___y_3349_ = v___y_3400_;
v___y_3350_ = v___x_3402_;
goto v___jp_3339_;
}
}
}
}
else
{
lean_dec_ref(v_c_3327_);
return v___x_3386_;
}
v___jp_3339_:
{
if (v___y_3350_ == 0)
{
lean_object* v___x_3351_; 
lean_inc_ref(v_c_3327_);
v___x_3351_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3327_, v___y_3346_, v___y_3342_, v___y_3345_, v___y_3344_, v___y_3349_, v___y_3343_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3370_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_unbox(v_a_3352_);
lean_dec(v_a_3352_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3358_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_c_3327_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_c_3327_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
else
{
lean_object* v___x_3360_; 
lean_del_object(v___x_3354_);
lean_inc_ref(v_c_3327_);
v___x_3360_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3327_, v___y_3346_, v___y_3341_, v___y_3347_, v___y_3340_, v___y_3342_, v___y_3348_, v___y_3345_, v___y_3344_, v___y_3349_, v___y_3343_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3369_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3369_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3365_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3327_, v_a_3361_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3365_);
v___x_3367_ = v___x_3363_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
else
{
lean_dec_ref(v_c_3327_);
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_c_3327_);
v_a_3371_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3351_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3351_);
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
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = l_Lean_Expr_getAppNumArgs(v_c_3327_);
v___x_3381_ = lean_nat_sub(v___x_3380_, v___x_3379_);
lean_dec(v___x_3380_);
v___x_3382_ = lean_nat_sub(v___x_3381_, v___x_3379_);
lean_dec(v___x_3381_);
v___x_3383_ = l_Lean_Expr_getRevArg_x21(v_c_3327_, v___x_3382_);
lean_dec_ref(v_c_3327_);
v___x_3384_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec(v_a_3474_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3486_, lean_object* v_major_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3488_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; uint8_t v_trace_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_trace_3497_ = lean_ctor_get_uint8(v_a_3496_, sizeof(void*)*13);
lean_dec(v_a_3496_);
if (v_trace_3497_ == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Meta_Grind_cases(v_mvarId_3486_, v_major_3487_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; 
lean_inc(v_a_3493_);
lean_inc_ref(v_a_3492_);
lean_inc(v_a_3491_);
lean_inc_ref(v_a_3490_);
lean_inc_ref(v_major_3487_);
v___x_3499_ = lean_infer_type(v_major_3487_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = l_Lean_Meta_whnfD(v_a_3500_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_Expr_getAppFn(v_a_3502_);
lean_dec(v_a_3502_);
if (lean_obj_tag(v___x_3503_) == 4)
{
lean_object* v_declName_3504_; lean_object* v___x_3505_; 
v_declName_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_declName_3504_);
lean_dec_ref_known(v___x_3503_, 2);
v___x_3505_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3504_, v_a_3489_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3505_, 1);
v___x_3506_ = l_Lean_Meta_Grind_cases(v_mvarId_3486_, v_major_3487_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
return v___x_3506_;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v_major_3487_);
lean_dec(v_mvarId_3486_);
v_a_3507_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3505_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3505_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v___x_3515_; 
lean_dec_ref(v___x_3503_);
v___x_3515_ = l_Lean_Meta_Grind_cases(v_mvarId_3486_, v_major_3487_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
return v___x_3515_;
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v_major_3487_);
lean_dec(v_mvarId_3486_);
v_a_3516_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3501_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3501_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v_major_3487_);
lean_dec(v_mvarId_3486_);
v_a_3524_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3499_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3499_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec_ref(v_major_3487_);
lean_dec(v_mvarId_3486_);
v_a_3532_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3495_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3495_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3540_, lean_object* v_major_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3540_, v_major_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3550_, lean_object* v_major_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3550_, v_major_3551_, v_a_3554_, v_a_3555_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3564_, lean_object* v_major_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3564_, v_major_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec(v_a_3566_);
return v_res_3577_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3578_){
_start:
{
uint64_t v_anchor_3579_; 
v_anchor_3579_ = lean_ctor_get_uint64(v_e_3578_, sizeof(void*)*3);
return v_anchor_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3580_){
_start:
{
uint64_t v_res_3581_; lean_object* v_r_3582_; 
v_res_3581_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3580_);
lean_dec_ref(v_e_3580_);
v_r_3582_ = lean_box_uint64(v_res_3581_);
return v_r_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3585_, lean_object* v_x_3586_){
_start:
{
if (lean_obj_tag(v_x_3586_) == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_box(0);
return v___x_3587_;
}
else
{
lean_object* v_key_3588_; lean_object* v_value_3589_; lean_object* v_tail_3590_; uint64_t v___x_3591_; uint8_t v___x_3592_; 
v_key_3588_ = lean_ctor_get(v_x_3586_, 0);
v_value_3589_ = lean_ctor_get(v_x_3586_, 1);
v_tail_3590_ = lean_ctor_get(v_x_3586_, 2);
v___x_3591_ = lean_unbox_uint64(v_key_3588_);
v___x_3592_ = lean_uint64_dec_eq(v___x_3591_, v_a_3585_);
if (v___x_3592_ == 0)
{
v_x_3586_ = v_tail_3590_;
goto _start;
}
else
{
lean_object* v___x_3594_; 
lean_inc(v_value_3589_);
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_value_3589_);
return v___x_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3595_, lean_object* v_x_3596_){
_start:
{
uint64_t v_a_boxed_3597_; lean_object* v_res_3598_; 
v_a_boxed_3597_ = lean_unbox_uint64(v_a_3595_);
lean_dec_ref(v_a_3595_);
v_res_3598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3597_, v_x_3596_);
lean_dec(v_x_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3599_, uint64_t v_a_3600_){
_start:
{
lean_object* v_buckets_3601_; lean_object* v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; uint64_t v_fold_3605_; uint64_t v___x_3606_; uint64_t v___x_3607_; uint64_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_buckets_3601_ = lean_ctor_get(v_m_3599_, 1);
v___x_3602_ = lean_array_get_size(v_buckets_3601_);
v___x_3603_ = 32ULL;
v___x_3604_ = lean_uint64_shift_right(v_a_3600_, v___x_3603_);
v_fold_3605_ = lean_uint64_xor(v_a_3600_, v___x_3604_);
v___x_3606_ = 16ULL;
v___x_3607_ = lean_uint64_shift_right(v_fold_3605_, v___x_3606_);
v___x_3608_ = lean_uint64_xor(v_fold_3605_, v___x_3607_);
v___x_3609_ = lean_uint64_to_usize(v___x_3608_);
v___x_3610_ = lean_usize_of_nat(v___x_3602_);
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_sub(v___x_3610_, v___x_3611_);
v___x_3613_ = lean_usize_land(v___x_3609_, v___x_3612_);
v___x_3614_ = lean_array_uget_borrowed(v_buckets_3601_, v___x_3613_);
v___x_3615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3600_, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3616_, lean_object* v_a_3617_){
_start:
{
uint64_t v_a_boxed_3618_; lean_object* v_res_3619_; 
v_a_boxed_3618_ = lean_unbox_uint64(v_a_3617_);
lean_dec_ref(v_a_3617_);
v_res_3619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3616_, v_a_boxed_3618_);
lean_dec_ref(v_m_3616_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
return v_x_3620_;
}
else
{
lean_object* v_key_3622_; lean_object* v_value_3623_; lean_object* v_tail_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3648_; 
v_key_3622_ = lean_ctor_get(v_x_3621_, 0);
v_value_3623_ = lean_ctor_get(v_x_3621_, 1);
v_tail_3624_ = lean_ctor_get(v_x_3621_, 2);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_x_3621_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3626_ = v_x_3621_;
v_isShared_3627_ = v_isSharedCheck_3648_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_tail_3624_);
lean_inc(v_value_3623_);
lean_inc(v_key_3622_);
lean_dec(v_x_3621_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3648_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; uint64_t v___x_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v_fold_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; uint64_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3628_ = lean_array_get_size(v_x_3620_);
v___x_3629_ = 32ULL;
v___x_3630_ = lean_unbox_uint64(v_key_3622_);
v___x_3631_ = lean_uint64_shift_right(v___x_3630_, v___x_3629_);
v___x_3632_ = lean_unbox_uint64(v_key_3622_);
v_fold_3633_ = lean_uint64_xor(v___x_3632_, v___x_3631_);
v___x_3634_ = 16ULL;
v___x_3635_ = lean_uint64_shift_right(v_fold_3633_, v___x_3634_);
v___x_3636_ = lean_uint64_xor(v_fold_3633_, v___x_3635_);
v___x_3637_ = lean_uint64_to_usize(v___x_3636_);
v___x_3638_ = lean_usize_of_nat(v___x_3628_);
v___x_3639_ = ((size_t)1ULL);
v___x_3640_ = lean_usize_sub(v___x_3638_, v___x_3639_);
v___x_3641_ = lean_usize_land(v___x_3637_, v___x_3640_);
v___x_3642_ = lean_array_uget_borrowed(v_x_3620_, v___x_3641_);
lean_inc(v___x_3642_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 2, v___x_3642_);
v___x_3644_ = v___x_3626_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_key_3622_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_value_3623_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_array_uset(v_x_3620_, v___x_3641_, v___x_3644_);
v_x_3620_ = v___x_3645_;
v_x_3621_ = v_tail_3624_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3649_, lean_object* v_source_3650_, lean_object* v_target_3651_){
_start:
{
lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = lean_array_get_size(v_source_3650_);
v___x_3653_ = lean_nat_dec_lt(v_i_3649_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec_ref(v_source_3650_);
lean_dec(v_i_3649_);
return v_target_3651_;
}
else
{
lean_object* v_es_3654_; lean_object* v___x_3655_; lean_object* v_source_3656_; lean_object* v_target_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_es_3654_ = lean_array_fget(v_source_3650_, v_i_3649_);
v___x_3655_ = lean_box(0);
v_source_3656_ = lean_array_fset(v_source_3650_, v_i_3649_, v___x_3655_);
v_target_3657_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3651_, v_es_3654_);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_i_3649_, v___x_3658_);
lean_dec(v_i_3649_);
v_i_3649_ = v___x_3659_;
v_source_3650_ = v_source_3656_;
v_target_3651_ = v_target_3657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3661_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v_nbuckets_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3662_ = lean_array_get_size(v_data_3661_);
v___x_3663_ = lean_unsigned_to_nat(2u);
v_nbuckets_3664_ = lean_nat_mul(v___x_3662_, v___x_3663_);
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_mk_array(v_nbuckets_3664_, v___x_3666_);
v___x_3668_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3665_, v_data_3661_, v___x_3667_);
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
lean_object* v_snd_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3817_; 
v_snd_3782_ = lean_ctor_get(v_b_3775_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_b_3775_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; 
v_unused_3818_ = lean_ctor_get(v_b_3775_, 0);
lean_dec(v_unused_3818_);
v___x_3784_ = v_b_3775_;
v_isShared_3785_ = v_isSharedCheck_3817_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_snd_3782_);
lean_dec(v_b_3775_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3817_;
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
lean_object* v_val_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3811_; 
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3794_ = v___x_3791_;
v_isShared_3795_ = v_isSharedCheck_3811_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_val_3792_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3811_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
uint64_t v___x_3796_; uint8_t v___x_3797_; uint8_t v___x_3798_; 
v___x_3796_ = lean_unbox_uint64(v_val_3792_);
lean_dec(v_val_3792_);
v___x_3797_ = lean_uint64_dec_eq(v___x_3796_, v_anchor_3787_);
v___x_3798_ = lean_bool_not(v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3800_; 
lean_del_object(v___x_3794_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3788_);
v___x_3800_ = v___x_3784_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_snd_3782_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
v_a_3777_ = v___x_3800_;
goto v___jp_3776_;
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_add(v_numDigits_3770_, v___x_3802_);
v___x_3804_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3771_, v___x_3803_);
lean_dec(v___x_3803_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3804_);
v___x_3806_ = v___x_3794_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3808_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3806_);
v___x_3808_ = v___x_3784_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_snd_3782_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
lean_dec(v___x_3791_);
v___x_3812_ = lean_box_uint64(v_anchor_3787_);
v___x_3813_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3782_, v___x_3790_, v___x_3812_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v___x_3813_);
lean_ctor_set(v___x_3784_, 0, v___x_3788_);
v___x_3815_ = v___x_3784_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v_a_3777_ = v___x_3815_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3819_, lean_object* v_numDigits_3820_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3821_ = lean_unsigned_to_nat(4u);
v___x_3822_ = lean_nat_mul(v___x_3821_, v_numDigits_3820_);
v___x_3823_ = lean_unsigned_to_nat(64u);
v___x_3824_ = lean_nat_dec_lt(v___x_3822_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_dec(v___x_3822_);
lean_inc(v_numDigits_3820_);
return v_numDigits_3820_;
}
else
{
lean_object* v_shift_3825_; lean_object* v___x_3826_; size_t v_sz_3827_; size_t v___x_3828_; lean_object* v___x_3829_; lean_object* v_fst_3830_; 
v_shift_3825_ = lean_nat_sub(v___x_3823_, v___x_3822_);
lean_dec(v___x_3822_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3827_ = lean_array_size(v_es_3819_);
v___x_3828_ = ((size_t)0ULL);
v___x_3829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3825_, v_numDigits_3820_, v_es_3819_, v_es_3819_, v_sz_3827_, v___x_3828_, v___x_3826_);
lean_dec(v_shift_3825_);
v_fst_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_fst_3830_);
lean_dec_ref(v___x_3829_);
if (lean_obj_tag(v_fst_3830_) == 0)
{
lean_inc(v_numDigits_3820_);
return v_numDigits_3820_;
}
else
{
lean_object* v_val_3831_; 
v_val_3831_ = lean_ctor_get(v_fst_3830_, 0);
lean_inc(v_val_3831_);
lean_dec_ref_known(v_fst_3830_, 1);
return v_val_3831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3832_, lean_object* v_numDigits_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3832_, v_numDigits_3833_);
lean_dec(v_numDigits_3833_);
lean_dec_ref(v_es_3832_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3835_, lean_object* v_numDigits_3836_, lean_object* v_es_3837_, lean_object* v_as_3838_, lean_object* v_sz_3839_, lean_object* v_i_3840_, lean_object* v_b_3841_){
_start:
{
size_t v_sz_boxed_3842_; size_t v_i_boxed_3843_; lean_object* v_res_3844_; 
v_sz_boxed_3842_ = lean_unbox_usize(v_sz_3839_);
lean_dec(v_sz_3839_);
v_i_boxed_3843_ = lean_unbox_usize(v_i_3840_);
lean_dec(v_i_3840_);
v_res_3844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3835_, v_numDigits_3836_, v_es_3837_, v_as_3838_, v_sz_boxed_3842_, v_i_boxed_3843_, v_b_3841_);
lean_dec_ref(v_as_3838_);
lean_dec_ref(v_es_3837_);
lean_dec(v_numDigits_3836_);
lean_dec(v_shift_3835_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3845_){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_unsigned_to_nat(4u);
v___x_3847_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3845_, v___x_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3848_);
lean_dec_ref(v_es_3848_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3850_, lean_object* v_as_3851_, size_t v_i_3852_, size_t v_stop_3853_, lean_object* v_b_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_a_3867_; uint8_t v___x_3871_; 
v___x_3871_ = lean_usize_dec_eq(v_i_3852_, v_stop_3853_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_array_uget_borrowed(v_as_3851_, v_i_3852_);
v___x_3873_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3872_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v_e_3875_; lean_object* v___x_3876_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v_e_3875_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3872_);
lean_inc(v___x_3872_);
v___x_3876_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3872_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
if (lean_obj_tag(v_a_3877_) == 2)
{
lean_object* v_numCases_3878_; uint8_t v_isRec_3879_; lean_object* v___x_3880_; 
v_numCases_3878_ = lean_ctor_get(v_a_3877_, 0);
lean_inc(v_numCases_3878_);
v_isRec_3879_ = lean_ctor_get_uint8(v_a_3877_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3877_, 1);
lean_inc_ref(v_filter_3850_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v_e_3875_);
v___x_3880_ = lean_apply_12(v_filter_3850_, v_e_3875_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, lean_box(0));
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; uint8_t v___x_3882_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = lean_unbox(v_a_3881_);
lean_dec(v_a_3881_);
if (v___x_3882_ == 0)
{
lean_dec(v_numCases_3878_);
lean_dec_ref(v_e_3875_);
lean_dec(v_a_3874_);
v_a_3867_ = v_b_3854_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3883_; uint64_t v___x_3884_; lean_object* v___x_3885_; 
lean_inc(v___x_3872_);
v___x_3883_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3883_, 0, v___x_3872_);
lean_ctor_set(v___x_3883_, 1, v_numCases_3878_);
lean_ctor_set(v___x_3883_, 2, v_e_3875_);
lean_ctor_set_uint8(v___x_3883_, sizeof(void*)*3 + 8, v_isRec_3879_);
v___x_3884_ = lean_unbox_uint64(v_a_3874_);
lean_dec(v_a_3874_);
lean_ctor_set_uint64(v___x_3883_, sizeof(void*)*3, v___x_3884_);
v___x_3885_ = lean_array_push(v_b_3854_, v___x_3883_);
v_a_3867_ = v___x_3885_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec(v_numCases_3878_);
lean_dec_ref(v_e_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_b_3854_);
lean_dec_ref(v_filter_3850_);
v_a_3886_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3880_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3880_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_dec(v_a_3877_);
lean_dec_ref(v_e_3875_);
lean_dec(v_a_3874_);
v_a_3867_ = v_b_3854_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec_ref(v_e_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_b_3854_);
lean_dec_ref(v_filter_3850_);
v_a_3894_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3876_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3876_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec_ref(v_b_3854_);
lean_dec_ref(v_filter_3850_);
v_a_3902_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3873_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3873_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
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
else
{
lean_object* v___x_3910_; 
lean_dec_ref(v_filter_3850_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_b_3854_);
return v___x_3910_;
}
v___jp_3866_:
{
size_t v___x_3868_; size_t v___x_3869_; 
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3852_, v___x_3868_);
v_i_3852_ = v___x_3869_;
v_b_3854_ = v_a_3867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3911_, lean_object* v_as_3912_, lean_object* v_i_3913_, lean_object* v_stop_3914_, lean_object* v_b_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
size_t v_i_boxed_3927_; size_t v_stop_boxed_3928_; lean_object* v_res_3929_; 
v_i_boxed_3927_ = lean_unbox_usize(v_i_3913_);
lean_dec(v_i_3913_);
v_stop_boxed_3928_ = lean_unbox_usize(v_stop_3914_);
lean_dec(v_stop_3914_);
v_res_3929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3911_, v_as_3912_, v_i_boxed_3927_, v_stop_boxed_3928_, v_b_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v_as_3912_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3932_, lean_object* v_as_3933_, lean_object* v_start_3934_, lean_object* v_stop_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3948_ = lean_nat_dec_lt(v_start_3934_, v_stop_3935_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref(v_filter_3932_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = lean_array_get_size(v_as_3933_);
v___x_3951_ = lean_nat_dec_le(v_stop_3935_, v___x_3950_);
if (v___x_3951_ == 0)
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_nat_dec_lt(v_start_3934_, v___x_3950_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v_filter_3932_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3947_);
return v___x_3953_;
}
else
{
size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = lean_usize_of_nat(v_start_3934_);
v___x_3955_ = lean_usize_of_nat(v___x_3950_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3932_, v_as_3933_, v___x_3954_, v___x_3955_, v___x_3947_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3956_;
}
}
else
{
size_t v___x_3957_; size_t v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_usize_of_nat(v_start_3934_);
v___x_3958_ = lean_usize_of_nat(v_stop_3935_);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3932_, v_as_3933_, v___x_3957_, v___x_3958_, v___x_3947_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
return v___x_3959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3960_, lean_object* v_as_3961_, lean_object* v_start_3962_, lean_object* v_stop_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3960_, v_as_3961_, v_start_3962_, v_stop_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v_stop_3963_);
lean_dec(v_start_3962_);
lean_dec_ref(v_as_3961_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3976_, lean_object* v_candidates_x3f_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_candidates_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; 
if (lean_obj_tag(v_candidates_x3f_3977_) == 0)
{
lean_object* v___x_4023_; lean_object* v_toGoalState_4024_; lean_object* v_split_4025_; lean_object* v_candidates_4026_; 
v___x_4023_ = lean_st_ref_get(v_a_3978_);
v_toGoalState_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc_ref(v_toGoalState_4024_);
lean_dec(v___x_4023_);
v_split_4025_ = lean_ctor_get(v_toGoalState_4024_, 14);
lean_inc_ref(v_split_4025_);
lean_dec_ref(v_toGoalState_4024_);
v_candidates_4026_ = lean_ctor_get(v_split_4025_, 1);
lean_inc(v_candidates_4026_);
lean_dec_ref(v_split_4025_);
v_candidates_3990_ = v_candidates_4026_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
goto v___jp_3989_;
}
else
{
lean_object* v_val_4027_; 
v_val_4027_ = lean_ctor_get(v_candidates_x3f_3977_, 0);
lean_inc(v_val_4027_);
lean_dec_ref_known(v_candidates_x3f_3977_, 1);
v_candidates_3990_ = v_val_4027_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
goto v___jp_3989_;
}
v___jp_3989_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = lean_array_mk(v_candidates_3990_);
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4003_ = lean_array_get_size(v___x_4001_);
v___x_4004_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3976_, v___x_4001_, v___x_4002_, v___x_4003_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
lean_dec_ref(v___x_4001_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4014_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4014_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4014_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4009_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4005_);
v___x_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4010_, 0, v_a_4005_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4010_);
v___x_4012_ = v___x_4007_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v_a_4015_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4004_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4004_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4028_, lean_object* v_candidates_x3f_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4028_, v_candidates_x3f_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec(v_a_4030_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4042_, lean_object* v_m_4043_, uint64_t v_a_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4043_, v_a_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_m_4047_, lean_object* v_a_4048_){
_start:
{
uint64_t v_a_boxed_4049_; lean_object* v_res_4050_; 
v_a_boxed_4049_ = lean_unbox_uint64(v_a_4048_);
lean_dec_ref(v_a_4048_);
v_res_4050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4046_, v_m_4047_, v_a_boxed_4049_);
lean_dec_ref(v_m_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4051_, lean_object* v_m_4052_, uint64_t v_a_4053_, lean_object* v_b_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4052_, v_a_4053_, v_b_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4056_, lean_object* v_m_4057_, lean_object* v_a_4058_, lean_object* v_b_4059_){
_start:
{
uint64_t v_a_boxed_4060_; lean_object* v_res_4061_; 
v_a_boxed_4060_ = lean_unbox_uint64(v_a_4058_);
lean_dec_ref(v_a_4058_);
v_res_4061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4056_, v_m_4057_, v_a_boxed_4060_, v_b_4059_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4062_, uint64_t v_a_4063_, lean_object* v_x_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4063_, v_x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4066_, lean_object* v_a_4067_, lean_object* v_x_4068_){
_start:
{
uint64_t v_a_boxed_4069_; lean_object* v_res_4070_; 
v_a_boxed_4069_ = lean_unbox_uint64(v_a_4067_);
lean_dec_ref(v_a_4067_);
v_res_4070_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4066_, v_a_boxed_4069_, v_x_4068_);
lean_dec(v_x_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4071_, uint64_t v_a_4072_, lean_object* v_x_4073_){
_start:
{
uint8_t v___x_4074_; 
v___x_4074_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4072_, v_x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4075_, lean_object* v_a_4076_, lean_object* v_x_4077_){
_start:
{
uint64_t v_a_boxed_4078_; uint8_t v_res_4079_; lean_object* v_r_4080_; 
v_a_boxed_4078_ = lean_unbox_uint64(v_a_4076_);
lean_dec_ref(v_a_4076_);
v_res_4079_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4075_, v_a_boxed_4078_, v_x_4077_);
lean_dec(v_x_4077_);
v_r_4080_ = lean_box(v_res_4079_);
return v_r_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4081_, lean_object* v_data_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4084_, uint64_t v_a_4085_, lean_object* v_b_4086_, lean_object* v_x_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4085_, v_b_4086_, v_x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4089_, lean_object* v_a_4090_, lean_object* v_b_4091_, lean_object* v_x_4092_){
_start:
{
uint64_t v_a_boxed_4093_; lean_object* v_res_4094_; 
v_a_boxed_4093_ = lean_unbox_uint64(v_a_4090_);
lean_dec_ref(v_a_4090_);
v_res_4094_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4089_, v_a_boxed_4093_, v_b_4091_, v_x_4092_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4095_, lean_object* v_i_4096_, lean_object* v_source_4097_, lean_object* v_target_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4096_, v_source_4097_, v_target_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4100_, lean_object* v_x_4101_, lean_object* v_x_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4101_, v_x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
uint8_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = 1;
v___x_4117_ = lean_box(v___x_4116_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v_x_4119_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4132_, uint64_t v_a_4133_, lean_object* v_c_4134_, lean_object* v_numDigits_4135_, lean_object* v_as_4136_, size_t v_sz_4137_, size_t v_i_4138_, lean_object* v_b_4139_){
_start:
{
lean_object* v_a_4142_; uint8_t v___x_4146_; 
v___x_4146_ = lean_usize_dec_lt(v_i_4138_, v_sz_4137_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_dec(v_numDigits_4135_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_b_4139_);
return v___x_4147_;
}
else
{
lean_object* v_snd_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4174_; 
v_snd_4148_ = lean_ctor_get(v_b_4139_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_b_4139_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; 
v_unused_4175_ = lean_ctor_get(v_b_4139_, 0);
lean_dec(v_unused_4175_);
v___x_4150_ = v_b_4139_;
v_isShared_4151_ = v_isSharedCheck_4174_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_snd_4148_);
lean_dec(v_b_4139_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4174_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v_a_4152_; lean_object* v_c_4153_; uint64_t v_anchor_4154_; lean_object* v___x_4155_; uint64_t v___x_4156_; uint64_t v___x_4157_; uint8_t v___x_4158_; 
v_a_4152_ = lean_array_uget_borrowed(v_as_4136_, v_i_4138_);
v_c_4153_ = lean_ctor_get(v_a_4152_, 0);
v_anchor_4154_ = lean_ctor_get_uint64(v_a_4152_, sizeof(void*)*3);
v___x_4155_ = lean_box(0);
v___x_4156_ = lean_uint64_shift_right(v_anchor_4154_, v___x_4132_);
v___x_4157_ = lean_uint64_shift_right(v_a_4133_, v___x_4132_);
v___x_4158_ = lean_uint64_dec_eq(v___x_4156_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4160_; 
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4155_);
v___x_4160_ = v___x_4150_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_snd_4148_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
v_a_4142_ = v___x_4160_;
goto v___jp_4141_;
}
}
else
{
uint8_t v___x_4162_; 
v___x_4162_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4153_, v_c_4134_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4163_ = lean_unsigned_to_nat(1u);
v___x_4164_ = lean_nat_add(v_snd_4148_, v___x_4163_);
lean_dec(v_snd_4148_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v___x_4164_);
lean_ctor_set(v___x_4150_, 0, v___x_4155_);
v___x_4166_ = v___x_4150_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
v_a_4142_ = v___x_4166_;
goto v___jp_4141_;
}
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
lean_inc(v_snd_4148_);
v___x_4168_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4168_, 0, v_numDigits_4135_);
lean_ctor_set(v___x_4168_, 1, v_snd_4148_);
lean_ctor_set_uint64(v___x_4168_, sizeof(void*)*2, v_a_4133_);
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4169_);
v___x_4171_ = v___x_4150_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_snd_4148_);
v___x_4171_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
}
}
}
}
v___jp_4141_:
{
size_t v___x_4143_; size_t v___x_4144_; 
v___x_4143_ = ((size_t)1ULL);
v___x_4144_ = lean_usize_add(v_i_4138_, v___x_4143_);
v_i_4138_ = v___x_4144_;
v_b_4139_ = v_a_4142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4176_, lean_object* v_a_4177_, lean_object* v_c_4178_, lean_object* v_numDigits_4179_, lean_object* v_as_4180_, lean_object* v_sz_4181_, lean_object* v_i_4182_, lean_object* v_b_4183_, lean_object* v___y_4184_){
_start:
{
uint64_t v___x_8573__boxed_4185_; uint64_t v_a_8574__boxed_4186_; size_t v_sz_boxed_4187_; size_t v_i_boxed_4188_; lean_object* v_res_4189_; 
v___x_8573__boxed_4185_ = lean_unbox_uint64(v___x_4176_);
lean_dec_ref(v___x_4176_);
v_a_8574__boxed_4186_ = lean_unbox_uint64(v_a_4177_);
lean_dec_ref(v_a_4177_);
v_sz_boxed_4187_ = lean_unbox_usize(v_sz_4181_);
lean_dec(v_sz_4181_);
v_i_boxed_4188_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_res_4189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_8573__boxed_4185_, v_a_8574__boxed_4186_, v_c_4178_, v_numDigits_4179_, v_as_4180_, v_sz_boxed_4187_, v_i_boxed_4188_, v_b_4183_);
lean_dec_ref(v_as_4180_);
lean_dec_ref(v_c_4178_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4194_, lean_object* v_candidates_x3f_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v___f_4207_; lean_object* v___x_4208_; 
v___f_4207_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4208_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4207_, v_candidates_x3f_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v_candidates_4210_; lean_object* v_numDigits_4211_; lean_object* v___x_4212_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v_candidates_4210_ = lean_ctor_get(v_a_4209_, 0);
lean_inc_ref(v_candidates_4210_);
v_numDigits_4211_ = lean_ctor_get(v_a_4209_, 1);
lean_inc(v_numDigits_4211_);
lean_dec(v_a_4209_);
v___x_4212_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4194_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint64_t v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; size_t v_sz_4221_; size_t v___x_4222_; uint64_t v___x_4223_; lean_object* v___x_4224_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = lean_unsigned_to_nat(64u);
v___x_4215_ = lean_unsigned_to_nat(4u);
v___x_4216_ = lean_nat_mul(v___x_4215_, v_numDigits_4211_);
v___x_4217_ = lean_nat_sub(v___x_4214_, v___x_4216_);
lean_dec(v___x_4216_);
v___x_4218_ = lean_uint64_of_nat(v___x_4217_);
lean_dec(v___x_4217_);
v___x_4219_ = lean_unsigned_to_nat(0u);
v___x_4220_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4221_ = lean_array_size(v_candidates_4210_);
v___x_4222_ = ((size_t)0ULL);
v___x_4223_ = lean_unbox_uint64(v_a_4213_);
lean_inc(v_numDigits_4211_);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4218_, v___x_4223_, v_c_4194_, v_numDigits_4211_, v_candidates_4210_, v_sz_4221_, v___x_4222_, v___x_4220_);
lean_dec_ref(v_candidates_4210_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4239_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_fst_4229_; 
v_fst_4229_ = lean_ctor_get(v_a_4225_, 0);
lean_inc(v_fst_4229_);
lean_dec(v_a_4225_);
if (lean_obj_tag(v_fst_4229_) == 0)
{
lean_object* v___x_4230_; uint64_t v___x_4231_; lean_object* v___x_4233_; 
v___x_4230_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4230_, 0, v_numDigits_4211_);
lean_ctor_set(v___x_4230_, 1, v___x_4219_);
v___x_4231_ = lean_unbox_uint64(v_a_4213_);
lean_dec(v_a_4213_);
lean_ctor_set_uint64(v___x_4230_, sizeof(void*)*2, v___x_4231_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4230_);
v___x_4233_ = v___x_4227_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4230_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
else
{
lean_object* v_val_4235_; lean_object* v___x_4237_; 
lean_dec(v_a_4213_);
lean_dec(v_numDigits_4211_);
v_val_4235_ = lean_ctor_get(v_fst_4229_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v_fst_4229_, 1);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v_val_4235_);
v___x_4237_ = v___x_4227_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_val_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_a_4213_);
lean_dec(v_numDigits_4211_);
v_a_4240_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4224_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4224_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_numDigits_4211_);
lean_dec_ref(v_candidates_4210_);
v_a_4248_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4212_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4212_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4208_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4208_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4264_, lean_object* v_candidates_x3f_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4264_, v_candidates_x3f_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_c_4264_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4278_, uint64_t v_a_4279_, lean_object* v_c_4280_, lean_object* v_numDigits_4281_, lean_object* v_as_4282_, size_t v_sz_4283_, size_t v_i_4284_, lean_object* v_b_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4278_, v_a_4279_, v_c_4280_, v_numDigits_4281_, v_as_4282_, v_sz_4283_, v_i_4284_, v_b_4285_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4298_ = _args[0];
lean_object* v_a_4299_ = _args[1];
lean_object* v_c_4300_ = _args[2];
lean_object* v_numDigits_4301_ = _args[3];
lean_object* v_as_4302_ = _args[4];
lean_object* v_sz_4303_ = _args[5];
lean_object* v_i_4304_ = _args[6];
lean_object* v_b_4305_ = _args[7];
lean_object* v___y_4306_ = _args[8];
lean_object* v___y_4307_ = _args[9];
lean_object* v___y_4308_ = _args[10];
lean_object* v___y_4309_ = _args[11];
lean_object* v___y_4310_ = _args[12];
lean_object* v___y_4311_ = _args[13];
lean_object* v___y_4312_ = _args[14];
lean_object* v___y_4313_ = _args[15];
lean_object* v___y_4314_ = _args[16];
lean_object* v___y_4315_ = _args[17];
lean_object* v___y_4316_ = _args[18];
_start:
{
uint64_t v___x_8772__boxed_4317_; uint64_t v_a_8773__boxed_4318_; size_t v_sz_boxed_4319_; size_t v_i_boxed_4320_; lean_object* v_res_4321_; 
v___x_8772__boxed_4317_ = lean_unbox_uint64(v___x_4298_);
lean_dec_ref(v___x_4298_);
v_a_8773__boxed_4318_ = lean_unbox_uint64(v_a_4299_);
lean_dec_ref(v_a_4299_);
v_sz_boxed_4319_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4320_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_8772__boxed_4317_, v_a_8773__boxed_4318_, v_c_4300_, v_numDigits_4301_, v_as_4302_, v_sz_boxed_4319_, v_i_boxed_4320_, v_b_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v_as_4302_);
lean_dec_ref(v_c_4300_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v_numDigits_4349_; uint64_t v_anchor_4350_; lean_object* v_ordinal_4351_; lean_object* v___x_4352_; 
v_numDigits_4349_ = lean_ctor_get(v_info_4346_, 0);
v_anchor_4350_ = lean_ctor_get_uint64(v_info_4346_, sizeof(void*)*2);
v_ordinal_4351_ = lean_ctor_get(v_info_4346_, 1);
v___x_4352_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4349_, v_anchor_4350_, v_a_4347_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4389_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4389_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4389_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4357_ = lean_unsigned_to_nat(0u);
v___x_4358_ = lean_nat_dec_eq(v_ordinal_4351_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v_ref_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; 
v_ref_4359_ = lean_ctor_get(v_a_4347_, 5);
v___x_4360_ = l_Lean_SourceInfo_fromRef(v_ref_4359_, v___x_4358_);
v___x_4361_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4362_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4360_, 3);
v___x_4363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4360_);
lean_ctor_set(v___x_4363_, 1, v___x_4361_);
v___x_4364_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4365_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4360_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_unsigned_to_nat(1u);
v___x_4368_ = lean_nat_add(v_ordinal_4351_, v___x_4367_);
v___x_4369_ = l_Nat_reprFast(v___x_4368_);
v___x_4370_ = lean_box(2);
v___x_4371_ = l_Lean_Syntax_mkNumLit(v___x_4369_, v___x_4370_);
v___x_4372_ = l_Lean_Syntax_node3(v___x_4360_, v___x_4364_, v_a_4353_, v___x_4366_, v___x_4371_);
v___x_4373_ = l_Lean_Syntax_node2(v___x_4360_, v___x_4362_, v___x_4363_, v___x_4372_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4373_);
v___x_4375_ = v___x_4355_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
else
{
lean_object* v_ref_4377_; uint8_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v_ref_4377_ = lean_ctor_get(v_a_4347_, 5);
v___x_4378_ = 0;
v___x_4379_ = l_Lean_SourceInfo_fromRef(v_ref_4377_, v___x_4378_);
v___x_4380_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4381_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4379_, 2);
v___x_4382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4379_);
lean_ctor_set(v___x_4382_, 1, v___x_4380_);
v___x_4383_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4384_ = l_Lean_Syntax_node1(v___x_4379_, v___x_4383_, v_a_4353_);
v___x_4385_ = l_Lean_Syntax_node2(v___x_4379_, v___x_4381_, v___x_4382_, v___x_4384_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4385_);
v___x_4387_ = v___x_4355_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
else
{
return v___x_4352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4390_, v_a_4391_);
lean_dec_ref(v_a_4391_);
lean_dec_ref(v_info_4390_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4394_, v_a_4395_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec_ref(v_info_4399_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_p_4423_; lean_object* v___x_4426_; 
lean_inc_ref(v_proof_4416_);
v___x_4426_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4416_, v_a_4418_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4465_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4465_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4465_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4447_ = l_Lean_Expr_cleanupAnnotations(v_a_4427_);
v___x_4448_ = l_Lean_Expr_isApp(v___x_4447_);
if (v___x_4448_ == 0)
{
lean_dec_ref(v___x_4447_);
v___y_4432_ = v_a_4417_;
v___y_4433_ = v_a_4418_;
v___y_4434_ = v_a_4419_;
v___y_4435_ = v_a_4420_;
goto v___jp_4431_;
}
else
{
lean_object* v_arg_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; 
v_arg_4449_ = lean_ctor_get(v___x_4447_, 1);
lean_inc_ref(v_arg_4449_);
v___x_4450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4447_);
v___x_4451_ = l_Lean_Expr_isApp(v___x_4450_);
if (v___x_4451_ == 0)
{
lean_dec_ref(v___x_4450_);
lean_dec_ref(v_arg_4449_);
v___y_4432_ = v_a_4417_;
v___y_4433_ = v_a_4418_;
v___y_4434_ = v_a_4419_;
v___y_4435_ = v_a_4420_;
goto v___jp_4431_;
}
else
{
lean_object* v_arg_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v_arg_4452_ = lean_ctor_get(v___x_4450_, 1);
lean_inc_ref(v_arg_4452_);
v___x_4453_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4450_);
v___x_4454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4455_ = l_Lean_Expr_isConstOf(v___x_4453_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; uint8_t v___x_4457_; 
lean_dec_ref(v_arg_4452_);
v___x_4456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4457_ = l_Lean_Expr_isConstOf(v___x_4453_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; uint8_t v___x_4459_; 
v___x_4458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4459_ = l_Lean_Expr_isConstOf(v___x_4453_, v___x_4458_);
lean_dec_ref(v___x_4453_);
if (v___x_4459_ == 0)
{
lean_dec_ref(v_arg_4449_);
v___y_4432_ = v_a_4417_;
v___y_4433_ = v_a_4418_;
v___y_4434_ = v_a_4419_;
v___y_4435_ = v_a_4420_;
goto v___jp_4431_;
}
else
{
lean_del_object(v___x_4429_);
lean_dec_ref(v_proof_4416_);
v_p_4423_ = v_arg_4449_;
goto v___jp_4422_;
}
}
else
{
lean_dec_ref(v___x_4453_);
lean_del_object(v___x_4429_);
lean_dec_ref(v_proof_4416_);
v_p_4423_ = v_arg_4449_;
goto v___jp_4422_;
}
}
else
{
uint8_t v___x_4460_; 
lean_dec_ref(v___x_4453_);
lean_del_object(v___x_4429_);
lean_dec_ref(v_proof_4416_);
v___x_4460_ = l_Lean_Expr_isFalse(v_arg_4452_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_dec_ref(v_arg_4449_);
v___x_4461_ = lean_box(0);
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_arg_4449_);
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
}
}
v___jp_4431_:
{
if (lean_obj_tag(v_proof_4416_) == 6)
{
lean_object* v_body_4436_; uint8_t v___x_4437_; 
v_body_4436_ = lean_ctor_get(v_proof_4416_, 2);
lean_inc_ref(v_body_4436_);
lean_dec_ref_known(v_proof_4416_, 3);
v___x_4437_ = l_Lean_Expr_hasLooseBVars(v_body_4436_);
if (v___x_4437_ == 0)
{
lean_del_object(v___x_4429_);
v_proof_4416_ = v_body_4436_;
v_a_4417_ = v___y_4432_;
v_a_4418_ = v___y_4433_;
v_a_4419_ = v___y_4434_;
v_a_4420_ = v___y_4435_;
goto _start;
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4441_; 
lean_dec_ref(v_body_4436_);
v___x_4439_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4439_);
v___x_4441_ = v___x_4429_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
lean_dec_ref(v_proof_4416_);
v___x_4443_ = lean_box(0);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4443_);
v___x_4445_ = v___x_4429_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_dec_ref(v_proof_4416_);
v_a_4466_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4426_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4426_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
v___jp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4424_, 0, v_p_4423_);
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
return v___x_4425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v___x_4484_; uint8_t v___x_4485_; 
v___x_4484_ = l_Lean_Expr_hasMVar(v_e_4481_);
v___x_4485_ = lean_bool_not(v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v_mctx_4487_; lean_object* v___x_4488_; lean_object* v_fst_4489_; lean_object* v_snd_4490_; lean_object* v___x_4491_; lean_object* v_cache_4492_; lean_object* v_zetaDeltaFVarIds_4493_; lean_object* v_postponed_4494_; lean_object* v_diag_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4504_; 
v___x_4486_ = lean_st_ref_get(v___y_4482_);
v_mctx_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc_ref(v_mctx_4487_);
lean_dec(v___x_4486_);
v___x_4488_ = l_Lean_instantiateMVarsCore(v_mctx_4487_, v_e_4481_);
v_fst_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_fst_4489_);
v_snd_4490_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_snd_4490_);
lean_dec_ref(v___x_4488_);
v___x_4491_ = lean_st_ref_take(v___y_4482_);
v_cache_4492_ = lean_ctor_get(v___x_4491_, 1);
v_zetaDeltaFVarIds_4493_ = lean_ctor_get(v___x_4491_, 2);
v_postponed_4494_ = lean_ctor_get(v___x_4491_, 3);
v_diag_4495_ = lean_ctor_get(v___x_4491_, 4);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v___x_4491_, 0);
lean_dec(v_unused_4505_);
v___x_4497_ = v___x_4491_;
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_diag_4495_);
lean_inc(v_postponed_4494_);
lean_inc(v_zetaDeltaFVarIds_4493_);
lean_inc(v_cache_4492_);
lean_dec(v___x_4491_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v_snd_4490_);
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_snd_4490_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v_cache_4492_);
lean_ctor_set(v_reuseFailAlloc_4503_, 2, v_zetaDeltaFVarIds_4493_);
lean_ctor_set(v_reuseFailAlloc_4503_, 3, v_postponed_4494_);
lean_ctor_set(v_reuseFailAlloc_4503_, 4, v_diag_4495_);
v___x_4500_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4501_ = lean_st_ref_set(v___y_4482_, v___x_4500_);
v___x_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4502_, 0, v_fst_4489_);
return v___x_4502_;
}
}
}
else
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v_e_4481_);
return v___x_4506_;
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
if (v___x_4642_ == 0)
{
lean_dec(v_tail_4640_);
return v___x_4642_;
}
else
{
v_x_4637_ = v_tail_4640_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v___x_4652_ = lean_unsigned_to_nat(3u);
v___x_4653_ = l_Lean_Syntax_getArg(v_head_4639_, v___x_4652_);
lean_dec(v_head_4639_);
v___x_4654_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4655_ = l_Lean_Syntax_isOfKind(v___x_4653_, v___x_4654_);
if (v___x_4655_ == 0)
{
v_x_4637_ = v_tail_4640_;
goto _start;
}
else
{
uint8_t v___x_4657_; 
lean_dec(v_tail_4640_);
v___x_4657_ = 0;
return v___x_4657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4658_){
_start:
{
uint8_t v_res_4659_; lean_object* v_r_4660_; 
v_res_4659_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4658_);
v_r_4660_ = lean_box(v_res_4659_);
return v_r_4660_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4661_){
_start:
{
uint8_t v___x_4662_; 
v___x_4662_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4663_){
_start:
{
uint8_t v_res_4664_; lean_object* v_r_4665_; 
v_res_4664_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4663_);
v_r_4665_ = lean_box(v_res_4664_);
return v_r_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4681_, lean_object* v_a_4682_){
_start:
{
if (lean_obj_tag(v_seq_4681_) == 0)
{
lean_object* v_ref_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v_ref_4684_ = lean_ctor_get(v_a_4682_, 5);
v___x_4685_ = 0;
v___x_4686_ = l_Lean_SourceInfo_fromRef(v_ref_4684_, v___x_4685_);
v___x_4687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4686_);
v___x_4689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4686_);
lean_ctor_set(v___x_4689_, 1, v___x_4687_);
v___x_4690_ = l_Lean_Syntax_node1(v___x_4686_, v___x_4688_, v___x_4689_);
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
return v___x_4691_;
}
else
{
lean_object* v_tail_4692_; 
v_tail_4692_ = lean_ctor_get(v_seq_4681_, 1);
if (lean_obj_tag(v_tail_4692_) == 0)
{
lean_object* v_head_4693_; lean_object* v___x_4694_; 
v_head_4693_ = lean_ctor_get(v_seq_4681_, 0);
lean_inc(v_head_4693_);
lean_dec_ref_known(v_seq_4681_, 2);
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_head_4693_);
return v___x_4694_;
}
else
{
lean_object* v_head_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4717_; 
lean_inc(v_tail_4692_);
v_head_4695_ = lean_ctor_get(v_seq_4681_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_seq_4681_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v_seq_4681_, 1);
lean_dec(v_unused_4718_);
v___x_4697_ = v_seq_4681_;
v_isShared_4698_ = v_isSharedCheck_4717_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_head_4695_);
lean_dec(v_seq_4681_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4717_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4716_; 
v___x_4699_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4692_, v_a_4682_);
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4716_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4716_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v_ref_4704_; uint8_t v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
v_ref_4704_ = lean_ctor_get(v_a_4682_, 5);
v___x_4705_ = 0;
v___x_4706_ = l_Lean_SourceInfo_fromRef(v_ref_4704_, v___x_4705_);
v___x_4707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4706_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set_tag(v___x_4697_, 2);
lean_ctor_set(v___x_4697_, 1, v___x_4708_);
lean_ctor_set(v___x_4697_, 0, v___x_4706_);
v___x_4710_ = v___x_4697_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4715_, 1, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4713_; 
v___x_4711_ = l_Lean_Syntax_node3(v___x_4706_, v___x_4707_, v_head_4695_, v___x_4710_, v_a_4700_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4711_);
v___x_4713_ = v___x_4702_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4711_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4719_, v_a_4720_);
lean_dec_ref(v_a_4720_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4723_, v_a_4724_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4728_, v_a_4729_, v_a_4730_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4733_, lean_object* v_seq_4734_, lean_object* v_a_4735_){
_start:
{
if (lean_obj_tag(v_seq_4734_) == 0)
{
lean_object* v___x_4737_; 
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v_cases_4733_);
return v___x_4737_;
}
else
{
lean_object* v___x_4738_; lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4753_; 
v___x_4738_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4734_, v_a_4735_);
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4741_ = v___x_4738_;
v_isShared_4742_ = v_isSharedCheck_4753_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4738_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4753_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v_ref_4743_; uint8_t v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4751_; 
v_ref_4743_ = lean_ctor_get(v_a_4735_, 5);
v___x_4744_ = 0;
v___x_4745_ = l_Lean_SourceInfo_fromRef(v_ref_4743_, v___x_4744_);
v___x_4746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4745_);
v___x_4748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4745_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = l_Lean_Syntax_node3(v___x_4745_, v___x_4746_, v_cases_4733_, v___x_4748_, v_a_4739_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 0, v___x_4749_);
v___x_4751_ = v___x_4741_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4754_, lean_object* v_seq_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4754_, v_seq_4755_, v_a_4756_);
lean_dec_ref(v_a_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4759_, lean_object* v_seq_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4759_, v_seq_4760_, v_a_4761_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4765_, lean_object* v_seq_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4765_, v_seq_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4770_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4771_, lean_object* v_x_4772_){
_start:
{
if (lean_obj_tag(v_x_4771_) == 0)
{
if (lean_obj_tag(v_x_4772_) == 0)
{
uint8_t v___x_4773_; 
v___x_4773_ = 1;
return v___x_4773_;
}
else
{
uint8_t v___x_4774_; 
lean_dec_ref_known(v_x_4772_, 2);
v___x_4774_ = 0;
return v___x_4774_;
}
}
else
{
if (lean_obj_tag(v_x_4772_) == 0)
{
uint8_t v___x_4775_; 
lean_dec_ref_known(v_x_4771_, 2);
v___x_4775_ = 0;
return v___x_4775_;
}
else
{
lean_object* v_head_4776_; lean_object* v_tail_4777_; lean_object* v_head_4778_; lean_object* v_tail_4779_; uint8_t v___x_4780_; 
v_head_4776_ = lean_ctor_get(v_x_4771_, 0);
lean_inc(v_head_4776_);
v_tail_4777_ = lean_ctor_get(v_x_4771_, 1);
lean_inc(v_tail_4777_);
lean_dec_ref_known(v_x_4771_, 2);
v_head_4778_ = lean_ctor_get(v_x_4772_, 0);
lean_inc(v_head_4778_);
v_tail_4779_ = lean_ctor_get(v_x_4772_, 1);
lean_inc(v_tail_4779_);
lean_dec_ref_known(v_x_4772_, 2);
v___x_4780_ = l_Lean_Syntax_structEq(v_head_4776_, v_head_4778_);
if (v___x_4780_ == 0)
{
lean_dec(v_tail_4779_);
lean_dec(v_tail_4777_);
return v___x_4780_;
}
else
{
v_x_4771_ = v_tail_4777_;
v_x_4772_ = v_tail_4779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4782_, lean_object* v_x_4783_){
_start:
{
uint8_t v_res_4784_; lean_object* v_r_4785_; 
v_res_4784_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4782_, v_x_4783_);
v_r_4785_ = lean_box(v_res_4784_);
return v_r_4785_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4786_, lean_object* v_as_4787_, size_t v_i_4788_, size_t v_stop_4789_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_eq(v_i_4788_, v_stop_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; uint8_t v___x_4792_; uint8_t v___x_4793_; 
v___x_4791_ = lean_array_uget_borrowed(v_as_4787_, v_i_4788_);
lean_inc(v_alt_4786_);
lean_inc(v___x_4791_);
v___x_4792_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4791_, v_alt_4786_);
v___x_4793_ = lean_bool_not(v___x_4792_);
if (v___x_4793_ == 0)
{
size_t v___x_4794_; size_t v___x_4795_; 
v___x_4794_ = ((size_t)1ULL);
v___x_4795_ = lean_usize_add(v_i_4788_, v___x_4794_);
v_i_4788_ = v___x_4795_;
goto _start;
}
else
{
lean_dec(v_alt_4786_);
return v___x_4793_;
}
}
else
{
uint8_t v___x_4797_; 
lean_dec(v_alt_4786_);
v___x_4797_ = 0;
return v___x_4797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4798_, lean_object* v_as_4799_, lean_object* v_i_4800_, lean_object* v_stop_4801_){
_start:
{
size_t v_i_boxed_4802_; size_t v_stop_boxed_4803_; uint8_t v_res_4804_; lean_object* v_r_4805_; 
v_i_boxed_4802_ = lean_unbox_usize(v_i_4800_);
lean_dec(v_i_4800_);
v_stop_boxed_4803_ = lean_unbox_usize(v_stop_4801_);
lean_dec(v_stop_4801_);
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4798_, v_as_4799_, v_i_boxed_4802_, v_stop_boxed_4803_);
lean_dec_ref(v_as_4799_);
v_r_4805_ = lean_box(v_res_4804_);
return v_r_4805_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4806_){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; 
v___x_4807_ = lean_unsigned_to_nat(0u);
v___x_4808_ = lean_array_get_size(v_alts_4806_);
v___x_4809_ = lean_nat_dec_lt(v___x_4807_, v___x_4808_);
if (v___x_4809_ == 0)
{
uint8_t v___x_4810_; 
v___x_4810_ = 1;
return v___x_4810_;
}
else
{
lean_object* v_alt_4811_; uint8_t v___x_4812_; 
v_alt_4811_ = lean_array_fget_borrowed(v_alts_4806_, v___x_4807_);
lean_inc(v_alt_4811_);
v___x_4812_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4811_);
if (v___x_4812_ == 0)
{
return v___x_4812_;
}
else
{
if (v___x_4809_ == 0)
{
uint8_t v___x_4813_; 
v___x_4813_ = lean_bool_not(v___x_4809_);
return v___x_4813_;
}
else
{
if (v___x_4809_ == 0)
{
uint8_t v___x_4814_; 
v___x_4814_ = lean_bool_not(v___x_4809_);
return v___x_4814_;
}
else
{
size_t v___x_4815_; size_t v___x_4816_; uint8_t v___x_4817_; uint8_t v___x_4818_; 
v___x_4815_ = ((size_t)0ULL);
v___x_4816_ = lean_usize_of_nat(v___x_4808_);
lean_inc(v_alt_4811_);
v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4811_, v_alts_4806_, v___x_4815_, v___x_4816_);
v___x_4818_ = lean_bool_not(v___x_4817_);
return v___x_4818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4819_){
_start:
{
uint8_t v_res_4820_; lean_object* v_r_4821_; 
v_res_4820_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4819_);
lean_dec_ref(v_alts_4819_);
v_r_4821_ = lean_box(v_res_4820_);
return v_r_4821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4829_){
_start:
{
if (lean_obj_tag(v_alt_4829_) == 1)
{
lean_object* v_tail_4830_; 
v_tail_4830_ = lean_ctor_get(v_alt_4829_, 1);
if (lean_obj_tag(v_tail_4830_) == 0)
{
lean_object* v_head_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v_head_4831_ = lean_ctor_get(v_alt_4829_, 0);
lean_inc(v_head_4831_);
lean_dec_ref_known(v_alt_4829_, 2);
v___x_4832_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4833_ = l_Lean_Syntax_isOfKind(v_head_4831_, v___x_4832_);
return v___x_4833_;
}
else
{
uint8_t v___x_4834_; 
lean_dec_ref_known(v_alt_4829_, 2);
v___x_4834_ = 0;
return v___x_4834_;
}
}
else
{
uint8_t v___x_4835_; 
lean_dec(v_alt_4829_);
v___x_4835_ = 0;
return v___x_4835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4836_){
_start:
{
uint8_t v_res_4837_; lean_object* v_r_4838_; 
v_res_4837_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4836_);
v_r_4838_ = lean_box(v_res_4837_);
return v_r_4838_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4839_, lean_object* v_x_4840_, lean_object* v___y_4841_){
_start:
{
if (lean_obj_tag(v_x_4839_) == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = l_List_reverse___redArg(v_x_4840_);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
else
{
lean_object* v_head_4845_; lean_object* v_tail_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4864_; 
v_head_4845_ = lean_ctor_get(v_x_4839_, 0);
v_tail_4846_ = lean_ctor_get(v_x_4839_, 1);
v_isSharedCheck_4864_ = !lean_is_exclusive(v_x_4839_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4848_ = v_x_4839_;
v_isShared_4849_ = v_isSharedCheck_4864_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_tail_4846_);
lean_inc(v_head_4845_);
lean_dec(v_x_4839_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4864_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4845_, v___y_4841_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 1, v_x_4840_);
lean_ctor_set(v___x_4848_, 0, v_a_4851_);
v___x_4853_ = v___x_4848_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4851_);
lean_ctor_set(v_reuseFailAlloc_4855_, 1, v_x_4840_);
v___x_4853_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
v_x_4839_ = v_tail_4846_;
v_x_4840_ = v___x_4853_;
goto _start;
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_del_object(v___x_4848_);
lean_dec(v_tail_4846_);
lean_dec(v_x_4840_);
v_a_4856_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4850_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4850_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4865_, lean_object* v_x_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4865_, v_x_4866_, v___y_4867_);
lean_dec_ref(v___y_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4870_, lean_object* v_alts_4871_, uint8_t v_compress_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v_seq_4877_; 
if (v_compress_4872_ == 0)
{
goto v___jp_4880_;
}
else
{
uint8_t v___x_4890_; 
v___x_4890_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4871_);
if (v___x_4890_ == 0)
{
goto v___jp_4880_;
}
else
{
lean_object* v___x_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = lean_array_get_size(v_alts_4871_);
v___x_4893_ = lean_nat_dec_lt(v___x_4891_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
lean_dec_ref(v_alts_4871_);
v___x_4894_ = lean_box(0);
v___x_4895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4895_, 0, v_cases_4870_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
else
{
lean_object* v___x_4897_; lean_object* v_firstAlt_4898_; uint8_t v___x_4899_; 
v___x_4897_ = lean_box(0);
v_firstAlt_4898_ = lean_array_get(v___x_4897_, v_alts_4871_, v___x_4891_);
lean_dec_ref(v_alts_4871_);
lean_inc(v_firstAlt_4898_);
v___x_4899_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4909_; 
v___x_4900_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4870_, v_firstAlt_4898_, v_a_4873_);
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4903_ = v___x_4900_;
v_isShared_4904_ = v_isSharedCheck_4909_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4900_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4909_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4905_, 0, v_a_4901_);
lean_ctor_set(v___x_4905_, 1, v___x_4897_);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 0, v___x_4905_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
else
{
lean_object* v___x_4910_; 
lean_dec(v_cases_4870_);
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_firstAlt_4898_);
return v___x_4910_;
}
}
}
}
v___jp_4876_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4878_, 0, v_cases_4870_);
lean_ctor_set(v___x_4878_, 1, v_seq_4877_);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
v___jp_4880_:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4881_ = lean_array_get_size(v_alts_4871_);
v___x_4882_ = lean_unsigned_to_nat(1u);
v___x_4883_ = lean_nat_dec_eq(v___x_4881_, v___x_4882_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4884_ = lean_array_to_list(v_alts_4871_);
v___x_4885_ = lean_box(0);
v___x_4886_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4884_, v___x_4885_, v_a_4873_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
v_seq_4877_ = v_a_4887_;
goto v___jp_4876_;
}
else
{
lean_dec(v_cases_4870_);
return v___x_4886_;
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = lean_array_fget(v_alts_4871_, v___x_4888_);
lean_dec_ref(v_alts_4871_);
v_seq_4877_ = v___x_4889_;
goto v___jp_4876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4911_, lean_object* v_alts_4912_, lean_object* v_compress_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
uint8_t v_compress_boxed_4917_; lean_object* v_res_4918_; 
v_compress_boxed_4917_ = lean_unbox(v_compress_4913_);
v_res_4918_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4911_, v_alts_4912_, v_compress_boxed_4917_, v_a_4914_, v_a_4915_);
lean_dec(v_a_4915_);
lean_dec_ref(v_a_4914_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4919_, lean_object* v_x_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4919_, v_x_4920_, v___y_4921_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4925_, lean_object* v_x_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4925_, v_x_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v___x_4934_; lean_object* v_env_4935_; uint8_t v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4934_ = lean_st_ref_get(v___y_4932_);
v_env_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc_ref(v_env_4935_);
lean_dec(v___x_4934_);
v___x_4936_ = l_Lean_Meta_isMatcherAppCore(v_env_4935_, v_e_4931_);
v___x_4937_ = lean_box(v___x_4936_);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4939_, v___y_4940_);
lean_dec(v___y_4940_);
lean_dec_ref(v_e_4939_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4943_, v___y_4953_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v_e_4956_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; 
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
lean_inc(v___y_4972_);
lean_inc_ref(v___y_4971_);
lean_inc(v___y_4970_);
v___x_4980_ = lean_apply_10(v_x_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, lean_box(0));
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4993_, lean_object* v_x_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v___f_5005_; lean_object* v___x_5006_; 
lean_inc(v___y_4999_);
lean_inc_ref(v___y_4998_);
lean_inc(v___y_4997_);
lean_inc_ref(v___y_4996_);
lean_inc(v___y_4995_);
v___f_5005_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5005_, 0, v_x_4994_);
lean_closure_set(v___f_5005_, 1, v___y_4995_);
lean_closure_set(v___f_5005_, 2, v___y_4996_);
lean_closure_set(v___f_5005_, 3, v___y_4997_);
lean_closure_set(v___f_5005_, 4, v___y_4998_);
lean_closure_set(v___f_5005_, 5, v___y_4999_);
v___x_5006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4993_, v___f_5005_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5006_) == 0)
{
return v___x_5006_;
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_5006_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_5006_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5015_, lean_object* v_x_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5015_, v_x_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5028_, lean_object* v_mvarId_5029_, lean_object* v_x_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
lean_object* v___x_5041_; 
v___x_5041_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5029_, v_x_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5042_, lean_object* v_mvarId_5043_, lean_object* v_x_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5042_, v_mvarId_5043_, v_x_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5056_, lean_object* v___y_5057_){
_start:
{
uint8_t v___x_5059_; uint8_t v___x_5060_; 
v___x_5059_ = l_Lean_Expr_hasMVar(v_e_5056_);
v___x_5060_ = lean_bool_not(v___x_5059_);
if (v___x_5060_ == 0)
{
lean_object* v___x_5061_; lean_object* v_mctx_5062_; lean_object* v___x_5063_; lean_object* v_fst_5064_; lean_object* v_snd_5065_; lean_object* v___x_5066_; lean_object* v_cache_5067_; lean_object* v_zetaDeltaFVarIds_5068_; lean_object* v_postponed_5069_; lean_object* v_diag_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5079_; 
v___x_5061_ = lean_st_ref_get(v___y_5057_);
v_mctx_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc_ref(v_mctx_5062_);
lean_dec(v___x_5061_);
v___x_5063_ = l_Lean_instantiateMVarsCore(v_mctx_5062_, v_e_5056_);
v_fst_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_fst_5064_);
v_snd_5065_ = lean_ctor_get(v___x_5063_, 1);
lean_inc(v_snd_5065_);
lean_dec_ref(v___x_5063_);
v___x_5066_ = lean_st_ref_take(v___y_5057_);
v_cache_5067_ = lean_ctor_get(v___x_5066_, 1);
v_zetaDeltaFVarIds_5068_ = lean_ctor_get(v___x_5066_, 2);
v_postponed_5069_ = lean_ctor_get(v___x_5066_, 3);
v_diag_5070_ = lean_ctor_get(v___x_5066_, 4);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5079_ == 0)
{
lean_object* v_unused_5080_; 
v_unused_5080_ = lean_ctor_get(v___x_5066_, 0);
lean_dec(v_unused_5080_);
v___x_5072_ = v___x_5066_;
v_isShared_5073_ = v_isSharedCheck_5079_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_diag_5070_);
lean_inc(v_postponed_5069_);
lean_inc(v_zetaDeltaFVarIds_5068_);
lean_inc(v_cache_5067_);
lean_dec(v___x_5066_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5079_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 0, v_snd_5065_);
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_snd_5065_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v_cache_5067_);
lean_ctor_set(v_reuseFailAlloc_5078_, 2, v_zetaDeltaFVarIds_5068_);
lean_ctor_set(v_reuseFailAlloc_5078_, 3, v_postponed_5069_);
lean_ctor_set(v_reuseFailAlloc_5078_, 4, v_diag_5070_);
v___x_5075_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = lean_st_ref_set(v___y_5057_, v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v_fst_5064_);
return v___x_5077_;
}
}
}
else
{
lean_object* v___x_5081_; 
v___x_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5081_, 0, v_e_5056_);
return v___x_5081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5082_, v___y_5083_);
lean_dec(v___y_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5086_, v___y_5093_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
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
lean_object* v_mvarIds_5131_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___x_5191_; 
v___x_5191_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5113_, v___y_5119_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v___y_5194_; lean_object* v___x_5245_; uint8_t v___y_5247_; uint8_t v___x_5249_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
lean_inc(v_a_5192_);
lean_dec_ref_known(v___x_5191_, 1);
v___x_5245_ = lean_unsigned_to_nat(1u);
v___x_5249_ = lean_nat_dec_lt(v___x_5245_, v_numCases_5116_);
if (v___x_5249_ == 0)
{
v___y_5247_ = v_isRec_5117_;
goto v___jp_5246_;
}
else
{
v___y_5247_ = v___x_5249_;
goto v___jp_5246_;
}
v___jp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5195_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5114_);
lean_inc_ref(v___x_5113_);
v___x_5196_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5113_, v___y_5194_, v_numCases_5116_, v___x_5195_, v___y_5122_, v___y_5125_, v___y_5127_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v___x_5197_; 
lean_dec_ref_known(v___x_5196_, 1);
lean_inc_ref(v___x_5113_);
v___x_5197_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5113_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_options_5198_; uint8_t v_hasTrace_5199_; 
lean_dec_ref_known(v___x_5197_, 1);
v_options_5198_ = lean_ctor_get(v___y_5127_, 2);
v_hasTrace_5199_ = lean_ctor_get_uint8(v_options_5198_, sizeof(void*)*1);
if (v_hasTrace_5199_ == 0)
{
lean_dec(v_a_5192_);
v___y_5135_ = v___y_5119_;
v___y_5136_ = v___y_5120_;
v___y_5137_ = v___y_5121_;
v___y_5138_ = v___y_5122_;
v___y_5139_ = v___y_5123_;
v___y_5140_ = v___y_5124_;
v___y_5141_ = v___y_5125_;
v___y_5142_ = v___y_5126_;
v___y_5143_ = v___y_5127_;
v___y_5144_ = v___y_5128_;
goto v___jp_5134_;
}
else
{
lean_object* v_inheritedTraceOptions_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; 
v_inheritedTraceOptions_5200_ = lean_ctor_get(v___y_5127_, 13);
v___x_5201_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5202_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5203_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5200_, v_options_5198_, v___x_5202_);
if (v___x_5203_ == 0)
{
lean_dec(v_a_5192_);
v___y_5135_ = v___y_5119_;
v___y_5136_ = v___y_5120_;
v___y_5137_ = v___y_5121_;
v___y_5138_ = v___y_5122_;
v___y_5139_ = v___y_5123_;
v___y_5140_ = v___y_5124_;
v___y_5141_ = v___y_5125_;
v___y_5142_ = v___y_5126_;
v___y_5143_ = v___y_5127_;
v___y_5144_ = v___y_5128_;
goto v___jp_5134_;
}
else
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Lean_Meta_Grind_updateLastTag(v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
lean_dec_ref_known(v___x_5204_, 1);
lean_inc_ref(v___x_5113_);
v___x_5205_ = l_Lean_MessageData_ofExpr(v___x_5113_);
v___x_5206_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5205_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = l_Nat_reprFast(v_a_5192_);
v___x_5209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5208_);
v___x_5210_ = l_Lean_MessageData_ofFormat(v___x_5209_);
v___x_5211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5207_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5201_, v___x_5211_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_dec_ref_known(v___x_5212_, 1);
v___y_5135_ = v___y_5119_;
v___y_5136_ = v___y_5120_;
v___y_5137_ = v___y_5121_;
v___y_5138_ = v___y_5122_;
v___y_5139_ = v___y_5123_;
v___y_5140_ = v___y_5124_;
v___y_5141_ = v___y_5125_;
v___y_5142_ = v___y_5126_;
v___y_5143_ = v___y_5127_;
v___y_5144_ = v___y_5128_;
goto v___jp_5134_;
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5221_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5204_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5204_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5236_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5229_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5197_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5197_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5234_; 
if (v_isShared_5232_ == 0)
{
v___x_5234_ = v___x_5231_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5237_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5196_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5196_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
v___jp_5246_:
{
if (v___y_5247_ == 0)
{
lean_inc(v_a_5192_);
v___y_5194_ = v_a_5192_;
goto v___jp_5193_;
}
else
{
lean_object* v___x_5248_; 
v___x_5248_ = lean_nat_add(v_a_5192_, v___x_5245_);
v___y_5194_ = v___x_5248_;
goto v___jp_5193_;
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_numCases_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_c_5114_);
lean_dec_ref(v___x_5113_);
v_a_5250_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5191_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5191_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
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
lean_object* v___x_5145_; 
v___x_5145_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5113_, v___y_5144_);
if (lean_obj_tag(v_c_5114_) == 1)
{
lean_object* v_e_5146_; lean_object* v_binderType_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
lean_dec_ref(v___x_5145_);
lean_dec_ref(v___x_5113_);
v_e_5146_ = lean_ctor_get(v_c_5114_, 0);
lean_inc_ref(v_e_5146_);
lean_dec_ref_known(v_c_5114_, 2);
v_binderType_5147_ = lean_ctor_get(v_e_5146_, 1);
lean_inc_ref(v_binderType_5147_);
lean_dec_ref(v_e_5146_);
v___x_5148_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5147_);
v___x_5149_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5115_, v___x_5148_, v___y_5137_, v___y_5138_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v_mvarIds_5131_ = v_a_5150_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5151_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5149_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5149_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v_a_5159_; uint8_t v___x_5160_; 
lean_dec_ref(v_c_5114_);
v_a_5159_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5145_);
v___x_5160_ = lean_unbox(v_a_5159_);
lean_dec(v_a_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; 
v___x_5161_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5113_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v___x_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5163_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5115_, v_a_5162_, v___y_5137_, v___y_5138_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc(v_a_5164_);
lean_dec_ref_known(v___x_5163_, 1);
v_mvarIds_5131_ = v_a_5164_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5165_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5163_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5163_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec(v_anchorInfo_x3f_5118_);
lean_dec(v_a_5115_);
v_a_5173_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5161_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5161_);
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
else
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Lean_Meta_Grind_casesMatch(v_a_5115_, v___x_5113_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5181_, 1);
v_mvarIds_5131_ = v_a_5182_;
goto v___jp_5130_;
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v_anchorInfo_x3f_5118_);
v_a_5183_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5181_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5181_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5258_ = _args[0];
lean_object* v_c_5259_ = _args[1];
lean_object* v_a_5260_ = _args[2];
lean_object* v_numCases_5261_ = _args[3];
lean_object* v_isRec_5262_ = _args[4];
lean_object* v_anchorInfo_x3f_5263_ = _args[5];
lean_object* v___y_5264_ = _args[6];
lean_object* v___y_5265_ = _args[7];
lean_object* v___y_5266_ = _args[8];
lean_object* v___y_5267_ = _args[9];
lean_object* v___y_5268_ = _args[10];
lean_object* v___y_5269_ = _args[11];
lean_object* v___y_5270_ = _args[12];
lean_object* v___y_5271_ = _args[13];
lean_object* v___y_5272_ = _args[14];
lean_object* v___y_5273_ = _args[15];
lean_object* v___y_5274_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5275_; lean_object* v_res_5276_; 
v_isRec_boxed_5275_ = lean_unbox(v_isRec_5262_);
v_res_5276_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5258_, v_c_5259_, v_a_5260_, v_numCases_5261_, v_isRec_boxed_5275_, v_anchorInfo_x3f_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec(v___y_5264_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5277_, uint8_t v_trace_5278_, lean_object* v___f_5279_, lean_object* v_c_5280_, lean_object* v_candidates_x3f_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v___x_5292_; lean_object* v___y_5294_; 
v___x_5292_ = lean_st_mk_ref(v_goal_5277_);
if (v_trace_5278_ == 0)
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
lean_dec(v_candidates_x3f_5281_);
v___x_5313_ = lean_box(0);
lean_inc(v___x_5292_);
v___x_5314_ = lean_apply_12(v___f_5279_, v___x_5313_, v___x_5292_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, lean_box(0));
v___y_5294_ = v___x_5314_;
goto v___jp_5293_;
}
else
{
lean_object* v___x_5315_; 
v___x_5315_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5280_, v_candidates_x3f_5281_, v___x_5292_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref_known(v___x_5315_, 1);
v___x_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5317_, 0, v_a_5316_);
lean_inc(v___x_5292_);
v___x_5318_ = lean_apply_12(v___f_5279_, v___x_5317_, v___x_5292_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, lean_box(0));
v___y_5294_ = v___x_5318_;
goto v___jp_5293_;
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
lean_dec(v___x_5292_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___f_5279_);
v_a_5319_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5315_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5315_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
v___jp_5293_:
{
if (lean_obj_tag(v___y_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5304_; 
v_a_5295_ = lean_ctor_get(v___y_5294_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___y_5294_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5297_ = v___y_5294_;
v_isShared_5298_ = v_isSharedCheck_5304_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___y_5294_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5304_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5302_; 
v___x_5299_ = lean_st_ref_get(v___x_5292_);
lean_dec(v___x_5292_);
v___x_5300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5300_, 0, v_a_5295_);
lean_ctor_set(v___x_5300_, 1, v___x_5299_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5300_);
v___x_5302_ = v___x_5297_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5300_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec(v___x_5292_);
v_a_5305_ = lean_ctor_get(v___y_5294_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___y_5294_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___y_5294_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___y_5294_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5327_, lean_object* v_trace_5328_, lean_object* v___f_5329_, lean_object* v_c_5330_, lean_object* v_candidates_x3f_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
uint8_t v_trace_boxed_5342_; lean_object* v_res_5343_; 
v_trace_boxed_5342_ = lean_unbox(v_trace_5328_);
v_res_5343_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5327_, v_trace_boxed_5342_, v___f_5329_, v_c_5330_, v_candidates_x3f_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec_ref(v_c_5330_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5344_, lean_object* v_x_5345_, lean_object* v_x_5346_, lean_object* v_x_5347_){
_start:
{
lean_object* v_ks_5348_; lean_object* v_vs_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5373_; 
v_ks_5348_ = lean_ctor_get(v_x_5344_, 0);
v_vs_5349_ = lean_ctor_get(v_x_5344_, 1);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_x_5344_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5351_ = v_x_5344_;
v_isShared_5352_ = v_isSharedCheck_5373_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_vs_5349_);
lean_inc(v_ks_5348_);
lean_dec(v_x_5344_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5373_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5353_ = lean_array_get_size(v_ks_5348_);
v___x_5354_ = lean_nat_dec_lt(v_x_5345_, v___x_5353_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5358_; 
lean_dec(v_x_5345_);
v___x_5355_ = lean_array_push(v_ks_5348_, v_x_5346_);
v___x_5356_ = lean_array_push(v_vs_5349_, v_x_5347_);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 1, v___x_5356_);
lean_ctor_set(v___x_5351_, 0, v___x_5355_);
v___x_5358_ = v___x_5351_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5359_, 1, v___x_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
else
{
lean_object* v_k_x27_5360_; uint8_t v___x_5361_; 
v_k_x27_5360_ = lean_array_fget_borrowed(v_ks_5348_, v_x_5345_);
v___x_5361_ = l_Lean_instBEqMVarId_beq(v_x_5346_, v_k_x27_5360_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5363_; 
if (v_isShared_5352_ == 0)
{
v___x_5363_ = v___x_5351_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_ks_5348_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_vs_5349_);
v___x_5363_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5364_ = lean_unsigned_to_nat(1u);
v___x_5365_ = lean_nat_add(v_x_5345_, v___x_5364_);
lean_dec(v_x_5345_);
v_x_5344_ = v___x_5363_;
v_x_5345_ = v___x_5365_;
goto _start;
}
}
else
{
lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5371_; 
v___x_5368_ = lean_array_fset(v_ks_5348_, v_x_5345_, v_x_5346_);
v___x_5369_ = lean_array_fset(v_vs_5349_, v_x_5345_, v_x_5347_);
lean_dec(v_x_5345_);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 1, v___x_5369_);
lean_ctor_set(v___x_5351_, 0, v___x_5368_);
v___x_5371_ = v___x_5351_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5368_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v___x_5369_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5374_, lean_object* v_k_5375_, lean_object* v_v_5376_){
_start:
{
lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5377_ = lean_unsigned_to_nat(0u);
v___x_5378_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5374_, v___x_5377_, v_k_5375_, v_v_5376_);
return v___x_5378_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5380_, size_t v_x_5381_, size_t v_x_5382_, lean_object* v_x_5383_, lean_object* v_x_5384_){
_start:
{
if (lean_obj_tag(v_x_5380_) == 0)
{
lean_object* v_es_5385_; size_t v___x_5386_; size_t v___x_5387_; lean_object* v_j_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; 
v_es_5385_ = lean_ctor_get(v_x_5380_, 0);
v___x_5386_ = ((size_t)31ULL);
v___x_5387_ = lean_usize_land(v_x_5381_, v___x_5386_);
v_j_5388_ = lean_usize_to_nat(v___x_5387_);
v___x_5389_ = lean_array_get_size(v_es_5385_);
v___x_5390_ = lean_nat_dec_lt(v_j_5388_, v___x_5389_);
if (v___x_5390_ == 0)
{
lean_dec(v_j_5388_);
lean_dec(v_x_5384_);
lean_dec(v_x_5383_);
return v_x_5380_;
}
else
{
lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5429_; 
lean_inc_ref(v_es_5385_);
v_isSharedCheck_5429_ = !lean_is_exclusive(v_x_5380_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; 
v_unused_5430_ = lean_ctor_get(v_x_5380_, 0);
lean_dec(v_unused_5430_);
v___x_5392_ = v_x_5380_;
v_isShared_5393_ = v_isSharedCheck_5429_;
goto v_resetjp_5391_;
}
else
{
lean_dec(v_x_5380_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5429_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v_v_5394_; lean_object* v___x_5395_; lean_object* v_xs_x27_5396_; lean_object* v___y_5398_; 
v_v_5394_ = lean_array_fget(v_es_5385_, v_j_5388_);
v___x_5395_ = lean_box(0);
v_xs_x27_5396_ = lean_array_fset(v_es_5385_, v_j_5388_, v___x_5395_);
switch(lean_obj_tag(v_v_5394_))
{
case 0:
{
lean_object* v_key_5403_; lean_object* v_val_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5414_; 
v_key_5403_ = lean_ctor_get(v_v_5394_, 0);
v_val_5404_ = lean_ctor_get(v_v_5394_, 1);
v_isSharedCheck_5414_ = !lean_is_exclusive(v_v_5394_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5406_ = v_v_5394_;
v_isShared_5407_ = v_isSharedCheck_5414_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_val_5404_);
lean_inc(v_key_5403_);
lean_dec(v_v_5394_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5414_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
uint8_t v___x_5408_; 
v___x_5408_ = l_Lean_instBEqMVarId_beq(v_x_5383_, v_key_5403_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_del_object(v___x_5406_);
v___x_5409_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5403_, v_val_5404_, v_x_5383_, v_x_5384_);
v___x_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5409_);
v___y_5398_ = v___x_5410_;
goto v___jp_5397_;
}
else
{
lean_object* v___x_5412_; 
lean_dec(v_val_5404_);
lean_dec(v_key_5403_);
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v_x_5384_);
lean_ctor_set(v___x_5406_, 0, v_x_5383_);
v___x_5412_ = v___x_5406_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_x_5383_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v_x_5384_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
v___y_5398_ = v___x_5412_;
goto v___jp_5397_;
}
}
}
}
case 1:
{
lean_object* v_node_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5427_; 
v_node_5415_ = lean_ctor_get(v_v_5394_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v_v_5394_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5417_ = v_v_5394_;
v_isShared_5418_ = v_isSharedCheck_5427_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_node_5415_);
lean_dec(v_v_5394_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5427_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
size_t v___x_5419_; size_t v___x_5420_; size_t v___x_5421_; size_t v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5425_; 
v___x_5419_ = ((size_t)5ULL);
v___x_5420_ = lean_usize_shift_right(v_x_5381_, v___x_5419_);
v___x_5421_ = ((size_t)1ULL);
v___x_5422_ = lean_usize_add(v_x_5382_, v___x_5421_);
v___x_5423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5415_, v___x_5420_, v___x_5422_, v_x_5383_, v_x_5384_);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 0, v___x_5423_);
v___x_5425_ = v___x_5417_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
v___y_5398_ = v___x_5425_;
goto v___jp_5397_;
}
}
}
default: 
{
lean_object* v___x_5428_; 
v___x_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5428_, 0, v_x_5383_);
lean_ctor_set(v___x_5428_, 1, v_x_5384_);
v___y_5398_ = v___x_5428_;
goto v___jp_5397_;
}
}
v___jp_5397_:
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
v___x_5399_ = lean_array_fset(v_xs_x27_5396_, v_j_5388_, v___y_5398_);
lean_dec(v_j_5388_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5399_);
v___x_5401_ = v___x_5392_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
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
else
{
lean_object* v_ks_5431_; lean_object* v_vs_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5452_; 
v_ks_5431_ = lean_ctor_get(v_x_5380_, 0);
v_vs_5432_ = lean_ctor_get(v_x_5380_, 1);
v_isSharedCheck_5452_ = !lean_is_exclusive(v_x_5380_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5434_ = v_x_5380_;
v_isShared_5435_ = v_isSharedCheck_5452_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_vs_5432_);
lean_inc(v_ks_5431_);
lean_dec(v_x_5380_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5452_;
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
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_ks_5431_);
lean_ctor_set(v_reuseFailAlloc_5451_, 1, v_vs_5432_);
v___x_5437_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v_newNode_5438_; uint8_t v___y_5440_; size_t v___x_5446_; uint8_t v___x_5447_; 
v_newNode_5438_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5437_, v_x_5383_, v_x_5384_);
v___x_5446_ = ((size_t)7ULL);
v___x_5447_ = lean_usize_dec_le(v___x_5446_, v_x_5382_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; lean_object* v___x_5449_; uint8_t v___x_5450_; 
v___x_5448_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5438_);
v___x_5449_ = lean_unsigned_to_nat(4u);
v___x_5450_ = lean_nat_dec_lt(v___x_5448_, v___x_5449_);
lean_dec(v___x_5448_);
v___y_5440_ = v___x_5450_;
goto v___jp_5439_;
}
else
{
v___y_5440_ = v___x_5447_;
goto v___jp_5439_;
}
v___jp_5439_:
{
if (v___y_5440_ == 0)
{
lean_object* v_ks_5441_; lean_object* v_vs_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v_ks_5441_ = lean_ctor_get(v_newNode_5438_, 0);
lean_inc_ref(v_ks_5441_);
v_vs_5442_ = lean_ctor_get(v_newNode_5438_, 1);
lean_inc_ref(v_vs_5442_);
lean_dec_ref(v_newNode_5438_);
v___x_5443_ = lean_unsigned_to_nat(0u);
v___x_5444_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5445_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5382_, v_ks_5441_, v_vs_5442_, v___x_5443_, v___x_5444_);
lean_dec_ref(v_vs_5442_);
lean_dec_ref(v_ks_5441_);
return v___x_5445_;
}
else
{
return v_newNode_5438_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5453_, lean_object* v_keys_5454_, lean_object* v_vals_5455_, lean_object* v_i_5456_, lean_object* v_entries_5457_){
_start:
{
lean_object* v___x_5458_; uint8_t v___x_5459_; 
v___x_5458_ = lean_array_get_size(v_keys_5454_);
v___x_5459_ = lean_nat_dec_lt(v_i_5456_, v___x_5458_);
if (v___x_5459_ == 0)
{
lean_dec(v_i_5456_);
return v_entries_5457_;
}
else
{
lean_object* v_k_5460_; lean_object* v_v_5461_; uint64_t v___x_5462_; size_t v_h_5463_; size_t v___x_5464_; lean_object* v___x_5465_; size_t v___x_5466_; size_t v___x_5467_; size_t v___x_5468_; size_t v_h_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; 
v_k_5460_ = lean_array_fget_borrowed(v_keys_5454_, v_i_5456_);
v_v_5461_ = lean_array_fget_borrowed(v_vals_5455_, v_i_5456_);
v___x_5462_ = l_Lean_instHashableMVarId_hash(v_k_5460_);
v_h_5463_ = lean_uint64_to_usize(v___x_5462_);
v___x_5464_ = ((size_t)5ULL);
v___x_5465_ = lean_unsigned_to_nat(1u);
v___x_5466_ = ((size_t)1ULL);
v___x_5467_ = lean_usize_sub(v_depth_5453_, v___x_5466_);
v___x_5468_ = lean_usize_mul(v___x_5464_, v___x_5467_);
v_h_5469_ = lean_usize_shift_right(v_h_5463_, v___x_5468_);
v___x_5470_ = lean_nat_add(v_i_5456_, v___x_5465_);
lean_dec(v_i_5456_);
lean_inc(v_v_5461_);
lean_inc(v_k_5460_);
v___x_5471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5457_, v_h_5469_, v_depth_5453_, v_k_5460_, v_v_5461_);
v_i_5456_ = v___x_5470_;
v_entries_5457_ = v___x_5471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5473_, lean_object* v_keys_5474_, lean_object* v_vals_5475_, lean_object* v_i_5476_, lean_object* v_entries_5477_){
_start:
{
size_t v_depth_boxed_5478_; lean_object* v_res_5479_; 
v_depth_boxed_5478_ = lean_unbox_usize(v_depth_5473_);
lean_dec(v_depth_5473_);
v_res_5479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5478_, v_keys_5474_, v_vals_5475_, v_i_5476_, v_entries_5477_);
lean_dec_ref(v_vals_5475_);
lean_dec_ref(v_keys_5474_);
return v_res_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5480_, lean_object* v_x_5481_, lean_object* v_x_5482_, lean_object* v_x_5483_, lean_object* v_x_5484_){
_start:
{
size_t v_x_77141__boxed_5485_; size_t v_x_77142__boxed_5486_; lean_object* v_res_5487_; 
v_x_77141__boxed_5485_ = lean_unbox_usize(v_x_5481_);
lean_dec(v_x_5481_);
v_x_77142__boxed_5486_ = lean_unbox_usize(v_x_5482_);
lean_dec(v_x_5482_);
v_res_5487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5480_, v_x_77141__boxed_5485_, v_x_77142__boxed_5486_, v_x_5483_, v_x_5484_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5488_, lean_object* v_x_5489_, lean_object* v_x_5490_){
_start:
{
uint64_t v___x_5491_; size_t v___x_5492_; size_t v___x_5493_; lean_object* v___x_5494_; 
v___x_5491_ = l_Lean_instHashableMVarId_hash(v_x_5489_);
v___x_5492_ = lean_uint64_to_usize(v___x_5491_);
v___x_5493_ = ((size_t)1ULL);
v___x_5494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5488_, v___x_5492_, v___x_5493_, v_x_5489_, v_x_5490_);
return v___x_5494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5495_, lean_object* v_val_5496_, lean_object* v___y_5497_){
_start:
{
lean_object* v___x_5499_; lean_object* v_mctx_5500_; lean_object* v_cache_5501_; lean_object* v_zetaDeltaFVarIds_5502_; lean_object* v_postponed_5503_; lean_object* v_diag_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5532_; 
v___x_5499_ = lean_st_ref_take(v___y_5497_);
v_mctx_5500_ = lean_ctor_get(v___x_5499_, 0);
v_cache_5501_ = lean_ctor_get(v___x_5499_, 1);
v_zetaDeltaFVarIds_5502_ = lean_ctor_get(v___x_5499_, 2);
v_postponed_5503_ = lean_ctor_get(v___x_5499_, 3);
v_diag_5504_ = lean_ctor_get(v___x_5499_, 4);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5499_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5506_ = v___x_5499_;
v_isShared_5507_ = v_isSharedCheck_5532_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_diag_5504_);
lean_inc(v_postponed_5503_);
lean_inc(v_zetaDeltaFVarIds_5502_);
lean_inc(v_cache_5501_);
lean_inc(v_mctx_5500_);
lean_dec(v___x_5499_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5532_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v_depth_5508_; lean_object* v_levelAssignDepth_5509_; lean_object* v_lmvarCounter_5510_; lean_object* v_mvarCounter_5511_; lean_object* v_lDecls_5512_; lean_object* v_decls_5513_; lean_object* v_userNames_5514_; lean_object* v_lAssignment_5515_; lean_object* v_eAssignment_5516_; lean_object* v_dAssignment_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5531_; 
v_depth_5508_ = lean_ctor_get(v_mctx_5500_, 0);
v_levelAssignDepth_5509_ = lean_ctor_get(v_mctx_5500_, 1);
v_lmvarCounter_5510_ = lean_ctor_get(v_mctx_5500_, 2);
v_mvarCounter_5511_ = lean_ctor_get(v_mctx_5500_, 3);
v_lDecls_5512_ = lean_ctor_get(v_mctx_5500_, 4);
v_decls_5513_ = lean_ctor_get(v_mctx_5500_, 5);
v_userNames_5514_ = lean_ctor_get(v_mctx_5500_, 6);
v_lAssignment_5515_ = lean_ctor_get(v_mctx_5500_, 7);
v_eAssignment_5516_ = lean_ctor_get(v_mctx_5500_, 8);
v_dAssignment_5517_ = lean_ctor_get(v_mctx_5500_, 9);
v_isSharedCheck_5531_ = !lean_is_exclusive(v_mctx_5500_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5519_ = v_mctx_5500_;
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_dAssignment_5517_);
lean_inc(v_eAssignment_5516_);
lean_inc(v_lAssignment_5515_);
lean_inc(v_userNames_5514_);
lean_inc(v_decls_5513_);
lean_inc(v_lDecls_5512_);
lean_inc(v_mvarCounter_5511_);
lean_inc(v_lmvarCounter_5510_);
lean_inc(v_levelAssignDepth_5509_);
lean_inc(v_depth_5508_);
lean_dec(v_mctx_5500_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
v___x_5521_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5516_, v_mvarId_5495_, v_val_5496_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 8, v___x_5521_);
v___x_5523_ = v___x_5519_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_depth_5508_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_levelAssignDepth_5509_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_lmvarCounter_5510_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_mvarCounter_5511_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_lDecls_5512_);
lean_ctor_set(v_reuseFailAlloc_5530_, 5, v_decls_5513_);
lean_ctor_set(v_reuseFailAlloc_5530_, 6, v_userNames_5514_);
lean_ctor_set(v_reuseFailAlloc_5530_, 7, v_lAssignment_5515_);
lean_ctor_set(v_reuseFailAlloc_5530_, 8, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5530_, 9, v_dAssignment_5517_);
v___x_5523_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5525_; 
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 0, v___x_5523_);
v___x_5525_ = v___x_5506_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_cache_5501_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_zetaDeltaFVarIds_5502_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v_postponed_5503_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_diag_5504_);
v___x_5525_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5526_ = lean_st_ref_set(v___y_5497_, v___x_5525_);
v___x_5527_ = lean_box(0);
v___x_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5527_);
return v___x_5528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5533_, lean_object* v_val_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_){
_start:
{
lean_object* v_res_5537_; 
v_res_5537_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5533_, v_val_5534_, v___y_5535_);
lean_dec(v___y_5535_);
return v_res_5537_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5538_, lean_object* v_snd_5539_, uint8_t v___y_5540_, lean_object* v_as_x27_5541_, lean_object* v_b_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
_start:
{
if (lean_obj_tag(v_as_x27_5541_) == 0)
{
lean_object* v___x_5553_; 
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v___x_5553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5553_, 0, v_b_5542_);
return v___x_5553_;
}
else
{
lean_object* v_head_5554_; lean_object* v_tail_5555_; lean_object* v___x_5556_; 
v_head_5554_ = lean_ctor_get(v_as_x27_5541_, 0);
v_tail_5555_ = lean_ctor_get(v_as_x27_5541_, 1);
lean_inc_ref(v_kp_5538_);
lean_inc(v___y_5551_);
lean_inc_ref(v___y_5550_);
lean_inc(v___y_5549_);
lean_inc_ref(v___y_5548_);
lean_inc(v___y_5547_);
lean_inc_ref(v___y_5546_);
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc(v_head_5554_);
v___x_5556_ = lean_apply_11(v_kp_5538_, v_head_5554_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, lean_box(0));
if (lean_obj_tag(v___x_5556_) == 0)
{
lean_object* v_snd_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5653_; 
v_snd_5557_ = lean_ctor_get(v_b_5542_, 1);
v_isSharedCheck_5653_ = !lean_is_exclusive(v_b_5542_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; 
v_unused_5654_ = lean_ctor_get(v_b_5542_, 0);
lean_dec(v_unused_5654_);
v___x_5559_ = v_b_5542_;
v_isShared_5560_ = v_isSharedCheck_5653_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_snd_5557_);
lean_dec(v_b_5542_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5653_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5652_; 
v_a_5561_ = lean_ctor_get(v___x_5556_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5556_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5563_ = v___x_5556_;
v_isShared_5564_ = v_isSharedCheck_5652_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5556_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5652_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v_fst_5565_; lean_object* v_snd_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5651_; 
v_fst_5565_ = lean_ctor_get(v_snd_5557_, 0);
v_snd_5566_ = lean_ctor_get(v_snd_5557_, 1);
v_isSharedCheck_5651_ = !lean_is_exclusive(v_snd_5557_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5568_ = v_snd_5557_;
v_isShared_5569_ = v_isSharedCheck_5651_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_snd_5566_);
lean_inc(v_fst_5565_);
lean_dec(v_snd_5557_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5651_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; 
v___x_5570_ = lean_box(0);
if (lean_obj_tag(v_a_5561_) == 0)
{
lean_object* v_seq_5571_; lean_object* v_mvarId_5572_; lean_object* v___x_5573_; 
lean_del_object(v___x_5563_);
v_seq_5571_ = lean_ctor_get(v_a_5561_, 0);
v_mvarId_5572_ = lean_ctor_get(v_head_5554_, 1);
lean_inc(v_mvarId_5572_);
v___x_5573_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5572_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v_a_5574_; 
v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
lean_inc(v_a_5574_);
lean_dec_ref_known(v___x_5573_, 1);
if (lean_obj_tag(v_a_5574_) == 1)
{
lean_object* v_val_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5606_; 
lean_dec_ref(v_kp_5538_);
v_val_5575_ = lean_ctor_get(v_a_5574_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_a_5574_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5577_ = v_a_5574_;
v_isShared_5578_ = v_isSharedCheck_5606_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_val_5575_);
lean_dec(v_a_5574_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5606_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v_mvarId_5579_; lean_object* v___x_5580_; 
v_mvarId_5579_ = lean_ctor_get(v_snd_5539_, 1);
lean_inc(v_mvarId_5579_);
lean_dec_ref(v_snd_5539_);
v___x_5580_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5579_, v_val_5575_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5596_; 
v_isSharedCheck_5596_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v___x_5580_, 0);
lean_dec(v_unused_5597_);
v___x_5582_ = v___x_5580_;
v_isShared_5583_ = v_isSharedCheck_5596_;
goto v_resetjp_5581_;
}
else
{
lean_dec(v___x_5580_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5596_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5585_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v_a_5561_);
v___x_5585_ = v___x_5577_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5561_);
v___x_5585_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5587_; 
if (v_isShared_5569_ == 0)
{
v___x_5587_ = v___x_5568_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_snd_5566_);
v___x_5587_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5589_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5587_);
lean_ctor_set(v___x_5559_, 0, v___x_5585_);
v___x_5589_ = v___x_5559_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5591_; 
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 0, v___x_5589_);
v___x_5591_ = v___x_5582_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
}
}
else
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5605_; 
lean_del_object(v___x_5577_);
lean_dec_ref_known(v_a_5561_, 1);
lean_del_object(v___x_5568_);
lean_dec(v_snd_5566_);
lean_dec(v_fst_5565_);
lean_del_object(v___x_5559_);
v_a_5598_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5600_ = v___x_5580_;
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5580_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5603_; 
if (v_isShared_5601_ == 0)
{
v___x_5603_ = v___x_5600_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5598_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
}
}
else
{
uint8_t v___x_5607_; uint8_t v___x_5608_; 
lean_inc(v_seq_5571_);
lean_dec(v_a_5574_);
lean_dec_ref_known(v_a_5561_, 1);
v___x_5607_ = l_List_isEmpty___redArg(v_seq_5571_);
v___x_5608_ = lean_bool_not(v___x_5607_);
if (v___x_5608_ == 0)
{
lean_object* v___x_5610_; 
lean_dec(v_seq_5571_);
if (v_isShared_5569_ == 0)
{
v___x_5610_ = v___x_5568_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_snd_5566_);
v___x_5610_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
lean_object* v___x_5612_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5610_);
lean_ctor_set(v___x_5559_, 0, v___x_5570_);
v___x_5612_ = v___x_5559_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v___x_5610_);
v___x_5612_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
v_as_x27_5541_ = v_tail_5555_;
v_b_5542_ = v___x_5612_;
goto _start;
}
}
}
else
{
lean_object* v___x_5616_; lean_object* v___x_5618_; 
v___x_5616_ = lean_array_push(v_fst_5565_, v_seq_5571_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 0, v___x_5616_);
v___x_5618_ = v___x_5568_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5616_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_snd_5566_);
v___x_5618_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5620_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5618_);
lean_ctor_set(v___x_5559_, 0, v___x_5570_);
v___x_5620_ = v___x_5559_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v___x_5618_);
v___x_5620_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
v_as_x27_5541_ = v_tail_5555_;
v_b_5542_ = v___x_5620_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec_ref_known(v_a_5561_, 1);
lean_del_object(v___x_5568_);
lean_dec(v_snd_5566_);
lean_dec(v_fst_5565_);
lean_del_object(v___x_5559_);
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v_a_5624_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5573_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5573_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
if (v___y_5540_ == 0)
{
lean_object* v_gs_5632_; lean_object* v___x_5633_; lean_object* v___x_5635_; 
lean_del_object(v___x_5563_);
v_gs_5632_ = lean_ctor_get(v_a_5561_, 0);
lean_inc(v_gs_5632_);
lean_dec_ref_known(v_a_5561_, 1);
v___x_5633_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5566_, v_gs_5632_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 1, v___x_5633_);
v___x_5635_ = v___x_5568_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5640_, 1, v___x_5633_);
v___x_5635_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
lean_object* v___x_5637_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5635_);
lean_ctor_set(v___x_5559_, 0, v___x_5570_);
v___x_5637_ = v___x_5559_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5570_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5635_);
v___x_5637_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
v_as_x27_5541_ = v_tail_5555_;
v_b_5542_ = v___x_5637_;
goto _start;
}
}
}
else
{
lean_object* v___x_5641_; lean_object* v___x_5643_; 
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v___x_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5641_, 0, v_a_5561_);
if (v_isShared_5569_ == 0)
{
v___x_5643_ = v___x_5568_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5565_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_snd_5566_);
v___x_5643_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5645_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5643_);
lean_ctor_set(v___x_5559_, 0, v___x_5641_);
v___x_5645_ = v___x_5559_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5641_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
lean_object* v___x_5647_; 
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5645_);
v___x_5647_ = v___x_5563_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5645_);
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
}
}
}
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
lean_dec_ref(v_b_5542_);
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v_a_5655_ = lean_ctor_get(v___x_5556_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5556_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5657_ = v___x_5556_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_dec(v___x_5556_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5658_ == 0)
{
v___x_5660_ = v___x_5657_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_a_5655_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5663_, lean_object* v_snd_5664_, lean_object* v___y_5665_, lean_object* v_as_x27_5666_, lean_object* v_b_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
uint8_t v___y_77355__boxed_5678_; lean_object* v_res_5679_; 
v___y_77355__boxed_5678_ = lean_unbox(v___y_5665_);
v_res_5679_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5663_, v_snd_5664_, v___y_77355__boxed_5678_, v_as_x27_5666_, v_b_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec(v_as_x27_5666_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5680_, lean_object* v_c_5681_, lean_object* v___x_5682_, lean_object* v___x_5683_, uint8_t v_isRec_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
if (lean_obj_tag(v_a_5685_) == 0)
{
lean_object* v___x_5687_; 
lean_dec(v___x_5683_);
lean_dec_ref(v___x_5682_);
lean_dec_ref(v_snd_5680_);
v___x_5687_ = lean_array_to_list(v_a_5686_);
return v___x_5687_;
}
else
{
lean_object* v_toGoalState_5688_; lean_object* v_split_5689_; lean_object* v_head_5690_; lean_object* v_tail_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5751_; 
v_toGoalState_5688_ = lean_ctor_get(v_snd_5680_, 0);
lean_inc_ref(v_toGoalState_5688_);
v_split_5689_ = lean_ctor_get(v_toGoalState_5688_, 14);
lean_inc_ref(v_split_5689_);
v_head_5690_ = lean_ctor_get(v_a_5685_, 0);
v_tail_5691_ = lean_ctor_get(v_a_5685_, 1);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_a_5685_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5693_ = v_a_5685_;
v_isShared_5694_ = v_isSharedCheck_5751_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_tail_5691_);
lean_inc(v_head_5690_);
lean_dec(v_a_5685_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5751_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v_nextDeclIdx_5695_; lean_object* v_enodeMap_5696_; lean_object* v_exprs_5697_; lean_object* v_parents_5698_; lean_object* v_congrTable_5699_; lean_object* v_appMap_5700_; lean_object* v_indicesFound_5701_; lean_object* v_newFacts_5702_; uint8_t v_inconsistent_5703_; lean_object* v_nextIdx_5704_; lean_object* v_newRawFacts_5705_; lean_object* v_facts_5706_; lean_object* v_extThms_5707_; lean_object* v_ematch_5708_; lean_object* v_inj_5709_; lean_object* v_clean_5710_; lean_object* v_sstates_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5749_; 
v_nextDeclIdx_5695_ = lean_ctor_get(v_toGoalState_5688_, 0);
v_enodeMap_5696_ = lean_ctor_get(v_toGoalState_5688_, 1);
v_exprs_5697_ = lean_ctor_get(v_toGoalState_5688_, 2);
v_parents_5698_ = lean_ctor_get(v_toGoalState_5688_, 3);
v_congrTable_5699_ = lean_ctor_get(v_toGoalState_5688_, 4);
v_appMap_5700_ = lean_ctor_get(v_toGoalState_5688_, 5);
v_indicesFound_5701_ = lean_ctor_get(v_toGoalState_5688_, 6);
v_newFacts_5702_ = lean_ctor_get(v_toGoalState_5688_, 7);
v_inconsistent_5703_ = lean_ctor_get_uint8(v_toGoalState_5688_, sizeof(void*)*17);
v_nextIdx_5704_ = lean_ctor_get(v_toGoalState_5688_, 8);
v_newRawFacts_5705_ = lean_ctor_get(v_toGoalState_5688_, 9);
v_facts_5706_ = lean_ctor_get(v_toGoalState_5688_, 10);
v_extThms_5707_ = lean_ctor_get(v_toGoalState_5688_, 11);
v_ematch_5708_ = lean_ctor_get(v_toGoalState_5688_, 12);
v_inj_5709_ = lean_ctor_get(v_toGoalState_5688_, 13);
v_clean_5710_ = lean_ctor_get(v_toGoalState_5688_, 15);
v_sstates_5711_ = lean_ctor_get(v_toGoalState_5688_, 16);
v_isSharedCheck_5749_ = !lean_is_exclusive(v_toGoalState_5688_);
if (v_isSharedCheck_5749_ == 0)
{
lean_object* v_unused_5750_; 
v_unused_5750_ = lean_ctor_get(v_toGoalState_5688_, 14);
lean_dec(v_unused_5750_);
v___x_5713_ = v_toGoalState_5688_;
v_isShared_5714_ = v_isSharedCheck_5749_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_sstates_5711_);
lean_inc(v_clean_5710_);
lean_inc(v_inj_5709_);
lean_inc(v_ematch_5708_);
lean_inc(v_extThms_5707_);
lean_inc(v_facts_5706_);
lean_inc(v_newRawFacts_5705_);
lean_inc(v_nextIdx_5704_);
lean_inc(v_newFacts_5702_);
lean_inc(v_indicesFound_5701_);
lean_inc(v_appMap_5700_);
lean_inc(v_congrTable_5699_);
lean_inc(v_parents_5698_);
lean_inc(v_exprs_5697_);
lean_inc(v_enodeMap_5696_);
lean_inc(v_nextDeclIdx_5695_);
lean_dec(v_toGoalState_5688_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5749_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v_num_5715_; lean_object* v_candidates_5716_; lean_object* v_added_5717_; lean_object* v_resolved_5718_; lean_object* v_trace_5719_; lean_object* v_lookaheads_5720_; lean_object* v_argPosMap_5721_; lean_object* v_argsAt_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5748_; 
v_num_5715_ = lean_ctor_get(v_split_5689_, 0);
v_candidates_5716_ = lean_ctor_get(v_split_5689_, 1);
v_added_5717_ = lean_ctor_get(v_split_5689_, 2);
v_resolved_5718_ = lean_ctor_get(v_split_5689_, 3);
v_trace_5719_ = lean_ctor_get(v_split_5689_, 4);
v_lookaheads_5720_ = lean_ctor_get(v_split_5689_, 5);
v_argPosMap_5721_ = lean_ctor_get(v_split_5689_, 6);
v_argsAt_5722_ = lean_ctor_get(v_split_5689_, 7);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_split_5689_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5724_ = v_split_5689_;
v_isShared_5725_ = v_isSharedCheck_5748_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_argsAt_5722_);
lean_inc(v_argPosMap_5721_);
lean_inc(v_lookaheads_5720_);
lean_inc(v_trace_5719_);
lean_inc(v_resolved_5718_);
lean_inc(v_added_5717_);
lean_inc(v_candidates_5716_);
lean_inc(v_num_5715_);
lean_dec(v_split_5689_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5748_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5726_; lean_object* v___y_5728_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5726_ = lean_array_get_size(v_a_5686_);
v___x_5746_ = lean_unsigned_to_nat(0u);
v___x_5747_ = lean_nat_dec_lt(v___x_5746_, v___x_5726_);
if (v___x_5747_ == 0)
{
if (v_isRec_5684_ == 0)
{
v___y_5728_ = v_num_5715_;
goto v___jp_5727_;
}
else
{
goto v___jp_5743_;
}
}
else
{
goto v___jp_5743_;
}
v___jp_5727_:
{
lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5732_; 
v___x_5729_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5681_);
lean_inc(v___x_5683_);
lean_inc_ref(v___x_5682_);
v___x_5730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5682_);
lean_ctor_set(v___x_5730_, 1, v___x_5726_);
lean_ctor_set(v___x_5730_, 2, v___x_5683_);
lean_ctor_set(v___x_5730_, 3, v___x_5729_);
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 1, v_trace_5719_);
lean_ctor_set(v___x_5693_, 0, v___x_5730_);
v___x_5732_ = v___x_5693_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5730_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_trace_5719_);
v___x_5732_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
lean_object* v___x_5734_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 4, v___x_5732_);
lean_ctor_set(v___x_5724_, 0, v___y_5728_);
v___x_5734_ = v___x_5724_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___y_5728_);
lean_ctor_set(v_reuseFailAlloc_5741_, 1, v_candidates_5716_);
lean_ctor_set(v_reuseFailAlloc_5741_, 2, v_added_5717_);
lean_ctor_set(v_reuseFailAlloc_5741_, 3, v_resolved_5718_);
lean_ctor_set(v_reuseFailAlloc_5741_, 4, v___x_5732_);
lean_ctor_set(v_reuseFailAlloc_5741_, 5, v_lookaheads_5720_);
lean_ctor_set(v_reuseFailAlloc_5741_, 6, v_argPosMap_5721_);
lean_ctor_set(v_reuseFailAlloc_5741_, 7, v_argsAt_5722_);
v___x_5734_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
lean_object* v___x_5736_; 
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 14, v___x_5734_);
v___x_5736_ = v___x_5713_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_nextDeclIdx_5695_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_enodeMap_5696_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_exprs_5697_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v_parents_5698_);
lean_ctor_set(v_reuseFailAlloc_5740_, 4, v_congrTable_5699_);
lean_ctor_set(v_reuseFailAlloc_5740_, 5, v_appMap_5700_);
lean_ctor_set(v_reuseFailAlloc_5740_, 6, v_indicesFound_5701_);
lean_ctor_set(v_reuseFailAlloc_5740_, 7, v_newFacts_5702_);
lean_ctor_set(v_reuseFailAlloc_5740_, 8, v_nextIdx_5704_);
lean_ctor_set(v_reuseFailAlloc_5740_, 9, v_newRawFacts_5705_);
lean_ctor_set(v_reuseFailAlloc_5740_, 10, v_facts_5706_);
lean_ctor_set(v_reuseFailAlloc_5740_, 11, v_extThms_5707_);
lean_ctor_set(v_reuseFailAlloc_5740_, 12, v_ematch_5708_);
lean_ctor_set(v_reuseFailAlloc_5740_, 13, v_inj_5709_);
lean_ctor_set(v_reuseFailAlloc_5740_, 14, v___x_5734_);
lean_ctor_set(v_reuseFailAlloc_5740_, 15, v_clean_5710_);
lean_ctor_set(v_reuseFailAlloc_5740_, 16, v_sstates_5711_);
lean_ctor_set_uint8(v_reuseFailAlloc_5740_, sizeof(void*)*17, v_inconsistent_5703_);
v___x_5736_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; 
v___x_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v_head_5690_);
v___x_5738_ = lean_array_push(v_a_5686_, v___x_5737_);
v_a_5685_ = v_tail_5691_;
v_a_5686_ = v___x_5738_;
goto _start;
}
}
}
}
v___jp_5743_:
{
lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5744_ = lean_unsigned_to_nat(1u);
v___x_5745_ = lean_nat_add(v_num_5715_, v___x_5744_);
lean_dec(v_num_5715_);
v___y_5728_ = v___x_5745_;
goto v___jp_5727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5752_, lean_object* v_c_5753_, lean_object* v___x_5754_, lean_object* v___x_5755_, lean_object* v_isRec_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_){
_start:
{
uint8_t v_isRec_boxed_5759_; lean_object* v_res_5760_; 
v_isRec_boxed_5759_ = lean_unbox(v_isRec_5756_);
v_res_5760_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5752_, v_c_5753_, v___x_5754_, v___x_5755_, v_isRec_boxed_5759_, v_a_5757_, v_a_5758_);
lean_dec_ref(v_c_5753_);
return v_res_5760_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5772_ = lean_box(0);
v___x_5773_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5774_ = l_Lean_mkConst(v___x_5773_, v___x_5772_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5775_, lean_object* v_numCases_5776_, uint8_t v_isRec_5777_, uint8_t v_stopAtFirstFailure_5778_, uint8_t v_compress_5779_, lean_object* v_candidates_x3f_5780_, lean_object* v_goal_5781_, lean_object* v_kp_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5784_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v___x_5795_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc(v_a_5794_);
lean_dec_ref_known(v___x_5793_, 1);
lean_inc_ref(v_goal_5781_);
v___x_5795_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5781_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; uint8_t v_trace_5797_; lean_object* v_mvarId_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___f_5801_; lean_object* v___x_5802_; lean_object* v___f_5803_; lean_object* v___x_5804_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
lean_inc_n(v_a_5796_, 2);
lean_dec_ref_known(v___x_5795_, 1);
v_trace_5797_ = lean_ctor_get_uint8(v_a_5794_, sizeof(void*)*13);
lean_dec(v_a_5794_);
v_mvarId_5798_ = lean_ctor_get(v_goal_5781_, 1);
lean_inc(v_mvarId_5798_);
v___x_5799_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5775_);
v___x_5800_ = lean_box(v_isRec_5777_);
lean_inc_ref_n(v_c_5775_, 2);
lean_inc_ref(v___x_5799_);
v___f_5801_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5801_, 0, v___x_5799_);
lean_closure_set(v___f_5801_, 1, v_c_5775_);
lean_closure_set(v___f_5801_, 2, v_a_5796_);
lean_closure_set(v___f_5801_, 3, v_numCases_5776_);
lean_closure_set(v___f_5801_, 4, v___x_5800_);
v___x_5802_ = lean_box(v_trace_5797_);
v___f_5803_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5803_, 0, v_goal_5781_);
lean_closure_set(v___f_5803_, 1, v___x_5802_);
lean_closure_set(v___f_5803_, 2, v___f_5801_);
lean_closure_set(v___f_5803_, 3, v_c_5775_);
lean_closure_set(v___f_5803_, 4, v_candidates_x3f_5780_);
v___x_5804_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5798_, v___f_5803_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5804_) == 0)
{
lean_object* v_a_5805_; lean_object* v_fst_5806_; lean_object* v_snd_5807_; lean_object* v_fst_5808_; lean_object* v_snd_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; 
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
lean_inc(v_a_5805_);
lean_dec_ref_known(v___x_5804_, 1);
v_fst_5806_ = lean_ctor_get(v_a_5805_, 0);
lean_inc(v_fst_5806_);
v_snd_5807_ = lean_ctor_get(v_a_5805_, 1);
lean_inc_n(v_snd_5807_, 3);
lean_dec(v_a_5805_);
v_fst_5808_ = lean_ctor_get(v_fst_5806_, 0);
lean_inc(v_fst_5808_);
v_snd_5809_ = lean_ctor_get(v_fst_5806_, 1);
lean_inc(v_snd_5809_);
lean_dec(v_fst_5806_);
v___x_5810_ = l_List_lengthTR___redArg(v_fst_5808_);
v___x_5811_ = lean_unsigned_to_nat(0u);
v___x_5812_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5813_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5807_, v_c_5775_, v___x_5799_, v___x_5810_, v_isRec_5777_, v_fst_5808_, v___x_5812_);
lean_dec_ref(v_c_5775_);
v___x_5814_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5815_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5782_, v_snd_5807_, v_stopAtFirstFailure_5778_, v___x_5813_, v___x_5814_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
lean_dec(v___x_5813_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v_a_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5903_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5818_ = v___x_5815_;
v_isShared_5819_ = v_isSharedCheck_5903_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_a_5816_);
lean_dec(v___x_5815_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5903_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v_fst_5820_; 
v_fst_5820_ = lean_ctor_get(v_a_5816_, 0);
if (lean_obj_tag(v_fst_5820_) == 0)
{
lean_object* v_snd_5821_; lean_object* v_mvarId_5822_; lean_object* v___x_5823_; 
lean_del_object(v___x_5818_);
v_snd_5821_ = lean_ctor_get(v_a_5816_, 1);
lean_inc(v_snd_5821_);
lean_dec(v_a_5816_);
v_mvarId_5822_ = lean_ctor_get(v_snd_5807_, 1);
lean_inc_n(v_mvarId_5822_, 2);
lean_dec(v_snd_5807_);
v___x_5823_ = l_Lean_MVarId_getType(v_mvarId_5822_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5890_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5826_ = v___x_5823_;
v_isShared_5827_ = v_isSharedCheck_5890_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_a_5824_);
lean_dec(v___x_5823_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5890_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v_fst_5828_; lean_object* v_snd_5829_; lean_object* v___y_5831_; lean_object* v___y_5832_; uint8_t v___x_5879_; 
v_fst_5828_ = lean_ctor_get(v_snd_5821_, 0);
lean_inc(v_fst_5828_);
v_snd_5829_ = lean_ctor_get(v_snd_5821_, 1);
lean_inc(v_snd_5829_);
lean_dec(v_snd_5821_);
v___x_5879_ = l_Lean_Expr_isFalse(v_a_5824_);
if (v___x_5879_ == 0)
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v_a_5882_; lean_object* v___x_5883_; 
v___x_5880_ = l_Lean_mkMVar(v_a_5796_);
v___x_5881_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5880_, v_a_5789_);
v_a_5882_ = lean_ctor_get(v___x_5881_, 0);
lean_inc(v_a_5882_);
lean_dec_ref(v___x_5881_);
v___x_5883_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5822_, v_a_5882_, v_a_5789_);
lean_dec_ref(v___x_5883_);
v___y_5831_ = v_a_5790_;
v___y_5832_ = v_a_5791_;
goto v___jp_5830_;
}
else
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v_a_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; 
v___x_5884_ = l_Lean_mkMVar(v_a_5796_);
v___x_5885_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5884_, v_a_5789_);
v_a_5886_ = lean_ctor_get(v___x_5885_, 0);
lean_inc(v_a_5886_);
lean_dec_ref(v___x_5885_);
v___x_5887_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5888_ = l_Lean_Meta_mkExpectedPropHint(v_a_5886_, v___x_5887_);
v___x_5889_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5822_, v___x_5888_, v_a_5789_);
lean_dec_ref(v___x_5889_);
v___y_5831_ = v_a_5790_;
v___y_5832_ = v_a_5791_;
goto v___jp_5830_;
}
v___jp_5830_:
{
lean_object* v___x_5833_; uint8_t v___x_5834_; 
v___x_5833_ = lean_array_get_size(v_snd_5829_);
v___x_5834_ = lean_nat_dec_eq(v___x_5833_, v___x_5811_);
if (v___x_5834_ == 0)
{
lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5838_; 
lean_dec(v_fst_5828_);
lean_dec(v_snd_5809_);
v___x_5835_ = lean_array_to_list(v_snd_5829_);
v___x_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5835_);
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 0, v___x_5836_);
v___x_5838_ = v___x_5826_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5836_);
v___x_5838_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
return v___x_5838_;
}
}
else
{
lean_dec(v_snd_5829_);
if (lean_obj_tag(v_snd_5809_) == 1)
{
lean_object* v_val_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5874_; 
lean_del_object(v___x_5826_);
v_val_5840_ = lean_ctor_get(v_snd_5809_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v_snd_5809_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5842_ = v_snd_5809_;
v_isShared_5843_ = v_isSharedCheck_5874_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_val_5840_);
lean_dec(v_snd_5809_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5874_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
lean_object* v___x_5844_; 
v___x_5844_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5840_, v___y_5831_);
lean_dec(v_val_5840_);
if (lean_obj_tag(v___x_5844_) == 0)
{
lean_object* v_a_5845_; lean_object* v___x_5846_; 
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
lean_inc(v_a_5845_);
lean_dec_ref_known(v___x_5844_, 1);
v___x_5846_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5845_, v_fst_5828_, v_compress_5779_, v___y_5831_, v___y_5832_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5857_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5857_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5849_ = v___x_5846_;
v_isShared_5850_ = v_isSharedCheck_5857_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5846_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5857_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5843_ == 0)
{
lean_ctor_set_tag(v___x_5842_, 0);
lean_ctor_set(v___x_5842_, 0, v_a_5847_);
v___x_5852_ = v___x_5842_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5847_);
v___x_5852_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5854_; 
if (v_isShared_5850_ == 0)
{
lean_ctor_set(v___x_5849_, 0, v___x_5852_);
v___x_5854_ = v___x_5849_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
else
{
lean_object* v_a_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5865_; 
lean_del_object(v___x_5842_);
v_a_5858_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5860_ = v___x_5846_;
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_a_5858_);
lean_dec(v___x_5846_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5863_; 
if (v_isShared_5861_ == 0)
{
v___x_5863_ = v___x_5860_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5858_);
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
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_del_object(v___x_5842_);
lean_dec(v_fst_5828_);
v_a_5866_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5844_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5844_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
}
}
else
{
lean_object* v___x_5875_; lean_object* v___x_5877_; 
lean_dec(v_fst_5828_);
lean_dec(v_snd_5809_);
v___x_5875_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 0, v___x_5875_);
v___x_5877_ = v___x_5826_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v___x_5875_);
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
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_dec(v_mvarId_5822_);
lean_dec(v_snd_5821_);
lean_dec(v_snd_5809_);
lean_dec(v_a_5796_);
v_a_5891_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5823_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5823_);
v___x_5893_ = lean_box(0);
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
v_resetjp_5892_:
{
lean_object* v___x_5896_; 
if (v_isShared_5894_ == 0)
{
v___x_5896_ = v___x_5893_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_a_5891_);
v___x_5896_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
return v___x_5896_;
}
}
}
}
else
{
lean_object* v_val_5899_; lean_object* v___x_5901_; 
lean_inc_ref(v_fst_5820_);
lean_dec(v_a_5816_);
lean_dec(v_snd_5809_);
lean_dec(v_snd_5807_);
lean_dec(v_a_5796_);
v_val_5899_ = lean_ctor_get(v_fst_5820_, 0);
lean_inc(v_val_5899_);
lean_dec_ref_known(v_fst_5820_, 1);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v_val_5899_);
v___x_5901_ = v___x_5818_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_val_5899_);
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
else
{
lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5911_; 
lean_dec(v_snd_5809_);
lean_dec(v_snd_5807_);
lean_dec(v_a_5796_);
v_a_5904_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5911_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5911_ == 0)
{
v___x_5906_ = v___x_5815_;
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5815_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v___x_5909_; 
if (v_isShared_5907_ == 0)
{
v___x_5909_ = v___x_5906_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_a_5904_);
v___x_5909_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
return v___x_5909_;
}
}
}
}
else
{
lean_object* v_a_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5919_; 
lean_dec_ref(v___x_5799_);
lean_dec(v_a_5796_);
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_c_5775_);
v_a_5912_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5919_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5914_ = v___x_5804_;
v_isShared_5915_ = v_isSharedCheck_5919_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_a_5912_);
lean_dec(v___x_5804_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5919_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v___x_5917_; 
if (v_isShared_5915_ == 0)
{
v___x_5917_ = v___x_5914_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_a_5912_);
v___x_5917_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
return v___x_5917_;
}
}
}
}
else
{
lean_object* v_a_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5927_; 
lean_dec(v_a_5794_);
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_goal_5781_);
lean_dec(v_candidates_x3f_5780_);
lean_dec(v_numCases_5776_);
lean_dec_ref(v_c_5775_);
v_a_5920_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5927_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5927_ == 0)
{
v___x_5922_ = v___x_5795_;
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_a_5920_);
lean_dec(v___x_5795_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5925_; 
if (v_isShared_5923_ == 0)
{
v___x_5925_ = v___x_5922_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_a_5920_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
}
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5935_; 
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_goal_5781_);
lean_dec(v_candidates_x3f_5780_);
lean_dec(v_numCases_5776_);
lean_dec_ref(v_c_5775_);
v_a_5928_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5935_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5930_ = v___x_5793_;
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5793_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5936_ = _args[0];
lean_object* v_numCases_5937_ = _args[1];
lean_object* v_isRec_5938_ = _args[2];
lean_object* v_stopAtFirstFailure_5939_ = _args[3];
lean_object* v_compress_5940_ = _args[4];
lean_object* v_candidates_x3f_5941_ = _args[5];
lean_object* v_goal_5942_ = _args[6];
lean_object* v_kp_5943_ = _args[7];
lean_object* v_a_5944_ = _args[8];
lean_object* v_a_5945_ = _args[9];
lean_object* v_a_5946_ = _args[10];
lean_object* v_a_5947_ = _args[11];
lean_object* v_a_5948_ = _args[12];
lean_object* v_a_5949_ = _args[13];
lean_object* v_a_5950_ = _args[14];
lean_object* v_a_5951_ = _args[15];
lean_object* v_a_5952_ = _args[16];
lean_object* v_a_5953_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5954_; uint8_t v_stopAtFirstFailure_boxed_5955_; uint8_t v_compress_boxed_5956_; lean_object* v_res_5957_; 
v_isRec_boxed_5954_ = lean_unbox(v_isRec_5938_);
v_stopAtFirstFailure_boxed_5955_ = lean_unbox(v_stopAtFirstFailure_5939_);
v_compress_boxed_5956_ = lean_unbox(v_compress_5940_);
v_res_5957_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5936_, v_numCases_5937_, v_isRec_boxed_5954_, v_stopAtFirstFailure_boxed_5955_, v_compress_boxed_5956_, v_candidates_x3f_5941_, v_goal_5942_, v_kp_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
lean_dec(v_a_5952_);
lean_dec_ref(v_a_5951_);
lean_dec(v_a_5950_);
lean_dec_ref(v_a_5949_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
lean_dec(v_a_5944_);
return v_res_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5958_, lean_object* v_numCases_5959_, uint8_t v_isRec_5960_, uint8_t v_stopAtFirstFailure_5961_, uint8_t v_compress_5962_, lean_object* v_candidates_x3f_5963_, lean_object* v_goal_5964_, lean_object* v_x_5965_, lean_object* v_kp_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5958_, v_numCases_5959_, v_isRec_5960_, v_stopAtFirstFailure_5961_, v_compress_5962_, v_candidates_x3f_5963_, v_goal_5964_, v_kp_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5978_ = _args[0];
lean_object* v_numCases_5979_ = _args[1];
lean_object* v_isRec_5980_ = _args[2];
lean_object* v_stopAtFirstFailure_5981_ = _args[3];
lean_object* v_compress_5982_ = _args[4];
lean_object* v_candidates_x3f_5983_ = _args[5];
lean_object* v_goal_5984_ = _args[6];
lean_object* v_x_5985_ = _args[7];
lean_object* v_kp_5986_ = _args[8];
lean_object* v_a_5987_ = _args[9];
lean_object* v_a_5988_ = _args[10];
lean_object* v_a_5989_ = _args[11];
lean_object* v_a_5990_ = _args[12];
lean_object* v_a_5991_ = _args[13];
lean_object* v_a_5992_ = _args[14];
lean_object* v_a_5993_ = _args[15];
lean_object* v_a_5994_ = _args[16];
lean_object* v_a_5995_ = _args[17];
lean_object* v_a_5996_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5997_; uint8_t v_stopAtFirstFailure_boxed_5998_; uint8_t v_compress_boxed_5999_; lean_object* v_res_6000_; 
v_isRec_boxed_5997_ = lean_unbox(v_isRec_5980_);
v_stopAtFirstFailure_boxed_5998_ = lean_unbox(v_stopAtFirstFailure_5981_);
v_compress_boxed_5999_ = lean_unbox(v_compress_5982_);
v_res_6000_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5978_, v_numCases_5979_, v_isRec_boxed_5997_, v_stopAtFirstFailure_boxed_5998_, v_compress_boxed_5999_, v_candidates_x3f_5983_, v_goal_5984_, v_x_5985_, v_kp_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_);
lean_dec(v_a_5995_);
lean_dec_ref(v_a_5994_);
lean_dec(v_a_5993_);
lean_dec_ref(v_a_5992_);
lean_dec(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec_ref(v_a_5988_);
lean_dec(v_a_5987_);
lean_dec_ref(v_x_5985_);
return v_res_6000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6001_, lean_object* v_snd_6002_, uint8_t v___y_6003_, lean_object* v_as_6004_, lean_object* v_as_x27_6005_, lean_object* v_b_6006_, lean_object* v_a_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_){
_start:
{
lean_object* v___x_6018_; 
v___x_6018_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6001_, v_snd_6002_, v___y_6003_, v_as_x27_6005_, v_b_6006_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_);
return v___x_6018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6019_ = _args[0];
lean_object* v_snd_6020_ = _args[1];
lean_object* v___y_6021_ = _args[2];
lean_object* v_as_6022_ = _args[3];
lean_object* v_as_x27_6023_ = _args[4];
lean_object* v_b_6024_ = _args[5];
lean_object* v_a_6025_ = _args[6];
lean_object* v___y_6026_ = _args[7];
lean_object* v___y_6027_ = _args[8];
lean_object* v___y_6028_ = _args[9];
lean_object* v___y_6029_ = _args[10];
lean_object* v___y_6030_ = _args[11];
lean_object* v___y_6031_ = _args[12];
lean_object* v___y_6032_ = _args[13];
lean_object* v___y_6033_ = _args[14];
lean_object* v___y_6034_ = _args[15];
lean_object* v___y_6035_ = _args[16];
_start:
{
uint8_t v___y_78027__boxed_6036_; lean_object* v_res_6037_; 
v___y_78027__boxed_6036_ = lean_unbox(v___y_6021_);
v_res_6037_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6019_, v_snd_6020_, v___y_78027__boxed_6036_, v_as_6022_, v_as_x27_6023_, v_b_6024_, v_a_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec(v___y_6028_);
lean_dec_ref(v___y_6027_);
lean_dec(v___y_6026_);
lean_dec(v_as_x27_6023_);
lean_dec(v_as_6022_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6038_, lean_object* v_val_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_){
_start:
{
lean_object* v___x_6050_; 
v___x_6050_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6038_, v_val_6039_, v___y_6046_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6051_, lean_object* v_val_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6051_, v_val_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6064_, lean_object* v_x_6065_, lean_object* v_x_6066_, lean_object* v_x_6067_){
_start:
{
lean_object* v___x_6068_; 
v___x_6068_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6065_, v_x_6066_, v_x_6067_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6069_, lean_object* v_x_6070_, size_t v_x_6071_, size_t v_x_6072_, lean_object* v_x_6073_, lean_object* v_x_6074_){
_start:
{
lean_object* v___x_6075_; 
v___x_6075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6070_, v_x_6071_, v_x_6072_, v_x_6073_, v_x_6074_);
return v___x_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6076_, lean_object* v_x_6077_, lean_object* v_x_6078_, lean_object* v_x_6079_, lean_object* v_x_6080_, lean_object* v_x_6081_){
_start:
{
size_t v_x_78108__boxed_6082_; size_t v_x_78109__boxed_6083_; lean_object* v_res_6084_; 
v_x_78108__boxed_6082_ = lean_unbox_usize(v_x_6078_);
lean_dec(v_x_6078_);
v_x_78109__boxed_6083_ = lean_unbox_usize(v_x_6079_);
lean_dec(v_x_6079_);
v_res_6084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6076_, v_x_6077_, v_x_78108__boxed_6082_, v_x_78109__boxed_6083_, v_x_6080_, v_x_6081_);
return v_res_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6085_, lean_object* v_n_6086_, lean_object* v_k_6087_, lean_object* v_v_6088_){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6086_, v_k_6087_, v_v_6088_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6090_, size_t v_depth_6091_, lean_object* v_keys_6092_, lean_object* v_vals_6093_, lean_object* v_heq_6094_, lean_object* v_i_6095_, lean_object* v_entries_6096_){
_start:
{
lean_object* v___x_6097_; 
v___x_6097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6091_, v_keys_6092_, v_vals_6093_, v_i_6095_, v_entries_6096_);
return v___x_6097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6098_, lean_object* v_depth_6099_, lean_object* v_keys_6100_, lean_object* v_vals_6101_, lean_object* v_heq_6102_, lean_object* v_i_6103_, lean_object* v_entries_6104_){
_start:
{
size_t v_depth_boxed_6105_; lean_object* v_res_6106_; 
v_depth_boxed_6105_ = lean_unbox_usize(v_depth_6099_);
lean_dec(v_depth_6099_);
v_res_6106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6098_, v_depth_boxed_6105_, v_keys_6100_, v_vals_6101_, v_heq_6102_, v_i_6103_, v_entries_6104_);
lean_dec_ref(v_vals_6101_);
lean_dec_ref(v_keys_6100_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6107_, lean_object* v_x_6108_, lean_object* v_x_6109_, lean_object* v_x_6110_, lean_object* v_x_6111_){
_start:
{
lean_object* v___x_6112_; 
v___x_6112_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6108_, v_x_6109_, v_x_6110_, v_x_6111_);
return v___x_6112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6124_ = lean_st_mk_ref(v_goal_6113_);
v___x_6125_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6124_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
if (lean_obj_tag(v___x_6125_) == 0)
{
lean_object* v_a_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6135_; 
v_a_6126_ = lean_ctor_get(v___x_6125_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_6125_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6128_ = v___x_6125_;
v_isShared_6129_ = v_isSharedCheck_6135_;
goto v_resetjp_6127_;
}
else
{
lean_inc(v_a_6126_);
lean_dec(v___x_6125_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6135_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6133_; 
v___x_6130_ = lean_st_ref_get(v___x_6124_);
lean_dec(v___x_6124_);
v___x_6131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6131_, 0, v_a_6126_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
if (v_isShared_6129_ == 0)
{
lean_ctor_set(v___x_6128_, 0, v___x_6131_);
v___x_6133_ = v___x_6128_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v___x_6131_);
v___x_6133_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
return v___x_6133_;
}
}
}
else
{
lean_object* v_a_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6143_; 
lean_dec(v___x_6124_);
v_a_6136_ = lean_ctor_get(v___x_6125_, 0);
v_isSharedCheck_6143_ = !lean_is_exclusive(v___x_6125_);
if (v_isSharedCheck_6143_ == 0)
{
v___x_6138_ = v___x_6125_;
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_a_6136_);
lean_dec(v___x_6125_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v___x_6141_; 
if (v_isShared_6139_ == 0)
{
v___x_6141_ = v___x_6138_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
v___x_6141_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
return v___x_6141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
lean_object* v_res_6155_; 
v_res_6155_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
lean_dec(v___y_6151_);
lean_dec_ref(v___y_6150_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_){
_start:
{
lean_object* v___x_6169_; 
v___x_6169_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6156_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6171_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6184_, lean_object* v___f_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6199_, 0, v___y_6184_);
v___x_6200_ = l_Lean_Meta_Grind_Action_andThen(v___x_6199_, v___f_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6201_, lean_object* v___f_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6201_, v___f_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
lean_dec(v___y_6214_);
lean_dec_ref(v___y_6213_);
lean_dec(v___y_6212_);
lean_dec_ref(v___y_6211_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6218_, uint8_t v_compress_6219_, lean_object* v_goal_6220_, lean_object* v_kna_6221_, lean_object* v_kp_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_){
_start:
{
lean_object* v_toGoalState_6233_; lean_object* v_mvarId_6234_; lean_object* v___f_6235_; lean_object* v___x_6236_; 
v_toGoalState_6233_ = lean_ctor_get(v_goal_6220_, 0);
lean_inc_ref(v_toGoalState_6233_);
v_mvarId_6234_ = lean_ctor_get(v_goal_6220_, 1);
lean_inc(v_mvarId_6234_);
v___f_6235_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_6235_, 0, v_goal_6220_);
v___x_6236_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6234_, v___f_6235_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v_a_6237_; lean_object* v_fst_6238_; 
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
lean_inc(v_a_6237_);
lean_dec_ref_known(v___x_6236_, 1);
v_fst_6238_ = lean_ctor_get(v_a_6237_, 0);
if (lean_obj_tag(v_fst_6238_) == 1)
{
lean_object* v_split_6239_; lean_object* v_snd_6240_; lean_object* v_c_6241_; lean_object* v_numCases_6242_; uint8_t v_isRec_6243_; lean_object* v_candidates_6244_; lean_object* v___f_6245_; lean_object* v___y_6247_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; uint8_t v___y_6259_; uint8_t v___x_6261_; 
lean_inc_ref(v_fst_6238_);
v_split_6239_ = lean_ctor_get(v_toGoalState_6233_, 14);
lean_inc_ref(v_split_6239_);
lean_dec_ref(v_toGoalState_6233_);
v_snd_6240_ = lean_ctor_get(v_a_6237_, 1);
lean_inc(v_snd_6240_);
lean_dec(v_a_6237_);
v_c_6241_ = lean_ctor_get(v_fst_6238_, 0);
lean_inc_ref(v_c_6241_);
v_numCases_6242_ = lean_ctor_get(v_fst_6238_, 1);
lean_inc(v_numCases_6242_);
v_isRec_6243_ = lean_ctor_get_uint8(v_fst_6238_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6238_, 2);
v_candidates_6244_ = lean_ctor_get(v_split_6239_, 1);
lean_inc(v_candidates_6244_);
lean_dec_ref(v_split_6239_);
v___f_6245_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_6255_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6241_);
v___x_6256_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6240_, v___x_6255_);
lean_dec_ref(v___x_6255_);
v___x_6257_ = lean_unsigned_to_nat(1u);
v___x_6261_ = lean_nat_dec_lt(v___x_6257_, v_numCases_6242_);
if (v___x_6261_ == 0)
{
v___y_6259_ = v_isRec_6243_;
goto v___jp_6258_;
}
else
{
v___y_6259_ = v___x_6261_;
goto v___jp_6258_;
}
v___jp_6246_:
{
lean_object* v___f_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v___f_6248_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6248_, 0, v___y_6247_);
lean_closure_set(v___f_6248_, 1, v___f_6245_);
v___x_6249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6249_, 0, v_candidates_6244_);
v___x_6250_ = lean_box(v_isRec_6243_);
v___x_6251_ = lean_box(v_stopAtFirstFailure_6218_);
v___x_6252_ = lean_box(v_compress_6219_);
v___x_6253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6253_, 0, v_c_6241_);
lean_closure_set(v___x_6253_, 1, v_numCases_6242_);
lean_closure_set(v___x_6253_, 2, v___x_6250_);
lean_closure_set(v___x_6253_, 3, v___x_6251_);
lean_closure_set(v___x_6253_, 4, v___x_6252_);
lean_closure_set(v___x_6253_, 5, v___x_6249_);
v___x_6254_ = l_Lean_Meta_Grind_Action_andThen(v___x_6253_, v___f_6248_, v_snd_6240_, v_kna_6221_, v_kp_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_);
return v___x_6254_;
}
v___jp_6258_:
{
if (v___y_6259_ == 0)
{
v___y_6247_ = v___x_6256_;
goto v___jp_6246_;
}
else
{
lean_object* v___x_6260_; 
v___x_6260_ = lean_nat_add(v___x_6256_, v___x_6257_);
lean_dec(v___x_6256_);
v___y_6247_ = v___x_6260_;
goto v___jp_6246_;
}
}
}
else
{
lean_object* v_snd_6262_; lean_object* v___x_6263_; 
lean_dec_ref(v_toGoalState_6233_);
lean_dec_ref(v_kp_6222_);
v_snd_6262_ = lean_ctor_get(v_a_6237_, 1);
lean_inc(v_snd_6262_);
lean_dec(v_a_6237_);
lean_inc(v_a_6231_);
lean_inc_ref(v_a_6230_);
lean_inc(v_a_6229_);
lean_inc_ref(v_a_6228_);
lean_inc(v_a_6227_);
lean_inc_ref(v_a_6226_);
lean_inc(v_a_6225_);
lean_inc_ref(v_a_6224_);
lean_inc(v_a_6223_);
v___x_6263_ = lean_apply_11(v_kna_6221_, v_snd_6262_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_, lean_box(0));
return v___x_6263_;
}
}
else
{
lean_object* v_a_6264_; lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6271_; 
lean_dec_ref(v_toGoalState_6233_);
lean_dec_ref(v_kp_6222_);
lean_dec_ref(v_kna_6221_);
v_a_6264_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6271_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6271_ == 0)
{
v___x_6266_ = v___x_6236_;
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
else
{
lean_inc(v_a_6264_);
lean_dec(v___x_6236_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6269_; 
if (v_isShared_6267_ == 0)
{
v___x_6269_ = v___x_6266_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_a_6264_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6272_, lean_object* v_compress_6273_, lean_object* v_goal_6274_, lean_object* v_kna_6275_, lean_object* v_kp_6276_, lean_object* v_a_6277_, lean_object* v_a_6278_, lean_object* v_a_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_, lean_object* v_a_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_, lean_object* v_a_6285_, lean_object* v_a_6286_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6287_; uint8_t v_compress_boxed_6288_; lean_object* v_res_6289_; 
v_stopAtFirstFailure_boxed_6287_ = lean_unbox(v_stopAtFirstFailure_6272_);
v_compress_boxed_6288_ = lean_unbox(v_compress_6273_);
v_res_6289_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6287_, v_compress_boxed_6288_, v_goal_6274_, v_kna_6275_, v_kp_6276_, v_a_6277_, v_a_6278_, v_a_6279_, v_a_6280_, v_a_6281_, v_a_6282_, v_a_6283_, v_a_6284_, v_a_6285_);
lean_dec(v_a_6285_);
lean_dec_ref(v_a_6284_);
lean_dec(v_a_6283_);
lean_dec_ref(v_a_6282_);
lean_dec(v_a_6281_);
lean_dec_ref(v_a_6280_);
lean_dec(v_a_6279_);
lean_dec_ref(v_a_6278_);
lean_dec(v_a_6277_);
return v_res_6289_;
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
