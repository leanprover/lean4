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
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; lean_object* v_mctx_1188_; lean_object* v_lctx_1189_; lean_object* v_options_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1185_ = lean_st_ref_get(v___y_1183_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_st_ref_get(v___y_1181_);
v_mctx_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_mctx_1188_);
lean_dec(v___x_1187_);
v_lctx_1189_ = lean_ctor_get(v___y_1180_, 2);
v_options_1190_ = lean_ctor_get(v___y_1182_, 2);
lean_inc_ref(v_options_1190_);
lean_inc_ref(v_lctx_1189_);
v___x_1191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1191_, 0, v_env_1186_);
lean_ctor_set(v___x_1191_, 1, v_mctx_1188_);
lean_ctor_set(v___x_1191_, 2, v_lctx_1189_);
lean_ctor_set(v___x_1191_, 3, v_options_1190_);
v___x_1192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_msgData_1179_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_ref_1207_ = lean_ctor_get(v___y_1204_, 5);
v___x_1208_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_inc(v_ref_1207_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_ref_1207_);
lean_ctor_set(v___x_1213_, 1, v_a_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 1);
lean_ctor_set(v___x_1211_, 0, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_fileName_1238_; lean_object* v_fileMap_1239_; lean_object* v_options_1240_; lean_object* v_currRecDepth_1241_; lean_object* v_maxRecDepth_1242_; lean_object* v_ref_1243_; lean_object* v_currNamespace_1244_; lean_object* v_openDecls_1245_; lean_object* v_initHeartbeats_1246_; lean_object* v_maxHeartbeats_1247_; lean_object* v_quotContext_1248_; lean_object* v_currMacroScope_1249_; uint8_t v_diag_1250_; lean_object* v_cancelTk_x3f_1251_; uint8_t v_suppressElabErrors_1252_; lean_object* v_inheritedTraceOptions_1253_; lean_object* v_ref_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_fileName_1238_ = lean_ctor_get(v___y_1235_, 0);
v_fileMap_1239_ = lean_ctor_get(v___y_1235_, 1);
v_options_1240_ = lean_ctor_get(v___y_1235_, 2);
v_currRecDepth_1241_ = lean_ctor_get(v___y_1235_, 3);
v_maxRecDepth_1242_ = lean_ctor_get(v___y_1235_, 4);
v_ref_1243_ = lean_ctor_get(v___y_1235_, 5);
v_currNamespace_1244_ = lean_ctor_get(v___y_1235_, 6);
v_openDecls_1245_ = lean_ctor_get(v___y_1235_, 7);
v_initHeartbeats_1246_ = lean_ctor_get(v___y_1235_, 8);
v_maxHeartbeats_1247_ = lean_ctor_get(v___y_1235_, 9);
v_quotContext_1248_ = lean_ctor_get(v___y_1235_, 10);
v_currMacroScope_1249_ = lean_ctor_get(v___y_1235_, 11);
v_diag_1250_ = lean_ctor_get_uint8(v___y_1235_, sizeof(void*)*14);
v_cancelTk_x3f_1251_ = lean_ctor_get(v___y_1235_, 12);
v_suppressElabErrors_1252_ = lean_ctor_get_uint8(v___y_1235_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1253_ = lean_ctor_get(v___y_1235_, 13);
v_ref_1254_ = l_Lean_replaceRef(v_ref_1225_, v_ref_1243_);
lean_inc_ref(v_inheritedTraceOptions_1253_);
lean_inc(v_cancelTk_x3f_1251_);
lean_inc(v_currMacroScope_1249_);
lean_inc(v_quotContext_1248_);
lean_inc(v_maxHeartbeats_1247_);
lean_inc(v_initHeartbeats_1246_);
lean_inc(v_openDecls_1245_);
lean_inc(v_currNamespace_1244_);
lean_inc(v_maxRecDepth_1242_);
lean_inc(v_currRecDepth_1241_);
lean_inc_ref(v_options_1240_);
lean_inc_ref(v_fileMap_1239_);
lean_inc_ref(v_fileName_1238_);
v___x_1255_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1255_, 0, v_fileName_1238_);
lean_ctor_set(v___x_1255_, 1, v_fileMap_1239_);
lean_ctor_set(v___x_1255_, 2, v_options_1240_);
lean_ctor_set(v___x_1255_, 3, v_currRecDepth_1241_);
lean_ctor_set(v___x_1255_, 4, v_maxRecDepth_1242_);
lean_ctor_set(v___x_1255_, 5, v_ref_1254_);
lean_ctor_set(v___x_1255_, 6, v_currNamespace_1244_);
lean_ctor_set(v___x_1255_, 7, v_openDecls_1245_);
lean_ctor_set(v___x_1255_, 8, v_initHeartbeats_1246_);
lean_ctor_set(v___x_1255_, 9, v_maxHeartbeats_1247_);
lean_ctor_set(v___x_1255_, 10, v_quotContext_1248_);
lean_ctor_set(v___x_1255_, 11, v_currMacroScope_1249_);
lean_ctor_set(v___x_1255_, 12, v_cancelTk_x3f_1251_);
lean_ctor_set(v___x_1255_, 13, v_inheritedTraceOptions_1253_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*14, v_diag_1250_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*14 + 1, v_suppressElabErrors_1252_);
v___x_1256_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1226_, v___y_1233_, v___y_1234_, v___x_1255_, v___y_1236_);
lean_dec_ref_known(v___x_1255_, 14);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1257_, lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1257_, v_msg_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec(v_ref_1257_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1271_, lean_object* v_msg_1272_, lean_object* v_declHint_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; lean_object* v_a_1286_; lean_object* v___x_1287_; 
v___x_1285_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1272_, v_declHint_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1271_, v_a_1286_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1288_, lean_object* v_msg_1289_, lean_object* v_declHint_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1288_, v_msg_1289_, v_declHint_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec(v_ref_1288_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1309_, lean_object* v_constName_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1322_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1323_ = 0;
lean_inc(v_constName_1310_);
v___x_1324_ = l_Lean_MessageData_ofConstName(v_constName_1310_, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1322_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1309_, v___x_1327_, v_constName_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1329_, lean_object* v_constName_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1329_, v_constName_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v_ref_1329_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_ref_1355_; lean_object* v___x_1356_; 
v_ref_1355_ = lean_ctor_get(v___y_1352_, 5);
v___x_1356_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1355_, v_constName_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec(v___y_1358_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_env_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_st_ref_get(v___y_1380_);
v_env_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_env_1383_);
lean_dec(v___x_1382_);
v___x_1384_ = 0;
lean_inc(v_constName_1370_);
v___x_1385_ = l_Lean_Environment_find_x3f(v_env_1383_, v_constName_1370_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_constName_1370_);
v_val_1387_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 0);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1407_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1408_; double v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_float_of_nat(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_ref_1420_; lean_object* v___x_1421_; lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1466_; 
v_ref_1420_ = lean_ctor_get(v___y_1417_, 5);
v___x_1421_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1466_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1466_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v_traceState_1427_; lean_object* v_env_1428_; lean_object* v_nextMacroScope_1429_; lean_object* v_ngen_1430_; lean_object* v_auxDeclNGen_1431_; lean_object* v_cache_1432_; lean_object* v_messages_1433_; lean_object* v_infoState_1434_; lean_object* v_snapshotTasks_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1465_; 
v___x_1426_ = lean_st_ref_take(v___y_1418_);
v_traceState_1427_ = lean_ctor_get(v___x_1426_, 4);
v_env_1428_ = lean_ctor_get(v___x_1426_, 0);
v_nextMacroScope_1429_ = lean_ctor_get(v___x_1426_, 1);
v_ngen_1430_ = lean_ctor_get(v___x_1426_, 2);
v_auxDeclNGen_1431_ = lean_ctor_get(v___x_1426_, 3);
v_cache_1432_ = lean_ctor_get(v___x_1426_, 5);
v_messages_1433_ = lean_ctor_get(v___x_1426_, 6);
v_infoState_1434_ = lean_ctor_get(v___x_1426_, 7);
v_snapshotTasks_1435_ = lean_ctor_get(v___x_1426_, 8);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1437_ = v___x_1426_;
v_isShared_1438_ = v_isSharedCheck_1465_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snapshotTasks_1435_);
lean_inc(v_infoState_1434_);
lean_inc(v_messages_1433_);
lean_inc(v_cache_1432_);
lean_inc(v_traceState_1427_);
lean_inc(v_auxDeclNGen_1431_);
lean_inc(v_ngen_1430_);
lean_inc(v_nextMacroScope_1429_);
lean_inc(v_env_1428_);
lean_dec(v___x_1426_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1465_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint64_t v_tid_1439_; lean_object* v_traces_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1464_; 
v_tid_1439_ = lean_ctor_get_uint64(v_traceState_1427_, sizeof(void*)*1);
v_traces_1440_ = lean_ctor_get(v_traceState_1427_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_traceState_1427_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1442_ = v_traceState_1427_;
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_traces_1440_);
lean_dec(v_traceState_1427_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; double v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1446_ = 0;
v___x_1447_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1448_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1448_, 0, v_cls_1413_);
lean_ctor_set(v___x_1448_, 1, v___x_1444_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
lean_ctor_set_float(v___x_1448_, sizeof(void*)*3, v___x_1445_);
lean_ctor_set_float(v___x_1448_, sizeof(void*)*3 + 8, v___x_1445_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*3 + 16, v___x_1446_);
v___x_1449_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1450_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v_a_1422_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_inc(v_ref_1420_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_ref_1420_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_PersistentArray_push___redArg(v_traces_1440_, v___x_1451_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1452_);
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1452_);
lean_ctor_set_uint64(v_reuseFailAlloc_1463_, sizeof(void*)*1, v_tid_1439_);
v___x_1454_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v___x_1454_);
v___x_1456_ = v___x_1437_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_env_1428_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_nextMacroScope_1429_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_ngen_1430_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_auxDeclNGen_1431_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_cache_1432_);
lean_ctor_set(v_reuseFailAlloc_1462_, 6, v_messages_1433_);
lean_ctor_set(v_reuseFailAlloc_1462_, 7, v_infoState_1434_);
lean_ctor_set(v_reuseFailAlloc_1462_, 8, v_snapshotTasks_1435_);
v___x_1456_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1457_ = lean_st_ref_put(v___y_1418_, v___x_1456_);
v___x_1458_ = lean_box(0);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1458_);
v___x_1460_ = v___x_1424_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1467_, v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1493_ = l_Lean_Name_append(v___x_1492_, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
uint8_t v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; uint8_t v___y_1644_; lean_object* v___x_1758_; 
lean_inc_ref(v_e_1506_);
v___x_1758_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1506_, v_a_1514_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1800_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1800_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1800_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = l_Lean_Expr_cleanupAnnotations(v_a_1759_);
v___x_1777_ = l_Lean_Expr_isApp(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___x_1776_);
lean_del_object(v___x_1761_);
v___y_1764_ = v_a_1507_;
v___y_1765_ = v_a_1508_;
v___y_1766_ = v_a_1509_;
v___y_1767_ = v_a_1510_;
v___y_1768_ = v_a_1511_;
v___y_1769_ = v_a_1512_;
v___y_1770_ = v_a_1513_;
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
goto v___jp_1763_;
}
else
{
lean_object* v_arg_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_arg_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc_ref(v_arg_1778_);
v___x_1779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1776_);
v___x_1780_ = l_Lean_Expr_isApp(v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_arg_1778_);
lean_del_object(v___x_1761_);
v___y_1764_ = v_a_1507_;
v___y_1765_ = v_a_1508_;
v___y_1766_ = v_a_1509_;
v___y_1767_ = v_a_1510_;
v___y_1768_ = v_a_1511_;
v___y_1769_ = v_a_1512_;
v___y_1770_ = v_a_1513_;
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
goto v___jp_1763_;
}
else
{
lean_object* v_arg_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_arg_1781_ = lean_ctor_get(v___x_1779_, 1);
lean_inc_ref(v_arg_1781_);
v___x_1782_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1779_);
v___x_1783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1784_ = l_Lean_Expr_isConstOf(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1786_ = l_Lean_Expr_isConstOf(v___x_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Expr_isApp(v___x_1782_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1782_);
lean_dec_ref(v_arg_1781_);
lean_dec_ref(v_arg_1778_);
lean_del_object(v___x_1761_);
v___y_1764_ = v_a_1507_;
v___y_1765_ = v_a_1508_;
v___y_1766_ = v_a_1509_;
v___y_1767_ = v_a_1510_;
v___y_1768_ = v_a_1511_;
v___y_1769_ = v_a_1512_;
v___y_1770_ = v_a_1513_;
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1782_);
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1790_ = l_Lean_Expr_isConstOf(v___x_1788_, v___x_1789_);
lean_dec_ref(v___x_1788_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v_arg_1781_);
lean_dec_ref(v_arg_1778_);
lean_del_object(v___x_1761_);
v___y_1764_ = v_a_1507_;
v___y_1765_ = v_a_1508_;
v___y_1766_ = v_a_1509_;
v___y_1767_ = v_a_1510_;
v___y_1768_ = v_a_1511_;
v___y_1769_ = v_a_1512_;
v___y_1770_ = v_a_1513_;
v___y_1771_ = v_a_1514_;
v___y_1772_ = v_a_1515_;
v___y_1773_ = v_a_1516_;
goto v___jp_1763_;
}
else
{
uint8_t v___x_1791_; 
lean_inc_ref(v_e_1506_);
v___x_1791_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1506_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec_ref(v_arg_1781_);
lean_dec_ref(v_arg_1778_);
lean_dec_ref(v_e_1506_);
v___x_1792_ = lean_unsigned_to_nat(2u);
v___x_1793_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*1, v___x_1791_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*1 + 1, v___x_1791_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1793_);
v___x_1795_ = v___x_1761_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
else
{
lean_object* v___x_1797_; 
lean_del_object(v___x_1761_);
v___x_1797_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1506_, v_arg_1781_, v_arg_1778_, v_a_1507_, v_a_1511_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v___x_1782_);
lean_del_object(v___x_1761_);
v___x_1798_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1506_, v_arg_1781_, v_arg_1778_, v_a_1507_, v_a_1511_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1798_;
}
}
else
{
lean_object* v___x_1799_; 
lean_dec_ref(v___x_1782_);
lean_del_object(v___x_1761_);
v___x_1799_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1506_, v_arg_1781_, v_arg_1778_, v_a_1507_, v_a_1511_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1799_;
}
}
}
v___jp_1763_:
{
uint8_t v___x_1774_; 
v___x_1774_ = l_Lean_Meta_Grind_isIte(v_e_1506_);
if (v___x_1774_ == 0)
{
uint8_t v___x_1775_; 
v___x_1775_ = l_Lean_Meta_Grind_isDIte(v_e_1506_);
v___y_1634_ = v___y_1764_;
v___y_1635_ = v___y_1770_;
v___y_1636_ = v___y_1768_;
v___y_1637_ = v___y_1766_;
v___y_1638_ = v___y_1773_;
v___y_1639_ = v___y_1772_;
v___y_1640_ = v___y_1767_;
v___y_1641_ = v___y_1771_;
v___y_1642_ = v___y_1769_;
v___y_1643_ = v___y_1765_;
v___y_1644_ = v___x_1775_;
goto v___jp_1633_;
}
else
{
v___y_1634_ = v___y_1764_;
v___y_1635_ = v___y_1770_;
v___y_1636_ = v___y_1768_;
v___y_1637_ = v___y_1766_;
v___y_1638_ = v___y_1773_;
v___y_1639_ = v___y_1772_;
v___y_1640_ = v___y_1767_;
v___y_1641_ = v___y_1771_;
v___y_1642_ = v___y_1769_;
v___y_1643_ = v___y_1765_;
v___y_1644_ = v___x_1774_;
goto v___jp_1633_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_e_1506_);
v_a_1801_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1758_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1758_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
v___jp_1518_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
v___jp_1521_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
v___jp_1524_:
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Lean_Expr_isFVar(v_e_1506_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v_e_1506_);
v___x_1537_ = lean_box(1);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; 
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc_ref(v_e_1506_);
v___x_1539_ = lean_infer_type(v_e_1506_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = l_Lean_Meta_whnfD(v_a_1540_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_n(v_a_1542_, 2);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1544_ = l_Lean_MessageData_ofExpr(v_e_1506_);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_indentExpr(v_a_1542_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_Expr_getAppFn(v_a_1542_);
lean_dec(v_a_1542_);
if (lean_obj_tag(v___x_1550_) == 4)
{
lean_object* v_declName_1551_; lean_object* v___x_1552_; 
v_declName_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_declName_1551_);
lean_dec_ref_known(v___x_1550_, 2);
v___x_1552_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1551_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1585_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1585_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1585_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
if (lean_obj_tag(v_a_1553_) == 5)
{
lean_object* v_val_1557_; lean_object* v_ctors_1558_; uint8_t v_isRec_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1549_, 2);
v_val_1557_ = lean_ctor_get(v_a_1553_, 0);
lean_inc_ref(v_val_1557_);
lean_dec_ref_known(v_a_1553_, 1);
v_ctors_1558_ = lean_ctor_get(v_val_1557_, 4);
lean_inc(v_ctors_1558_);
v_isRec_1559_ = lean_ctor_get_uint8(v_val_1557_, sizeof(void*)*6);
lean_dec_ref(v_val_1557_);
v___x_1560_ = l_List_lengthTR___redArg(v_ctors_1558_);
lean_dec(v_ctors_1558_);
v___x_1561_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*1, v_isRec_1559_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*1 + 1, v___y_1525_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1561_);
v___x_1563_ = v___x_1555_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
else
{
lean_object* v___x_1565_; 
lean_del_object(v___x_1555_);
lean_dec(v_a_1553_);
v___x_1565_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1530_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; uint8_t v_verbose_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_verbose_1567_ = lean_ctor_get_uint8(v_a_1566_, 0);
lean_dec(v_a_1566_);
if (v_verbose_1567_ == 0)
{
lean_dec_ref_known(v___x_1549_, 2);
goto v___jp_1521_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_Sym_reportIssue(v___x_1549_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_dec_ref_known(v___x_1568_, 1);
goto v___jp_1521_;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref_known(v___x_1549_, 2);
v_a_1577_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1565_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1565_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref_known(v___x_1549_, 2);
v_a_1586_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1552_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1552_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v___x_1594_; 
lean_dec_ref(v___x_1550_);
v___x_1594_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1530_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; uint8_t v_verbose_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_verbose_1596_ = lean_ctor_get_uint8(v_a_1595_, 0);
lean_dec(v_a_1595_);
if (v_verbose_1596_ == 0)
{
lean_dec_ref_known(v___x_1549_, 2);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_Sym_reportIssue(v___x_1549_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref_known(v___x_1597_, 1);
goto v___jp_1518_;
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref_known(v___x_1549_, 2);
v_a_1606_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1594_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1594_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v_e_1506_);
v_a_1614_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1541_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1541_);
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
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_e_1506_);
v_a_1622_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1539_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1539_);
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
v___jp_1630_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
v___jp_1633_:
{
if (v___y_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1506_, v___y_1634_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; uint8_t v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = lean_unbox(v_a_1646_);
lean_dec(v_a_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_inc_ref(v_e_1506_);
v___x_1648_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1506_, v___y_1634_, v___y_1643_, v___y_1637_, v___y_1640_, v___y_1636_, v___y_1642_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1708_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1708_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1708_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_unbox(v_a_1649_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v_env_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_st_ref_get(v___y_1638_);
v_env_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc_ref(v_env_1655_);
lean_dec(v___x_1654_);
v___x_1656_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1655_, v_e_1506_);
if (lean_obj_tag(v___x_1656_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1663_; 
lean_dec_ref(v_e_1506_);
v_val_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1657_);
lean_dec(v_val_1657_);
v___x_1659_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
v___x_1660_ = lean_unbox(v_a_1649_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*1, v___x_1660_);
v___x_1661_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*1 + 1, v___x_1661_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1659_);
v___x_1663_ = v___x_1651_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1659_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v___x_1656_);
lean_del_object(v___x_1651_);
v___x_1665_ = l_Lean_Expr_getAppFn(v_e_1506_);
if (lean_obj_tag(v___x_1665_) == 4)
{
lean_object* v_declName_1666_; lean_object* v___x_1667_; 
v_declName_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_declName_1666_);
lean_dec_ref_known(v___x_1665_, 2);
v___x_1667_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1666_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
if (lean_obj_tag(v_a_1668_) == 1)
{
lean_object* v_val_1669_; lean_object* v___x_1670_; 
v_val_1669_ = lean_ctor_get(v_a_1668_, 0);
lean_inc(v_val_1669_);
lean_dec_ref_known(v_a_1668_, 1);
lean_inc_ref(v_e_1506_);
v___x_1670_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1506_, v___y_1634_, v___y_1636_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1685_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1685_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_unbox(v_a_1671_);
lean_dec(v_a_1671_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; 
lean_del_object(v___x_1673_);
lean_dec(v_val_1669_);
v___x_1676_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
v___y_1525_ = v___x_1676_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1643_;
v___y_1528_ = v___y_1637_;
v___y_1529_ = v___y_1640_;
v___y_1530_ = v___y_1636_;
v___y_1531_ = v___y_1642_;
v___y_1532_ = v___y_1635_;
v___y_1533_ = v___y_1641_;
v___y_1534_ = v___y_1639_;
v___y_1535_ = v___y_1638_;
goto v___jp_1524_;
}
else
{
lean_object* v_ctors_1677_; uint8_t v_isRec_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; lean_object* v___x_1683_; 
lean_dec_ref(v_e_1506_);
v_ctors_1677_ = lean_ctor_get(v_val_1669_, 4);
lean_inc(v_ctors_1677_);
v_isRec_1678_ = lean_ctor_get_uint8(v_val_1669_, sizeof(void*)*6);
lean_dec(v_val_1669_);
v___x_1679_ = l_List_lengthTR___redArg(v_ctors_1677_);
lean_dec(v_ctors_1677_);
v___x_1680_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*1, v_isRec_1678_);
v___x_1681_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*1 + 1, v___x_1681_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1680_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1680_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_val_1669_);
lean_dec(v_a_1649_);
lean_dec_ref(v_e_1506_);
v_a_1686_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1670_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1670_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
uint8_t v___x_1694_; 
lean_dec(v_a_1668_);
v___x_1694_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
v___y_1525_ = v___x_1694_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1643_;
v___y_1528_ = v___y_1637_;
v___y_1529_ = v___y_1640_;
v___y_1530_ = v___y_1636_;
v___y_1531_ = v___y_1642_;
v___y_1532_ = v___y_1635_;
v___y_1533_ = v___y_1641_;
v___y_1534_ = v___y_1639_;
v___y_1535_ = v___y_1638_;
goto v___jp_1524_;
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1649_);
lean_dec_ref(v_e_1506_);
v_a_1695_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1667_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1667_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
uint8_t v___x_1703_; 
lean_dec_ref(v___x_1665_);
v___x_1703_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
v___y_1525_ = v___x_1703_;
v___y_1526_ = v___y_1634_;
v___y_1527_ = v___y_1643_;
v___y_1528_ = v___y_1637_;
v___y_1529_ = v___y_1640_;
v___y_1530_ = v___y_1636_;
v___y_1531_ = v___y_1642_;
v___y_1532_ = v___y_1635_;
v___y_1533_ = v___y_1641_;
v___y_1534_ = v___y_1639_;
v___y_1535_ = v___y_1638_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_dec(v_a_1649_);
lean_dec_ref(v_e_1506_);
v___x_1704_ = lean_box(0);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1704_);
v___x_1706_ = v___x_1651_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v_e_1506_);
v_a_1709_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1648_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1648_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_options_1717_; uint8_t v_hasTrace_1718_; 
v_options_1717_ = lean_ctor_get(v___y_1639_, 2);
v_hasTrace_1718_ = lean_ctor_get_uint8(v_options_1717_, sizeof(void*)*1);
if (v_hasTrace_1718_ == 0)
{
lean_dec_ref(v_e_1506_);
goto v___jp_1630_;
}
else
{
lean_object* v_inheritedTraceOptions_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_inheritedTraceOptions_1719_ = lean_ctor_get(v___y_1639_, 13);
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1721_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1719_, v_options_1717_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v_e_1506_);
goto v___jp_1630_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Meta_Grind_updateLastTag(v___y_1634_, v___y_1643_, v___y_1637_, v___y_1640_, v___y_1636_, v___y_1642_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1725_ = l_Lean_MessageData_ofExpr(v_e_1506_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1720_, v___x_1726_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_dec_ref_known(v___x_1727_, 1);
goto v___jp_1630_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v_e_1506_);
v_a_1736_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1723_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1723_);
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
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v_e_1506_);
v_a_1744_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1645_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1645_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
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
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = l_Lean_Expr_getAppNumArgs(v_e_1506_);
v___x_1754_ = lean_nat_sub(v___x_1753_, v___x_1752_);
lean_dec(v___x_1753_);
v___x_1755_ = lean_nat_sub(v___x_1754_, v___x_1752_);
lean_dec(v___x_1754_);
v___x_1756_ = l_Lean_Expr_getRevArg_x21(v_e_1506_, v___x_1755_);
lean_dec_ref(v_e_1506_);
v___x_1757_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1756_, v___y_1634_, v___y_1636_, v___y_1635_, v___y_1641_, v___y_1639_, v___y_1638_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec(v_a_1810_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1822_, lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1822_, v_msg_1823_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1836_, v_msg_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec(v___y_1838_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1850_, lean_object* v_constName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_constName_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1864_, v_constName_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1878_, lean_object* v_ref_1879_, lean_object* v_constName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1879_, v_constName_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1893_, lean_object* v_ref_1894_, lean_object* v_constName_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1893_, v_ref_1894_, v_constName_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
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
lean_dec(v_ref_1894_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1908_, lean_object* v_ref_1909_, lean_object* v_msg_1910_, lean_object* v_declHint_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1909_, v_msg_1910_, v_declHint_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_ref_1925_, lean_object* v_msg_1926_, lean_object* v_declHint_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1924_, v_ref_1925_, v_msg_1926_, v_declHint_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v_ref_1925_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1940_, lean_object* v_declHint_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1940_, v_declHint_1941_, v___y_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1954_, lean_object* v_declHint_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1954_, v_declHint_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
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
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1968_, lean_object* v_ref_1969_, lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1969_, v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_ref_1984_, lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1983_, v_ref_1984_, v_msg_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec(v_ref_1984_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1998_, lean_object* v_msg_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1999_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2012_, v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_box(0);
return v___x_2028_;
}
else
{
lean_object* v_key_2029_; lean_object* v_value_2030_; lean_object* v_tail_2031_; uint8_t v___y_2033_; lean_object* v_fst_2036_; lean_object* v_snd_2037_; lean_object* v_fst_2038_; lean_object* v_snd_2039_; uint8_t v___x_2040_; 
v_key_2029_ = lean_ctor_get(v_x_2027_, 0);
v_value_2030_ = lean_ctor_get(v_x_2027_, 1);
v_tail_2031_ = lean_ctor_get(v_x_2027_, 2);
v_fst_2036_ = lean_ctor_get(v_key_2029_, 0);
v_snd_2037_ = lean_ctor_get(v_key_2029_, 1);
v_fst_2038_ = lean_ctor_get(v_a_2026_, 0);
v_snd_2039_ = lean_ctor_get(v_a_2026_, 1);
v___x_2040_ = lean_expr_eqv(v_fst_2036_, v_fst_2038_);
if (v___x_2040_ == 0)
{
v___y_2033_ = v___x_2040_;
goto v___jp_2032_;
}
else
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_expr_eqv(v_snd_2037_, v_snd_2039_);
v___y_2033_ = v___x_2041_;
goto v___jp_2032_;
}
v___jp_2032_:
{
if (v___y_2033_ == 0)
{
v_x_2027_ = v_tail_2031_;
goto _start;
}
else
{
lean_object* v___x_2035_; 
lean_inc(v_value_2030_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_value_2030_);
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2042_, v_x_2043_);
lean_dec(v_x_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_buckets_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; uint64_t v___x_2051_; uint64_t v___x_2052_; uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; uint64_t v_fold_2056_; uint64_t v___x_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_buckets_2047_ = lean_ctor_get(v_m_2045_, 1);
v_fst_2048_ = lean_ctor_get(v_a_2046_, 0);
v_snd_2049_ = lean_ctor_get(v_a_2046_, 1);
v___x_2050_ = lean_array_get_size(v_buckets_2047_);
v___x_2051_ = l_Lean_Expr_hash(v_fst_2048_);
v___x_2052_ = l_Lean_Expr_hash(v_snd_2049_);
v___x_2053_ = lean_uint64_mix_hash(v___x_2051_, v___x_2052_);
v___x_2054_ = 32ULL;
v___x_2055_ = lean_uint64_shift_right(v___x_2053_, v___x_2054_);
v_fold_2056_ = lean_uint64_xor(v___x_2053_, v___x_2055_);
v___x_2057_ = 16ULL;
v___x_2058_ = lean_uint64_shift_right(v_fold_2056_, v___x_2057_);
v___x_2059_ = lean_uint64_xor(v_fold_2056_, v___x_2058_);
v___x_2060_ = lean_uint64_to_usize(v___x_2059_);
v___x_2061_ = lean_usize_of_nat(v___x_2050_);
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_sub(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_usize_land(v___x_2060_, v___x_2063_);
v___x_2065_ = lean_array_uget_borrowed(v_buckets_2047_, v___x_2064_);
v___x_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2046_, v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2067_, v_a_2068_);
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_m_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2070_, uint8_t v___x_2071_, lean_object* v_fst_2072_, lean_object* v_snd_2073_, lean_object* v___x_2074_, lean_object* v_____r_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2087_ = lean_unsigned_to_nat(2u);
v___x_2088_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*1, v_a_2070_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*1 + 1, v___x_2071_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_fst_2072_);
lean_ctor_set(v___x_2090_, 1, v_snd_2073_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2074_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2089_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2095_ = _args[0];
lean_object* v___x_2096_ = _args[1];
lean_object* v_fst_2097_ = _args[2];
lean_object* v_snd_2098_ = _args[3];
lean_object* v___x_2099_ = _args[4];
lean_object* v_____r_2100_ = _args[5];
lean_object* v___y_2101_ = _args[6];
lean_object* v___y_2102_ = _args[7];
lean_object* v___y_2103_ = _args[8];
lean_object* v___y_2104_ = _args[9];
lean_object* v___y_2105_ = _args[10];
lean_object* v___y_2106_ = _args[11];
lean_object* v___y_2107_ = _args[12];
lean_object* v___y_2108_ = _args[13];
lean_object* v___y_2109_ = _args[14];
lean_object* v___y_2110_ = _args[15];
lean_object* v___y_2111_ = _args[16];
_start:
{
uint8_t v_a_33555__boxed_2112_; uint8_t v___x_33556__boxed_2113_; lean_object* v_res_2114_; 
v_a_33555__boxed_2112_ = lean_unbox(v_a_2095_);
v___x_33556__boxed_2113_ = lean_unbox(v___x_2096_);
v_res_2114_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_33555__boxed_2112_, v___x_33556__boxed_2113_, v_fst_2097_, v_snd_2098_, v___x_2099_, v_____r_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec(v___y_2101_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2115_, lean_object* v_snd_2116_, lean_object* v___x_2117_, lean_object* v___x_2118_, lean_object* v_____r_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2131_ = l_Lean_Expr_appFn_x21(v_fst_2115_);
v___x_2132_ = l_Lean_Expr_appFn_x21(v_snd_2116_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2117_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2118_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2138_, lean_object* v_snd_2139_, lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v_____r_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2138_, v_snd_2139_, v___x_2140_, v___x_2141_, v_____r_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec(v_snd_2139_);
lean_dec(v_fst_2138_);
return v_res_2154_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___f_2156_; 
v___x_2155_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2156_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2156_, 0, v___x_2155_);
return v___f_2156_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2162_ = l_Lean_Name_append(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2168_ = l_Lean_stringToMessageData(v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2180_ = l_Lean_stringToMessageData(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2181_, lean_object* v___y_2182_, lean_object* v_eq_2183_, lean_object* v_a_2184_, lean_object* v_b_2185_, lean_object* v_a_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___y_2199_; lean_object* v_snd_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2341_; 
v_snd_2219_ = lean_ctor_get(v_a_2186_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_a_2186_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v_a_2186_, 0);
lean_dec(v_unused_2342_);
v___x_2221_ = v_a_2186_;
v_isShared_2222_ = v_isSharedCheck_2341_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_snd_2219_);
lean_dec(v_a_2186_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2341_;
goto v_resetjp_2220_;
}
v___jp_2198_:
{
if (lean_obj_tag(v___y_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2210_; 
v_a_2200_ = lean_ctor_get(v___y_2199_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___y_2199_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2202_ = v___y_2199_;
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___y_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
if (lean_obj_tag(v_a_2200_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; 
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2204_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v_a_2200_, 1);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_a_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
else
{
lean_object* v_a_2208_; 
lean_del_object(v___x_2202_);
v_a_2208_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v_a_2200_, 1);
v_a_2186_ = v_a_2208_;
goto _start;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2211_ = lean_ctor_get(v___y_2199_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___y_2199_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___y_2199_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___y_2199_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
v_resetjp_2220_:
{
lean_object* v_snd_2223_; lean_object* v_fst_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2340_; 
v_snd_2223_ = lean_ctor_get(v_snd_2219_, 1);
v_fst_2224_ = lean_ctor_get(v_snd_2219_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_snd_2219_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2226_ = v_snd_2219_;
v_isShared_2227_ = v_isSharedCheck_2340_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2224_);
lean_dec(v_snd_2219_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2340_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2339_; 
v_fst_2228_ = lean_ctor_get(v_snd_2223_, 0);
v_snd_2229_ = lean_ctor_get(v_snd_2223_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_snd_2223_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2231_ = v_snd_2223_;
v_isShared_2232_ = v_isSharedCheck_2339_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_inc(v_fst_2228_);
lean_dec(v_snd_2223_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2339_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
uint8_t v___y_2234_; uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_Expr_isApp(v_fst_2228_);
if (v___x_2248_ == 0)
{
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v___y_2234_ = v_a_2181_;
goto v___jp_2233_;
}
else
{
uint8_t v___x_2249_; 
v___x_2249_ = l_Lean_Expr_isApp(v_snd_2229_);
if (v___x_2249_ == 0)
{
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v___y_2234_ = v___x_2249_;
goto v___jp_2233_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___f_2256_; uint8_t v___x_2257_; 
lean_del_object(v___x_2231_);
lean_del_object(v___x_2226_);
lean_del_object(v___x_2221_);
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_sub(v_fst_2224_, v___x_2251_);
lean_dec(v_fst_2224_);
v___f_2256_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2182_);
lean_inc(v___x_2252_);
v___x_2257_ = l_List_elem___redArg(v___f_2256_, v___x_2252_, v___y_2182_);
if (v___x_2257_ == 0)
{
if (v___x_2249_ == 0)
{
goto v___jp_2253_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_Expr_appArg_x21(v_fst_2228_);
v___x_2259_ = l_Lean_Expr_appArg_x21(v_snd_2229_);
v___x_2260_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2258_, v___x_2259_, v___y_2187_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; uint8_t v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = lean_unbox(v_a_2261_);
if (v___x_2262_ == 0)
{
lean_object* v_options_2263_; lean_object* v_inheritedTraceOptions_2264_; uint8_t v_hasTrace_2265_; 
v_options_2263_ = lean_ctor_get(v___y_2195_, 2);
v_inheritedTraceOptions_2264_ = lean_ctor_get(v___y_2195_, 13);
v_hasTrace_2265_ = lean_ctor_get_uint8(v_options_2263_, sizeof(void*)*1);
if (v_hasTrace_2265_ == 0)
{
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
goto v___jp_2266_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2271_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2264_, v_options_2263_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
goto v___jp_2266_;
}
else
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Meta_Grind_updateLastTag(v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; 
lean_dec_ref_known(v___x_2273_, 1);
v___x_2274_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2183_, v___y_2187_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2184_);
v___x_2277_ = l_Lean_MessageData_ofExpr(v_a_2184_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
lean_inc_ref(v_b_2185_);
v___x_2281_ = l_Lean_MessageData_ofExpr(v_b_2185_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
lean_inc_ref(v_eq_2183_);
v___x_2285_ = l_Lean_MessageData_ofExpr(v_eq_2183_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_MessageData_ofExpr(v___x_2258_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_MessageData_ofExpr(v___x_2259_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Nat_reprFast(v_a_2275_);
v___x_2298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
v___x_2299_ = l_Lean_MessageData_ofFormat(v___x_2298_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2296_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2270_, v___x_2300_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = lean_unbox(v_a_2261_);
lean_dec(v_a_2261_);
v___x_2304_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2303_, v___x_2249_, v_fst_2228_, v_snd_2229_, v___x_2252_, v_a_2302_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
v___y_2199_ = v___x_2304_;
goto v___jp_2198_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2261_);
lean_dec(v___x_2252_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2305_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2301_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2301_);
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
lean_dec(v_a_2261_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec(v___x_2252_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2313_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2274_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2274_);
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
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2261_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec(v___x_2252_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2321_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2273_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2273_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
v___jp_2266_:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_unbox(v_a_2261_);
lean_dec(v_a_2261_);
v___x_2269_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2268_, v___x_2249_, v_fst_2228_, v_snd_2229_, v___x_2252_, v___x_2267_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
v___y_2199_ = v___x_2269_;
goto v___jp_2198_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_dec(v_a_2261_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2228_, v_snd_2229_, v___x_2252_, v___x_2250_, v___x_2329_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
v___y_2199_ = v___x_2330_;
goto v___jp_2198_;
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec(v___x_2252_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
lean_dec_ref(v_b_2185_);
lean_dec_ref(v_a_2184_);
lean_dec_ref(v_eq_2183_);
lean_dec(v___y_2182_);
v_a_2331_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2260_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2260_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
else
{
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2228_, v_snd_2229_, v___x_2252_, v___x_2250_, v___x_2254_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v_snd_2229_);
lean_dec(v_fst_2228_);
v___y_2199_ = v___x_2255_;
goto v___jp_2198_;
}
}
}
v___jp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2235_ = lean_unsigned_to_nat(2u);
v___x_2236_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1, v___y_2234_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1 + 1, v___y_2234_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
if (v_isShared_2232_ == 0)
{
v___x_2239_ = v___x_2231_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_fst_2228_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_snd_2229_);
v___x_2239_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2239_);
v___x_2241_ = v___x_2226_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_fst_2224_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2241_);
lean_ctor_set(v___x_2221_, 0, v___x_2237_);
v___x_2243_ = v___x_2221_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
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
lean_object* v_a_2343_ = _args[0];
lean_object* v___y_2344_ = _args[1];
lean_object* v_eq_2345_ = _args[2];
lean_object* v_a_2346_ = _args[3];
lean_object* v_b_2347_ = _args[4];
lean_object* v_a_2348_ = _args[5];
lean_object* v___y_2349_ = _args[6];
lean_object* v___y_2350_ = _args[7];
lean_object* v___y_2351_ = _args[8];
lean_object* v___y_2352_ = _args[9];
lean_object* v___y_2353_ = _args[10];
lean_object* v___y_2354_ = _args[11];
lean_object* v___y_2355_ = _args[12];
lean_object* v___y_2356_ = _args[13];
lean_object* v___y_2357_ = _args[14];
lean_object* v___y_2358_ = _args[15];
lean_object* v___y_2359_ = _args[16];
_start:
{
uint8_t v_a_33729__boxed_2360_; lean_object* v_res_2361_; 
v_a_33729__boxed_2360_ = lean_unbox(v_a_2343_);
v_res_2361_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_33729__boxed_2360_, v___y_2344_, v_eq_2345_, v_a_2346_, v_b_2347_, v_a_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec(v___y_2349_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2362_, lean_object* v_b_2363_, lean_object* v_eq_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
uint8_t v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2409_; lean_object* v___x_2445_; 
lean_inc_ref(v_eq_2364_);
v___x_2445_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2364_, v_a_2365_, v_a_2369_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; uint8_t v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
v___x_2447_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref_known(v___x_2445_, 1);
lean_inc_ref(v_eq_2364_);
v___x_2448_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2364_, v_a_2365_, v_a_2369_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
v___y_2409_ = v___x_2448_;
goto v___jp_2408_;
}
else
{
v___y_2409_ = v___x_2445_;
goto v___jp_2408_;
}
}
else
{
v___y_2409_ = v___x_2445_;
goto v___jp_2408_;
}
v___jp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2379_ = l_Lean_Expr_getAppNumArgs(v_a_2362_);
v___x_2380_ = lean_box(0);
lean_inc_ref(v_b_2363_);
lean_inc_ref(v_a_2362_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2362_);
lean_ctor_set(v___x_2381_, 1, v_b_2363_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2377_, v___y_2378_, v_eq_2364_, v_a_2362_, v_b_2363_, v___x_2383_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2399_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2399_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2399_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_fst_2389_; 
v_fst_2389_ = lean_ctor_get(v_a_2385_, 0);
lean_inc(v_fst_2389_);
lean_dec(v_a_2385_);
if (lean_obj_tag(v_fst_2389_) == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = lean_unsigned_to_nat(2u);
v___x_2391_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1, v___y_2377_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1 + 1, v___y_2377_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2391_);
v___x_2393_ = v___x_2387_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
else
{
lean_object* v_val_2395_; lean_object* v___x_2397_; 
v_val_2395_ = lean_ctor_get(v_fst_2389_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v_fst_2389_, 1);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v_val_2395_);
v___x_2397_ = v___x_2387_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_val_2395_);
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
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_a_2400_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2384_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2384_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
v___jp_2408_:
{
if (lean_obj_tag(v___y_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2436_; 
v_a_2410_ = lean_ctor_get(v___y_2409_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___y_2409_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2412_ = v___y_2409_;
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___y_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2436_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_unbox(v_a_2410_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v_toGoalState_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2412_);
v___x_2415_ = lean_st_ref_get(v_a_2365_);
v_toGoalState_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2415_, 1);
lean_dec(v_unused_2431_);
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_toGoalState_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_split_2420_; lean_object* v_argPosMap_2421_; lean_object* v___x_2423_; 
v_split_2420_ = lean_ctor_get(v_toGoalState_2416_, 14);
lean_inc_ref(v_split_2420_);
lean_dec_ref(v_toGoalState_2416_);
v_argPosMap_2421_ = lean_ctor_get(v_split_2420_, 6);
lean_inc_ref(v_argPosMap_2421_);
lean_dec_ref(v_split_2420_);
lean_inc_ref(v_b_2363_);
lean_inc_ref(v_a_2362_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v_b_2363_);
lean_ctor_set(v___x_2418_, 0, v_a_2362_);
v___x_2423_ = v___x_2418_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2362_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_b_2363_);
v___x_2423_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2421_, v___x_2423_);
lean_dec_ref(v___x_2423_);
lean_dec_ref(v_argPosMap_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_unbox(v_a_2410_);
lean_dec(v_a_2410_);
v___y_2377_ = v___x_2426_;
v___y_2378_ = v___x_2425_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2427_; uint8_t v___x_2428_; 
v_val_2427_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2428_ = lean_unbox(v_a_2410_);
lean_dec(v_a_2410_);
v___y_2377_ = v___x_2428_;
v___y_2378_ = v_val_2427_;
goto v___jp_2376_;
}
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec(v_a_2410_);
lean_dec_ref(v_eq_2364_);
lean_dec_ref(v_b_2363_);
lean_dec_ref(v_a_2362_);
v___x_2432_ = lean_box(0);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2432_);
v___x_2434_ = v___x_2412_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
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
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_eq_2364_);
lean_dec_ref(v_b_2363_);
lean_dec_ref(v_a_2362_);
v_a_2437_ = lean_ctor_get(v___y_2409_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___y_2409_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___y_2409_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___y_2409_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2449_, lean_object* v_b_2450_, lean_object* v_eq_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2449_, v_b_2450_, v_eq_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec(v_a_2452_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2464_, lean_object* v___y_2465_, lean_object* v_eq_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_, lean_object* v_inst_2469_, lean_object* v_a_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2464_, v___y_2465_, v_eq_2466_, v_a_2467_, v_b_2468_, v_a_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2483_ = _args[0];
lean_object* v___y_2484_ = _args[1];
lean_object* v_eq_2485_ = _args[2];
lean_object* v_a_2486_ = _args[3];
lean_object* v_b_2487_ = _args[4];
lean_object* v_inst_2488_ = _args[5];
lean_object* v_a_2489_ = _args[6];
lean_object* v___y_2490_ = _args[7];
lean_object* v___y_2491_ = _args[8];
lean_object* v___y_2492_ = _args[9];
lean_object* v___y_2493_ = _args[10];
lean_object* v___y_2494_ = _args[11];
lean_object* v___y_2495_ = _args[12];
lean_object* v___y_2496_ = _args[13];
lean_object* v___y_2497_ = _args[14];
lean_object* v___y_2498_ = _args[15];
lean_object* v___y_2499_ = _args[16];
lean_object* v___y_2500_ = _args[17];
_start:
{
uint8_t v_a_34211__boxed_2501_; lean_object* v_res_2502_; 
v_a_34211__boxed_2501_ = lean_unbox(v_a_2483_);
v_res_2502_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34211__boxed_2501_, v___y_2484_, v_eq_2485_, v_a_2486_, v_b_2487_, v_inst_2488_, v_a_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2503_, lean_object* v_m_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2504_, v_a_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2507_, lean_object* v_m_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2507_, v_m_2508_, v_a_2509_);
lean_dec_ref(v_a_2509_);
lean_dec_ref(v_m_2508_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2511_, lean_object* v_a_2512_, lean_object* v_x_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2512_, v_x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2515_, lean_object* v_a_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2515_, v_a_2516_, v_x_2517_);
lean_dec(v_x_2517_);
lean_dec_ref(v_a_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
uint8_t v___y_2528_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___x_2553_; 
lean_inc_ref(v_imp_2519_);
v___x_2553_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; uint8_t v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = lean_unbox(v_a_2554_);
lean_dec(v_a_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2570_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2570_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2570_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
uint8_t v___x_2561_; 
v___x_2561_ = lean_unbox(v_a_2557_);
lean_dec(v_a_2557_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = lean_box(1);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2562_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_box(0);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2566_);
v___x_2568_ = v___x_2559_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
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
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2571_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2556_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2556_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
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
lean_object* v_binderType_2579_; lean_object* v_body_2580_; lean_object* v___y_2582_; lean_object* v___x_2610_; 
v_binderType_2579_ = lean_ctor_get(v_imp_2519_, 1);
lean_inc_ref_n(v_binderType_2579_, 2);
v_body_2580_ = lean_ctor_get(v_imp_2519_, 2);
lean_inc_ref(v_body_2580_);
lean_dec_ref(v_imp_2519_);
v___x_2610_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2579_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; uint8_t v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
v___x_2612_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec_ref_known(v___x_2610_, 1);
v___x_2613_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2579_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
v___y_2582_ = v___x_2613_;
goto v___jp_2581_;
}
else
{
lean_dec_ref(v_binderType_2579_);
v___y_2582_ = v___x_2610_;
goto v___jp_2581_;
}
}
else
{
lean_dec_ref(v_binderType_2579_);
v___y_2582_ = v___x_2610_;
goto v___jp_2581_;
}
v___jp_2581_:
{
if (lean_obj_tag(v___y_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2601_; 
v_a_2583_ = lean_ctor_get(v___y_2582_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___y_2582_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2585_ = v___y_2582_;
v_isShared_2586_ = v_isSharedCheck_2601_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___y_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2601_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_unbox(v_a_2583_);
if (v___x_2587_ == 0)
{
uint8_t v___x_2588_; 
lean_del_object(v___x_2585_);
v___x_2588_ = l_Lean_Expr_hasLooseBVars(v_body_2580_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
lean_inc_ref(v_body_2580_);
v___x_2589_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2580_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
v___x_2591_ = lean_unbox(v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
lean_dec_ref_known(v___x_2589_, 1);
v___x_2592_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2580_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
v___x_2593_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
v___y_2533_ = v___x_2593_;
v___y_2534_ = v___x_2592_;
goto v___jp_2532_;
}
else
{
uint8_t v___x_2594_; 
lean_dec_ref(v_body_2580_);
v___x_2594_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
v___y_2533_ = v___x_2594_;
v___y_2534_ = v___x_2589_;
goto v___jp_2532_;
}
}
else
{
uint8_t v___x_2595_; 
lean_dec_ref(v_body_2580_);
v___x_2595_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
v___y_2533_ = v___x_2595_;
v___y_2534_ = v___x_2589_;
goto v___jp_2532_;
}
}
else
{
uint8_t v___x_2596_; 
lean_dec_ref(v_body_2580_);
v___x_2596_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
v___y_2528_ = v___x_2596_;
goto v___jp_2527_;
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_dec(v_a_2583_);
lean_dec_ref(v_body_2580_);
v___x_2597_ = lean_box(0);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2597_);
v___x_2599_ = v___x_2585_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
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
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_body_2580_);
v_a_2602_ = lean_ctor_get(v___y_2582_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___y_2582_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___y_2582_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___y_2582_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
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
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v_imp_2519_);
v_a_2614_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2553_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2553_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_unsigned_to_nat(2u);
v___x_2530_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*1, v___y_2528_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*1 + 1, v___y_2528_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
v___jp_2532_:
{
if (lean_obj_tag(v___y_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2544_; 
v_a_2535_ = lean_ctor_get(v___y_2534_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___y_2534_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2537_ = v___y_2534_;
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___y_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_unbox(v_a_2535_);
lean_dec(v_a_2535_);
if (v___x_2539_ == 0)
{
lean_del_object(v___x_2537_);
v___y_2528_ = v___y_2533_;
goto v___jp_2527_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_box(0);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2540_);
v___x_2542_ = v___x_2537_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
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
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___y_2534_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___y_2534_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___y_2534_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___y_2534_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2631_, lean_object* v_h_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2631_, v_a_2633_, v_a_2637_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2645_, lean_object* v_h_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2645_, v_h_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec(v_a_2647_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
switch(lean_obj_tag(v_s_2659_))
{
case 0:
{
lean_object* v_e_2671_; lean_object* v___x_2672_; 
v_e_2671_ = lean_ctor_get(v_s_2659_, 0);
lean_inc_ref(v_e_2671_);
lean_dec_ref_known(v_s_2659_, 2);
v___x_2672_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2671_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2672_;
}
case 1:
{
lean_object* v_e_2673_; lean_object* v___x_2674_; 
v_e_2673_ = lean_ctor_get(v_s_2659_, 0);
lean_inc_ref(v_e_2673_);
lean_dec_ref_known(v_s_2659_, 2);
v___x_2674_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2673_, v_a_2660_, v_a_2664_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2674_;
}
default: 
{
lean_object* v_a_2675_; lean_object* v_b_2676_; lean_object* v_eq_2677_; lean_object* v___x_2678_; 
v_a_2675_ = lean_ctor_get(v_s_2659_, 0);
lean_inc_ref(v_a_2675_);
v_b_2676_ = lean_ctor_get(v_s_2659_, 1);
lean_inc_ref(v_b_2676_);
v_eq_2677_ = lean_ctor_get(v_s_2659_, 3);
lean_inc_ref(v_eq_2677_);
lean_dec_ref_known(v_s_2659_, 5);
v___x_2678_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2675_, v_b_2676_, v_eq_2677_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec(v_a_2680_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(lean_object* v_x_2692_){
_start:
{
if (lean_obj_tag(v_x_2692_) == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
return v___x_2693_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_unsigned_to_nat(1u);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___boxed(lean_object* v_x_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx(v_x_2695_);
lean_dec(v_x_2695_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2697_, lean_object* v_k_2698_){
_start:
{
if (lean_obj_tag(v_t_2697_) == 0)
{
return v_k_2698_;
}
else
{
lean_object* v_c_2699_; lean_object* v_numCases_2700_; uint8_t v_isRec_2701_; uint8_t v_tryPostpone_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_c_2699_ = lean_ctor_get(v_t_2697_, 0);
lean_inc_ref(v_c_2699_);
v_numCases_2700_ = lean_ctor_get(v_t_2697_, 1);
lean_inc(v_numCases_2700_);
v_isRec_2701_ = lean_ctor_get_uint8(v_t_2697_, sizeof(void*)*2);
v_tryPostpone_2702_ = lean_ctor_get_uint8(v_t_2697_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2697_, 2);
v___x_2703_ = lean_box(v_isRec_2701_);
v___x_2704_ = lean_box(v_tryPostpone_2702_);
v___x_2705_ = lean_apply_4(v_k_2698_, v_c_2699_, v_numCases_2700_, v___x_2703_, v___x_2704_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2706_, lean_object* v_ctorIdx_2707_, lean_object* v_t_2708_, lean_object* v_h_2709_, lean_object* v_k_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2708_, v_k_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2712_, lean_object* v_ctorIdx_2713_, lean_object* v_t_2714_, lean_object* v_h_2715_, lean_object* v_k_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2712_, v_ctorIdx_2713_, v_t_2714_, v_h_2715_, v_k_2716_);
lean_dec(v_ctorIdx_2713_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2718_, lean_object* v_none_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2718_, v_none_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2721_, lean_object* v_t_2722_, lean_object* v_h_2723_, lean_object* v_none_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2722_, v_none_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2726_, lean_object* v_some_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2726_, v_some_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2729_, lean_object* v_t_2730_, lean_object* v_h_2731_, lean_object* v_some_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2730_, v_some_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2734_, lean_object* v_as_2735_, size_t v_i_2736_, size_t v_stop_2737_){
_start:
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_usize_dec_eq(v_i_2736_, v_stop_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = lean_array_uget_borrowed(v_as_2735_, v_i_2736_);
v___x_2740_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2739_, v_a_2734_);
if (v___x_2740_ == 0)
{
size_t v___x_2741_; size_t v___x_2742_; 
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2736_, v___x_2741_);
v_i_2736_ = v___x_2742_;
goto _start;
}
else
{
return v___x_2740_;
}
}
else
{
uint8_t v___x_2744_; 
v___x_2744_ = 0;
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2745_, lean_object* v_as_2746_, lean_object* v_i_2747_, lean_object* v_stop_2748_){
_start:
{
uint64_t v_a_2506__boxed_2749_; size_t v_i_boxed_2750_; size_t v_stop_boxed_2751_; uint8_t v_res_2752_; lean_object* v_r_2753_; 
v_a_2506__boxed_2749_ = lean_unbox_uint64(v_a_2745_);
lean_dec_ref(v_a_2745_);
v_i_boxed_2750_ = lean_unbox_usize(v_i_2747_);
lean_dec(v_i_2747_);
v_stop_boxed_2751_ = lean_unbox_usize(v_stop_2748_);
lean_dec(v_stop_2748_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2506__boxed_2749_, v_as_2746_, v_i_boxed_2750_, v_stop_boxed_2751_);
lean_dec_ref(v_as_2746_);
v_r_2753_ = lean_box(v_res_2752_);
return v_r_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2756_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2809_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2809_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2809_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
if (lean_obj_tag(v_a_2766_) == 1)
{
lean_object* v_val_2770_; lean_object* v___x_2771_; 
lean_del_object(v___x_2768_);
v_val_2770_ = lean_ctor_get(v_a_2766_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v_a_2766_, 1);
v___x_2771_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2795_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2795_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_array_get_size(v_val_2770_);
v___x_2778_ = lean_nat_dec_lt(v___x_2776_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec(v_a_2772_);
lean_dec(v_val_2770_);
v___x_2779_ = lean_box(v___x_2778_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2779_);
v___x_2781_ = v___x_2774_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
if (v___x_2778_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_a_2772_);
lean_dec(v_val_2770_);
v___x_2783_ = lean_box(v___x_2778_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2783_);
v___x_2785_ = v___x_2774_;
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
else
{
size_t v___x_2787_; size_t v___x_2788_; uint64_t v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2787_ = ((size_t)0ULL);
v___x_2788_ = lean_usize_of_nat(v___x_2777_);
v___x_2789_ = lean_unbox_uint64(v_a_2772_);
lean_dec(v_a_2772_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2789_, v_val_2770_, v___x_2787_, v___x_2788_);
lean_dec(v_val_2770_);
v___x_2791_ = lean_box(v___x_2790_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2791_);
v___x_2793_ = v___x_2774_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
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
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_val_2770_);
v_a_2796_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2771_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2771_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
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
uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_dec(v_a_2766_);
v___x_2804_ = 1;
v___x_2805_ = lean_box(v___x_2804_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2805_);
v___x_2807_ = v___x_2768_;
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
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v_a_2810_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2765_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2765_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_c_2818_);
return v_res_2829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2833_, lean_object* v_c_x3f_2834_, lean_object* v_cs_x27_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
if (lean_obj_tag(v_cs_2833_) == 0)
{
lean_object* v___x_2847_; lean_object* v_toGoalState_2848_; lean_object* v_split_2849_; lean_object* v_mvarId_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2958_; 
v___x_2847_ = lean_st_ref_take(v_a_2836_);
v_toGoalState_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_toGoalState_2848_);
v_split_2849_ = lean_ctor_get(v_toGoalState_2848_, 14);
lean_inc_ref(v_split_2849_);
v_mvarId_2850_ = lean_ctor_get(v___x_2847_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v___x_2847_, 0);
lean_dec(v_unused_2959_);
v___x_2852_ = v___x_2847_;
v_isShared_2853_ = v_isSharedCheck_2958_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_mvarId_2850_);
lean_dec(v___x_2847_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2958_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_nextDeclIdx_2854_; lean_object* v_enodeMap_2855_; lean_object* v_exprs_2856_; lean_object* v_parents_2857_; lean_object* v_congrTable_2858_; lean_object* v_appMap_2859_; lean_object* v_indicesFound_2860_; lean_object* v_newFacts_2861_; uint8_t v_inconsistent_2862_; lean_object* v_nextIdx_2863_; lean_object* v_newRawFacts_2864_; lean_object* v_facts_2865_; lean_object* v_extThms_2866_; lean_object* v_ematch_2867_; lean_object* v_inj_2868_; lean_object* v_clean_2869_; lean_object* v_sstates_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2956_; 
v_nextDeclIdx_2854_ = lean_ctor_get(v_toGoalState_2848_, 0);
v_enodeMap_2855_ = lean_ctor_get(v_toGoalState_2848_, 1);
v_exprs_2856_ = lean_ctor_get(v_toGoalState_2848_, 2);
v_parents_2857_ = lean_ctor_get(v_toGoalState_2848_, 3);
v_congrTable_2858_ = lean_ctor_get(v_toGoalState_2848_, 4);
v_appMap_2859_ = lean_ctor_get(v_toGoalState_2848_, 5);
v_indicesFound_2860_ = lean_ctor_get(v_toGoalState_2848_, 6);
v_newFacts_2861_ = lean_ctor_get(v_toGoalState_2848_, 7);
v_inconsistent_2862_ = lean_ctor_get_uint8(v_toGoalState_2848_, sizeof(void*)*17);
v_nextIdx_2863_ = lean_ctor_get(v_toGoalState_2848_, 8);
v_newRawFacts_2864_ = lean_ctor_get(v_toGoalState_2848_, 9);
v_facts_2865_ = lean_ctor_get(v_toGoalState_2848_, 10);
v_extThms_2866_ = lean_ctor_get(v_toGoalState_2848_, 11);
v_ematch_2867_ = lean_ctor_get(v_toGoalState_2848_, 12);
v_inj_2868_ = lean_ctor_get(v_toGoalState_2848_, 13);
v_clean_2869_ = lean_ctor_get(v_toGoalState_2848_, 15);
v_sstates_2870_ = lean_ctor_get(v_toGoalState_2848_, 16);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_toGoalState_2848_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v_toGoalState_2848_, 14);
lean_dec(v_unused_2957_);
v___x_2872_ = v_toGoalState_2848_;
v_isShared_2873_ = v_isSharedCheck_2956_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_sstates_2870_);
lean_inc(v_clean_2869_);
lean_inc(v_inj_2868_);
lean_inc(v_ematch_2867_);
lean_inc(v_extThms_2866_);
lean_inc(v_facts_2865_);
lean_inc(v_newRawFacts_2864_);
lean_inc(v_nextIdx_2863_);
lean_inc(v_newFacts_2861_);
lean_inc(v_indicesFound_2860_);
lean_inc(v_appMap_2859_);
lean_inc(v_congrTable_2858_);
lean_inc(v_parents_2857_);
lean_inc(v_exprs_2856_);
lean_inc(v_enodeMap_2855_);
lean_inc(v_nextDeclIdx_2854_);
lean_dec(v_toGoalState_2848_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2956_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_num_2874_; lean_object* v_added_2875_; lean_object* v_resolved_2876_; lean_object* v_trace_2877_; lean_object* v_lookaheads_2878_; lean_object* v_argPosMap_2879_; lean_object* v_argsAt_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2954_; 
v_num_2874_ = lean_ctor_get(v_split_2849_, 0);
v_added_2875_ = lean_ctor_get(v_split_2849_, 2);
v_resolved_2876_ = lean_ctor_get(v_split_2849_, 3);
v_trace_2877_ = lean_ctor_get(v_split_2849_, 4);
v_lookaheads_2878_ = lean_ctor_get(v_split_2849_, 5);
v_argPosMap_2879_ = lean_ctor_get(v_split_2849_, 6);
v_argsAt_2880_ = lean_ctor_get(v_split_2849_, 7);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_split_2849_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v_split_2849_, 1);
lean_dec(v_unused_2955_);
v___x_2882_ = v_split_2849_;
v_isShared_2883_ = v_isSharedCheck_2954_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_argsAt_2880_);
lean_inc(v_argPosMap_2879_);
lean_inc(v_lookaheads_2878_);
lean_inc(v_trace_2877_);
lean_inc(v_resolved_2876_);
lean_inc(v_added_2875_);
lean_inc(v_num_2874_);
lean_dec(v_split_2849_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2954_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2884_ = l_List_reverse___redArg(v_cs_x27_2835_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2884_);
v___x_2886_ = v___x_2882_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_num_2874_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_added_2875_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_resolved_2876_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_trace_2877_);
lean_ctor_set(v_reuseFailAlloc_2953_, 5, v_lookaheads_2878_);
lean_ctor_set(v_reuseFailAlloc_2953_, 6, v_argPosMap_2879_);
lean_ctor_set(v_reuseFailAlloc_2953_, 7, v_argsAt_2880_);
v___x_2886_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 14, v___x_2886_);
v___x_2888_ = v___x_2872_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_nextDeclIdx_2854_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_enodeMap_2855_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_exprs_2856_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_parents_2857_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_congrTable_2858_);
lean_ctor_set(v_reuseFailAlloc_2952_, 5, v_appMap_2859_);
lean_ctor_set(v_reuseFailAlloc_2952_, 6, v_indicesFound_2860_);
lean_ctor_set(v_reuseFailAlloc_2952_, 7, v_newFacts_2861_);
lean_ctor_set(v_reuseFailAlloc_2952_, 8, v_nextIdx_2863_);
lean_ctor_set(v_reuseFailAlloc_2952_, 9, v_newRawFacts_2864_);
lean_ctor_set(v_reuseFailAlloc_2952_, 10, v_facts_2865_);
lean_ctor_set(v_reuseFailAlloc_2952_, 11, v_extThms_2866_);
lean_ctor_set(v_reuseFailAlloc_2952_, 12, v_ematch_2867_);
lean_ctor_set(v_reuseFailAlloc_2952_, 13, v_inj_2868_);
lean_ctor_set(v_reuseFailAlloc_2952_, 14, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2952_, 15, v_clean_2869_);
lean_ctor_set(v_reuseFailAlloc_2952_, 16, v_sstates_2870_);
lean_ctor_set_uint8(v_reuseFailAlloc_2952_, sizeof(void*)*17, v_inconsistent_2862_);
v___x_2888_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2890_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2888_);
v___x_2890_ = v___x_2852_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_mvarId_2850_);
v___x_2890_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_st_ref_put(v_a_2836_, v___x_2890_);
if (lean_obj_tag(v_c_x3f_2834_) == 1)
{
lean_object* v___x_2892_; lean_object* v_toGoalState_2893_; lean_object* v_ematch_2894_; lean_object* v_mvarId_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2948_; 
v___x_2892_ = lean_st_ref_take(v_a_2836_);
v_toGoalState_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc_ref(v_toGoalState_2893_);
v_ematch_2894_ = lean_ctor_get(v_toGoalState_2893_, 12);
lean_inc_ref(v_ematch_2894_);
v_mvarId_2895_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v___x_2892_, 0);
lean_dec(v_unused_2949_);
v___x_2897_ = v___x_2892_;
v_isShared_2898_ = v_isSharedCheck_2948_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_mvarId_2895_);
lean_dec(v___x_2892_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2948_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_nextDeclIdx_2899_; lean_object* v_enodeMap_2900_; lean_object* v_exprs_2901_; lean_object* v_parents_2902_; lean_object* v_congrTable_2903_; lean_object* v_appMap_2904_; lean_object* v_indicesFound_2905_; lean_object* v_newFacts_2906_; uint8_t v_inconsistent_2907_; lean_object* v_nextIdx_2908_; lean_object* v_newRawFacts_2909_; lean_object* v_facts_2910_; lean_object* v_extThms_2911_; lean_object* v_inj_2912_; lean_object* v_split_2913_; lean_object* v_clean_2914_; lean_object* v_sstates_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2946_; 
v_nextDeclIdx_2899_ = lean_ctor_get(v_toGoalState_2893_, 0);
v_enodeMap_2900_ = lean_ctor_get(v_toGoalState_2893_, 1);
v_exprs_2901_ = lean_ctor_get(v_toGoalState_2893_, 2);
v_parents_2902_ = lean_ctor_get(v_toGoalState_2893_, 3);
v_congrTable_2903_ = lean_ctor_get(v_toGoalState_2893_, 4);
v_appMap_2904_ = lean_ctor_get(v_toGoalState_2893_, 5);
v_indicesFound_2905_ = lean_ctor_get(v_toGoalState_2893_, 6);
v_newFacts_2906_ = lean_ctor_get(v_toGoalState_2893_, 7);
v_inconsistent_2907_ = lean_ctor_get_uint8(v_toGoalState_2893_, sizeof(void*)*17);
v_nextIdx_2908_ = lean_ctor_get(v_toGoalState_2893_, 8);
v_newRawFacts_2909_ = lean_ctor_get(v_toGoalState_2893_, 9);
v_facts_2910_ = lean_ctor_get(v_toGoalState_2893_, 10);
v_extThms_2911_ = lean_ctor_get(v_toGoalState_2893_, 11);
v_inj_2912_ = lean_ctor_get(v_toGoalState_2893_, 13);
v_split_2913_ = lean_ctor_get(v_toGoalState_2893_, 14);
v_clean_2914_ = lean_ctor_get(v_toGoalState_2893_, 15);
v_sstates_2915_ = lean_ctor_get(v_toGoalState_2893_, 16);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_toGoalState_2893_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v_toGoalState_2893_, 12);
lean_dec(v_unused_2947_);
v___x_2917_ = v_toGoalState_2893_;
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_sstates_2915_);
lean_inc(v_clean_2914_);
lean_inc(v_split_2913_);
lean_inc(v_inj_2912_);
lean_inc(v_extThms_2911_);
lean_inc(v_facts_2910_);
lean_inc(v_newRawFacts_2909_);
lean_inc(v_nextIdx_2908_);
lean_inc(v_newFacts_2906_);
lean_inc(v_indicesFound_2905_);
lean_inc(v_appMap_2904_);
lean_inc(v_congrTable_2903_);
lean_inc(v_parents_2902_);
lean_inc(v_exprs_2901_);
lean_inc(v_enodeMap_2900_);
lean_inc(v_nextDeclIdx_2899_);
lean_dec(v_toGoalState_2893_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_thmMap_2919_; lean_object* v_gmt_2920_; lean_object* v_thms_2921_; lean_object* v_newThms_2922_; lean_object* v_numInstances_2923_; lean_object* v_numDelayedInstances_2924_; lean_object* v_preInstances_2925_; lean_object* v_nextThmIdx_2926_; lean_object* v_matchEqNames_2927_; lean_object* v_delayedThmInsts_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2944_; 
v_thmMap_2919_ = lean_ctor_get(v_ematch_2894_, 0);
v_gmt_2920_ = lean_ctor_get(v_ematch_2894_, 1);
v_thms_2921_ = lean_ctor_get(v_ematch_2894_, 2);
v_newThms_2922_ = lean_ctor_get(v_ematch_2894_, 3);
v_numInstances_2923_ = lean_ctor_get(v_ematch_2894_, 4);
v_numDelayedInstances_2924_ = lean_ctor_get(v_ematch_2894_, 5);
v_preInstances_2925_ = lean_ctor_get(v_ematch_2894_, 7);
v_nextThmIdx_2926_ = lean_ctor_get(v_ematch_2894_, 8);
v_matchEqNames_2927_ = lean_ctor_get(v_ematch_2894_, 9);
v_delayedThmInsts_2928_ = lean_ctor_get(v_ematch_2894_, 10);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_ematch_2894_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_ematch_2894_, 6);
lean_dec(v_unused_2945_);
v___x_2930_ = v_ematch_2894_;
v_isShared_2931_ = v_isSharedCheck_2944_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_delayedThmInsts_2928_);
lean_inc(v_matchEqNames_2927_);
lean_inc(v_nextThmIdx_2926_);
lean_inc(v_preInstances_2925_);
lean_inc(v_numDelayedInstances_2924_);
lean_inc(v_numInstances_2923_);
lean_inc(v_newThms_2922_);
lean_inc(v_thms_2921_);
lean_inc(v_gmt_2920_);
lean_inc(v_thmMap_2919_);
lean_dec(v_ematch_2894_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2944_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = lean_unsigned_to_nat(0u);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 6, v___x_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_thmMap_2919_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_gmt_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_thms_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_newThms_2922_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_numInstances_2923_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_numDelayedInstances_2924_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v_preInstances_2925_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v_nextThmIdx_2926_);
lean_ctor_set(v_reuseFailAlloc_2943_, 9, v_matchEqNames_2927_);
lean_ctor_set(v_reuseFailAlloc_2943_, 10, v_delayedThmInsts_2928_);
v___x_2934_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2936_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 12, v___x_2934_);
v___x_2936_ = v___x_2917_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_nextDeclIdx_2899_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_enodeMap_2900_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_exprs_2901_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v_parents_2902_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v_congrTable_2903_);
lean_ctor_set(v_reuseFailAlloc_2942_, 5, v_appMap_2904_);
lean_ctor_set(v_reuseFailAlloc_2942_, 6, v_indicesFound_2905_);
lean_ctor_set(v_reuseFailAlloc_2942_, 7, v_newFacts_2906_);
lean_ctor_set(v_reuseFailAlloc_2942_, 8, v_nextIdx_2908_);
lean_ctor_set(v_reuseFailAlloc_2942_, 9, v_newRawFacts_2909_);
lean_ctor_set(v_reuseFailAlloc_2942_, 10, v_facts_2910_);
lean_ctor_set(v_reuseFailAlloc_2942_, 11, v_extThms_2911_);
lean_ctor_set(v_reuseFailAlloc_2942_, 12, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2942_, 13, v_inj_2912_);
lean_ctor_set(v_reuseFailAlloc_2942_, 14, v_split_2913_);
lean_ctor_set(v_reuseFailAlloc_2942_, 15, v_clean_2914_);
lean_ctor_set(v_reuseFailAlloc_2942_, 16, v_sstates_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2942_, sizeof(void*)*17, v_inconsistent_2907_);
v___x_2936_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2936_);
v___x_2938_ = v___x_2897_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_mvarId_2895_);
v___x_2938_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_st_ref_put(v_a_2836_, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_c_x3f_2834_);
return v___x_2940_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_c_x3f_2834_);
return v___x_2950_;
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
lean_object* v_head_2960_; lean_object* v_tail_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3178_; 
v_head_2960_ = lean_ctor_get(v_cs_2833_, 0);
v_tail_2961_ = lean_ctor_get(v_cs_2833_, 1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_cs_2833_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_2963_ = v_cs_2833_;
v_isShared_2964_ = v_isSharedCheck_3178_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_tail_2961_);
lean_inc(v_head_2960_);
lean_dec(v_cs_2833_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3178_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; uint8_t v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; uint8_t v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; uint8_t v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; uint8_t v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; uint8_t v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; uint8_t v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___x_3074_; 
v___x_3074_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2960_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; uint8_t v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = lean_unbox(v_a_3075_);
lean_dec(v_a_3075_);
if (v___x_3076_ == 0)
{
lean_del_object(v___x_2963_);
lean_dec(v_head_2960_);
v_cs_2833_ = v_tail_2961_;
goto _start;
}
else
{
lean_object* v_options_3078_; lean_object* v_inheritedTraceOptions_3079_; uint8_t v_hasTrace_3080_; uint8_t v___x_3081_; uint8_t v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; uint8_t v___y_3096_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; 
v_options_3078_ = lean_ctor_get(v_a_2844_, 2);
v_inheritedTraceOptions_3079_ = lean_ctor_get(v_a_2844_, 13);
v_hasTrace_3080_ = lean_ctor_get_uint8(v_options_3078_, sizeof(void*)*1);
v___x_3081_ = 0;
if (v_hasTrace_3080_ == 0)
{
v___y_3104_ = v_a_2836_;
v___y_3105_ = v_a_2837_;
v___y_3106_ = v_a_2838_;
v___y_3107_ = v_a_2839_;
v___y_3108_ = v_a_2840_;
v___y_3109_ = v_a_2841_;
v___y_3110_ = v_a_2842_;
v___y_3111_ = v_a_2843_;
v___y_3112_ = v_a_2844_;
v___y_3113_ = v_a_2845_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3079_, v_options_3078_, v___x_3146_);
if (v___x_3147_ == 0)
{
v___y_3104_ = v_a_2836_;
v___y_3105_ = v_a_2837_;
v___y_3106_ = v_a_2838_;
v___y_3107_ = v_a_2839_;
v___y_3108_ = v_a_2840_;
v___y_3109_ = v_a_2841_;
v___y_3110_ = v_a_2842_;
v___y_3111_ = v_a_2843_;
v___y_3112_ = v_a_2844_;
v___y_3113_ = v_a_2845_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Meta_Grind_updateLastTag(v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec_ref_known(v___x_3148_, 1);
v___x_3149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3150_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2960_);
v___x_3151_ = l_Lean_MessageData_ofExpr(v___x_3150_);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3145_, v___x_3152_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_dec_ref_known(v___x_3153_, 1);
v___y_3104_ = v_a_2836_;
v___y_3105_ = v_a_2837_;
v___y_3106_ = v_a_2838_;
v___y_3107_ = v_a_2839_;
v___y_3108_ = v_a_2840_;
v___y_3109_ = v_a_2841_;
v___y_3110_ = v_a_2842_;
v___y_3111_ = v_a_2843_;
v___y_3112_ = v_a_2844_;
v___y_3113_ = v_a_2845_;
goto v___jp_3103_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
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
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3162_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3148_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3148_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
v___jp_3082_:
{
if (lean_obj_tag(v_c_x3f_2834_) == 0)
{
lean_object* v___x_3097_; 
lean_del_object(v___x_2963_);
v___x_3097_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3097_, 0, v_head_2960_);
lean_ctor_set(v___x_3097_, 1, v___y_3093_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*2, v___y_3088_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*2 + 1, v___y_3083_);
v_cs_2833_ = v_tail_2961_;
v_c_x3f_2834_ = v___x_3097_;
v_a_2836_ = v___y_3086_;
v_a_2837_ = v___y_3095_;
v_a_2838_ = v___y_3087_;
v_a_2839_ = v___y_3089_;
v_a_2840_ = v___y_3085_;
v_a_2841_ = v___y_3091_;
v_a_2842_ = v___y_3094_;
v_a_2843_ = v___y_3084_;
v_a_2844_ = v___y_3090_;
v_a_2845_ = v___y_3092_;
goto _start;
}
else
{
lean_object* v_c_3099_; lean_object* v_numCases_3100_; uint8_t v_tryPostpone_3101_; uint8_t v___x_3102_; 
v_c_3099_ = lean_ctor_get(v_c_x3f_2834_, 0);
v_numCases_3100_ = lean_ctor_get(v_c_x3f_2834_, 1);
v_tryPostpone_3101_ = lean_ctor_get_uint8(v_c_x3f_2834_, sizeof(void*)*2 + 1);
v___x_3102_ = lean_nat_dec_lt(v___y_3093_, v_numCases_3100_);
if (v_tryPostpone_3101_ == 0)
{
if (v___y_3083_ == 0)
{
lean_inc_ref(v_c_3099_);
lean_inc(v_numCases_3100_);
v___y_3055_ = v___y_3083_;
v___y_3056_ = v___y_3084_;
v___y_3057_ = v___y_3085_;
v___y_3058_ = v___y_3086_;
v___y_3059_ = v___y_3087_;
v___y_3060_ = v_numCases_3100_;
v___y_3061_ = v___y_3088_;
v___y_3062_ = v___y_3090_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___y_3091_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3094_;
v___y_3068_ = v___y_3095_;
v___y_3069_ = v___x_3102_;
v___y_3070_ = v_c_3099_;
v___y_3071_ = v___x_3081_;
goto v___jp_3054_;
}
else
{
lean_dec(v___y_3093_);
v___y_2966_ = v___y_3085_;
v___y_2967_ = v___y_3087_;
v___y_2968_ = v___y_3086_;
v___y_2969_ = v___y_3090_;
v___y_2970_ = v___y_3089_;
v___y_2971_ = v___y_3091_;
v___y_2972_ = v___y_3092_;
v___y_2973_ = v___y_3094_;
v___y_2974_ = v___y_3095_;
v___y_2975_ = v___y_3084_;
goto v___jp_2965_;
}
}
else
{
if (v___y_3083_ == 0)
{
lean_inc_ref(v_c_3099_);
lean_dec_ref_known(v_c_x3f_2834_, 2);
lean_del_object(v___x_2963_);
v___y_2981_ = v___y_3083_;
v___y_2982_ = v___y_3084_;
v___y_2983_ = v___y_3085_;
v___y_2984_ = v___y_3086_;
v___y_2985_ = v___y_3087_;
v___y_2986_ = v___y_3088_;
v___y_2987_ = v___y_3089_;
v___y_2988_ = v___y_3090_;
v___y_2989_ = v___y_3091_;
v___y_2990_ = v___y_3092_;
v___y_2991_ = v___y_3093_;
v___y_2992_ = v___y_3094_;
v___y_2993_ = v___y_3095_;
v___y_2994_ = v_c_3099_;
goto v___jp_2980_;
}
else
{
if (v___y_3096_ == 0)
{
lean_inc_ref(v_c_3099_);
lean_inc(v_numCases_3100_);
v___y_3055_ = v___y_3083_;
v___y_3056_ = v___y_3084_;
v___y_3057_ = v___y_3085_;
v___y_3058_ = v___y_3086_;
v___y_3059_ = v___y_3087_;
v___y_3060_ = v_numCases_3100_;
v___y_3061_ = v___y_3088_;
v___y_3062_ = v___y_3090_;
v___y_3063_ = v___y_3089_;
v___y_3064_ = v___y_3091_;
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3094_;
v___y_3068_ = v___y_3095_;
v___y_3069_ = v___x_3102_;
v___y_3070_ = v_c_3099_;
v___y_3071_ = v___y_3096_;
goto v___jp_3054_;
}
else
{
lean_inc_ref(v_c_3099_);
lean_dec_ref_known(v_c_x3f_2834_, 2);
lean_del_object(v___x_2963_);
v___y_2981_ = v___y_3083_;
v___y_2982_ = v___y_3084_;
v___y_2983_ = v___y_3085_;
v___y_2984_ = v___y_3086_;
v___y_2985_ = v___y_3087_;
v___y_2986_ = v___y_3088_;
v___y_2987_ = v___y_3089_;
v___y_2988_ = v___y_3090_;
v___y_2989_ = v___y_3091_;
v___y_2990_ = v___y_3092_;
v___y_2991_ = v___y_3093_;
v___y_2992_ = v___y_3094_;
v___y_2993_ = v___y_3095_;
v___y_2994_ = v_c_3099_;
goto v___jp_2980_;
}
}
}
}
}
v___jp_3103_:
{
lean_object* v___x_3114_; 
lean_inc(v_head_2960_);
v___x_3114_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2960_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
switch(lean_obj_tag(v_a_3115_))
{
case 0:
{
lean_del_object(v___x_2963_);
lean_dec(v_head_2960_);
v_cs_2833_ = v_tail_2961_;
v_a_2836_ = v___y_3104_;
v_a_2837_ = v___y_3105_;
v_a_2838_ = v___y_3106_;
v_a_2839_ = v___y_3107_;
v_a_2840_ = v___y_3108_;
v_a_2841_ = v___y_3109_;
v_a_2842_ = v___y_3110_;
v_a_2843_ = v___y_3111_;
v_a_2844_ = v___y_3112_;
v_a_2845_ = v___y_3113_;
goto _start;
}
case 1:
{
lean_object* v___x_3117_; 
lean_del_object(v___x_2963_);
v___x_3117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_head_2960_);
lean_ctor_set(v___x_3117_, 1, v_cs_x27_2835_);
v_cs_2833_ = v_tail_2961_;
v_cs_x27_2835_ = v___x_3117_;
v_a_2836_ = v___y_3104_;
v_a_2837_ = v___y_3105_;
v_a_2838_ = v___y_3106_;
v_a_2839_ = v___y_3107_;
v_a_2840_ = v___y_3108_;
v_a_2841_ = v___y_3109_;
v_a_2842_ = v___y_3110_;
v_a_2843_ = v___y_3111_;
v_a_2844_ = v___y_3112_;
v_a_2845_ = v___y_3113_;
goto _start;
}
default: 
{
lean_object* v_numCases_3119_; uint8_t v_isRec_3120_; uint8_t v_tryPostpone_3121_; lean_object* v___x_3122_; 
v_numCases_3119_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_numCases_3119_);
v_isRec_3120_ = lean_ctor_get_uint8(v_a_3115_, sizeof(void*)*1);
v_tryPostpone_3121_ = lean_ctor_get_uint8(v_a_3115_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3115_, 1);
v___x_3122_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3106_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; uint8_t v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3124_ = lean_unbox(v_a_3123_);
lean_dec(v_a_3123_);
if (v___x_3124_ == 0)
{
v___y_3083_ = v_tryPostpone_3121_;
v___y_3084_ = v___y_3111_;
v___y_3085_ = v___y_3108_;
v___y_3086_ = v___y_3104_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v_isRec_3120_;
v___y_3089_ = v___y_3107_;
v___y_3090_ = v___y_3112_;
v___y_3091_ = v___y_3109_;
v___y_3092_ = v___y_3113_;
v___y_3093_ = v_numCases_3119_;
v___y_3094_ = v___y_3110_;
v___y_3095_ = v___y_3105_;
v___y_3096_ = v___x_3081_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3125_ = lean_unsigned_to_nat(1u);
v___x_3126_ = lean_nat_dec_lt(v___x_3125_, v_numCases_3119_);
if (v___x_3126_ == 0)
{
v___y_3083_ = v_tryPostpone_3121_;
v___y_3084_ = v___y_3111_;
v___y_3085_ = v___y_3108_;
v___y_3086_ = v___y_3104_;
v___y_3087_ = v___y_3106_;
v___y_3088_ = v_isRec_3120_;
v___y_3089_ = v___y_3107_;
v___y_3090_ = v___y_3112_;
v___y_3091_ = v___y_3109_;
v___y_3092_ = v___y_3113_;
v___y_3093_ = v_numCases_3119_;
v___y_3094_ = v___y_3110_;
v___y_3095_ = v___y_3105_;
v___y_3096_ = v___x_3126_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3127_; 
lean_dec(v_numCases_3119_);
lean_del_object(v___x_2963_);
v___x_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_head_2960_);
lean_ctor_set(v___x_3127_, 1, v_cs_x27_2835_);
v_cs_2833_ = v_tail_2961_;
v_cs_x27_2835_ = v___x_3127_;
v_a_2836_ = v___y_3104_;
v_a_2837_ = v___y_3105_;
v_a_2838_ = v___y_3106_;
v_a_2839_ = v___y_3107_;
v_a_2840_ = v___y_3108_;
v_a_2841_ = v___y_3109_;
v_a_2842_ = v___y_3110_;
v_a_2843_ = v___y_3111_;
v_a_2844_ = v___y_3112_;
v_a_2845_ = v___y_3113_;
goto _start;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_numCases_3119_);
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3129_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3122_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3122_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3137_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3114_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3114_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3170_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3074_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3074_);
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
v___jp_2965_:
{
lean_object* v___x_2977_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v_cs_x27_2835_);
v___x_2977_ = v___x_2963_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_head_2960_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_cs_x27_2835_);
v___x_2977_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v_cs_2833_ = v_tail_2961_;
v_cs_x27_2835_ = v___x_2977_;
v_a_2836_ = v___y_2968_;
v_a_2837_ = v___y_2974_;
v_a_2838_ = v___y_2967_;
v_a_2839_ = v___y_2970_;
v_a_2840_ = v___y_2966_;
v_a_2841_ = v___y_2971_;
v_a_2842_ = v___y_2973_;
v_a_2843_ = v___y_2975_;
v_a_2844_ = v___y_2969_;
v_a_2845_ = v___y_2972_;
goto _start;
}
}
v___jp_2980_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2995_, 0, v_head_2960_);
lean_ctor_set(v___x_2995_, 1, v___y_2991_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*2, v___y_2986_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*2 + 1, v___y_2981_);
v___x_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2994_);
lean_ctor_set(v___x_2996_, 1, v_cs_x27_2835_);
v_cs_2833_ = v_tail_2961_;
v_c_x3f_2834_ = v___x_2995_;
v_cs_x27_2835_ = v___x_2996_;
v_a_2836_ = v___y_2984_;
v_a_2837_ = v___y_2993_;
v_a_2838_ = v___y_2985_;
v_a_2839_ = v___y_2987_;
v_a_2840_ = v___y_2983_;
v_a_2841_ = v___y_2989_;
v_a_2842_ = v___y_2992_;
v_a_2843_ = v___y_2982_;
v_a_2844_ = v___y_2988_;
v_a_2845_ = v___y_2990_;
goto _start;
}
v___jp_2998_:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2960_, v___y_3002_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3013_, v___y_3002_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; uint8_t v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_nat_dec_lt(v_a_3015_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec(v_a_3015_);
if (v___x_3018_ == 0)
{
if (v___y_3011_ == 0)
{
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3009_);
v___y_2966_ = v___y_3001_;
v___y_2967_ = v___y_3003_;
v___y_2968_ = v___y_3002_;
v___y_2969_ = v___y_3005_;
v___y_2970_ = v___y_3006_;
v___y_2971_ = v___y_3007_;
v___y_2972_ = v___y_3008_;
v___y_2973_ = v___y_3010_;
v___y_2974_ = v___y_3012_;
v___y_2975_ = v___y_3000_;
goto v___jp_2965_;
}
else
{
lean_del_object(v___x_2963_);
lean_dec(v_c_x3f_2834_);
v___y_2981_ = v___y_2999_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3001_;
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3003_;
v___y_2986_ = v___y_3004_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3005_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v___y_3008_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3013_;
goto v___jp_2980_;
}
}
else
{
lean_del_object(v___x_2963_);
lean_dec(v_c_x3f_2834_);
v___y_2981_ = v___y_2999_;
v___y_2982_ = v___y_3000_;
v___y_2983_ = v___y_3001_;
v___y_2984_ = v___y_3002_;
v___y_2985_ = v___y_3003_;
v___y_2986_ = v___y_3004_;
v___y_2987_ = v___y_3006_;
v___y_2988_ = v___y_3005_;
v___y_2989_ = v___y_3007_;
v___y_2990_ = v___y_3008_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3013_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_3015_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3009_);
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3019_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3016_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3016_);
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
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3009_);
lean_del_object(v___x_2963_);
lean_dec(v_tail_2961_);
lean_dec(v_head_2960_);
lean_dec(v_cs_x27_2835_);
lean_dec(v_c_x3f_2834_);
v_a_3027_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3014_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3014_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
v___jp_3035_:
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(1u);
v___x_3053_ = lean_nat_dec_lt(v___x_3052_, v___y_3041_);
lean_dec(v___y_3041_);
if (v___x_3053_ == 0)
{
v___y_2999_ = v___y_3036_;
v___y_3000_ = v___y_3037_;
v___y_3001_ = v___y_3038_;
v___y_3002_ = v___y_3039_;
v___y_3003_ = v___y_3040_;
v___y_3004_ = v___y_3042_;
v___y_3005_ = v___y_3043_;
v___y_3006_ = v___y_3044_;
v___y_3007_ = v___y_3045_;
v___y_3008_ = v___y_3046_;
v___y_3009_ = v___y_3047_;
v___y_3010_ = v___y_3048_;
v___y_3011_ = v___y_3050_;
v___y_3012_ = v___y_3049_;
v___y_3013_ = v___y_3051_;
goto v___jp_2998_;
}
else
{
lean_del_object(v___x_2963_);
lean_dec(v_c_x3f_2834_);
v___y_2981_ = v___y_3036_;
v___y_2982_ = v___y_3037_;
v___y_2983_ = v___y_3038_;
v___y_2984_ = v___y_3039_;
v___y_2985_ = v___y_3040_;
v___y_2986_ = v___y_3042_;
v___y_2987_ = v___y_3044_;
v___y_2988_ = v___y_3043_;
v___y_2989_ = v___y_3045_;
v___y_2990_ = v___y_3046_;
v___y_2991_ = v___y_3047_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3051_;
goto v___jp_2980_;
}
}
v___jp_3054_:
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_dec_eq(v___y_3066_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_dec(v___y_3060_);
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v___y_3058_;
v___y_3003_ = v___y_3059_;
v___y_3004_ = v___y_3061_;
v___y_3005_ = v___y_3062_;
v___y_3006_ = v___y_3063_;
v___y_3007_ = v___y_3064_;
v___y_3008_ = v___y_3065_;
v___y_3009_ = v___y_3066_;
v___y_3010_ = v___y_3067_;
v___y_3011_ = v___y_3069_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3070_;
goto v___jp_2998_;
}
else
{
if (v___y_3061_ == 0)
{
v___y_3036_ = v___y_3055_;
v___y_3037_ = v___y_3056_;
v___y_3038_ = v___y_3057_;
v___y_3039_ = v___y_3058_;
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
goto v___jp_3035_;
}
else
{
if (v___y_3071_ == 0)
{
lean_dec(v___y_3060_);
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v___y_3058_;
v___y_3003_ = v___y_3059_;
v___y_3004_ = v___y_3061_;
v___y_3005_ = v___y_3062_;
v___y_3006_ = v___y_3063_;
v___y_3007_ = v___y_3064_;
v___y_3008_ = v___y_3065_;
v___y_3009_ = v___y_3066_;
v___y_3010_ = v___y_3067_;
v___y_3011_ = v___y_3069_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3070_;
goto v___jp_2998_;
}
else
{
v___y_3036_ = v___y_3055_;
v___y_3037_ = v___y_3056_;
v___y_3038_ = v___y_3057_;
v___y_3039_ = v___y_3058_;
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
goto v___jp_3035_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3179_, lean_object* v_c_x3f_3180_, lean_object* v_cs_x27_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3179_, v_c_x3f_3180_, v_cs_x27_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3194_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3241_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3241_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3241_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
uint8_t v___x_3210_; 
v___x_3210_ = lean_unbox(v_a_3206_);
lean_dec(v_a_3206_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_del_object(v___x_3208_);
v___x_3211_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3194_, v_a_3196_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3228_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3228_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3228_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v_toGoalState_3218_; lean_object* v_split_3219_; lean_object* v_candidates_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_del_object(v___x_3214_);
v___x_3217_ = lean_st_ref_get(v_a_3194_);
v_toGoalState_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_ref(v_toGoalState_3218_);
lean_dec(v___x_3217_);
v_split_3219_ = lean_ctor_get(v_toGoalState_3218_, 14);
lean_inc_ref(v_split_3219_);
lean_dec_ref(v_toGoalState_3218_);
v_candidates_3220_ = lean_ctor_get(v_split_3219_, 1);
lean_inc(v_candidates_3220_);
lean_dec_ref(v_split_3219_);
v___x_3221_ = lean_box(0);
v___x_3222_ = lean_box(0);
v___x_3223_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3220_, v___x_3221_, v___x_3222_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_box(0);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3224_);
v___x_3226_ = v___x_3214_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_a_3229_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3211_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3211_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3237_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3237_);
v___x_3239_ = v___x_3208_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3205_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3205_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec(v_a_3250_);
return v_res_3261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_box(0);
v___x_3270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3271_ = l_Lean_mkConst(v___x_3270_, v___x_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3272_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3274_ = l_Lean_Expr_app___override(v___x_3273_, v_c_3272_);
return v___x_3274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3285_ = l_Lean_mkConst(v___x_3284_, v___x_3283_);
return v___x_3285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_box(0);
v___x_3292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3293_ = l_Lean_mkConst(v___x_3292_, v___x_3291_);
return v___x_3293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_box(0);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3301_ = l_Lean_mkConst(v___x_3300_, v___x_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___x_3361_; 
lean_inc_ref(v_c_3302_);
v___x_3361_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3302_, v_a_3310_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3447_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3447_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3447_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = l_Lean_Expr_cleanupAnnotations(v_a_3362_);
v___x_3380_ = l_Lean_Expr_isApp(v___x_3379_);
if (v___x_3380_ == 0)
{
lean_dec_ref(v___x_3379_);
lean_del_object(v___x_3364_);
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
v___y_3370_ = v_a_3306_;
v___y_3371_ = v_a_3307_;
v___y_3372_ = v_a_3308_;
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
goto v___jp_3366_;
}
else
{
lean_object* v_arg_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_arg_3381_ = lean_ctor_get(v___x_3379_, 1);
lean_inc_ref(v_arg_3381_);
v___x_3382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3379_);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3384_ = l_Lean_Expr_isConstOf(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_Expr_isApp(v___x_3382_);
if (v___x_3385_ == 0)
{
lean_dec_ref(v___x_3382_);
lean_dec_ref(v_arg_3381_);
lean_del_object(v___x_3364_);
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
v___y_3370_ = v_a_3306_;
v___y_3371_ = v_a_3307_;
v___y_3372_ = v_a_3308_;
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
goto v___jp_3366_;
}
else
{
lean_object* v_arg_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_arg_3386_ = lean_ctor_get(v___x_3382_, 1);
lean_inc_ref(v_arg_3386_);
v___x_3387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3382_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3389_ = l_Lean_Expr_isConstOf(v___x_3387_, v___x_3388_);
if (v___x_3389_ == 0)
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_Expr_isApp(v___x_3387_);
if (v___x_3390_ == 0)
{
lean_dec_ref(v___x_3387_);
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_del_object(v___x_3364_);
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
v___y_3370_ = v_a_3306_;
v___y_3371_ = v_a_3307_;
v___y_3372_ = v_a_3308_;
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
goto v___jp_3366_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3387_);
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3393_ = l_Lean_Expr_isConstOf(v___x_3391_, v___x_3392_);
lean_dec_ref(v___x_3391_);
if (v___x_3393_ == 0)
{
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_del_object(v___x_3364_);
v___y_3367_ = v_a_3303_;
v___y_3368_ = v_a_3304_;
v___y_3369_ = v_a_3305_;
v___y_3370_ = v_a_3306_;
v___y_3371_ = v_a_3307_;
v___y_3372_ = v_a_3308_;
v___y_3373_ = v_a_3309_;
v___y_3374_ = v_a_3310_;
v___y_3375_ = v_a_3311_;
v___y_3376_ = v_a_3312_;
goto v___jp_3366_;
}
else
{
uint8_t v___x_3394_; 
lean_inc_ref(v_c_3302_);
v___x_3394_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3302_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3397_; 
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
v___x_3395_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3302_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3395_);
v___x_3397_ = v___x_3364_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
else
{
lean_object* v___x_3399_; 
lean_del_object(v___x_3364_);
lean_inc_ref(v_c_3302_);
v___x_3399_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3302_, v_a_3303_, v_a_3307_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; uint8_t v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v___x_3401_ = lean_unbox(v_a_3400_);
lean_dec(v_a_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3412_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3412_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3412_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3408_ = l_Lean_mkApp3(v___x_3407_, v_arg_3386_, v_arg_3381_, v_a_3403_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3408_);
v___x_3410_ = v___x_3405_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
return v___x_3402_;
}
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3423_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3419_ = l_Lean_mkApp3(v___x_3418_, v_arg_3386_, v_arg_3381_, v_a_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3419_);
v___x_3421_ = v___x_3416_;
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
}
else
{
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
return v___x_3413_;
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_c_3302_);
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
}
}
else
{
lean_object* v___x_3432_; 
lean_dec_ref(v___x_3387_);
lean_del_object(v___x_3364_);
v___x_3432_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3442_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3438_ = l_Lean_mkApp3(v___x_3437_, v_arg_3386_, v_arg_3381_, v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
return v___x_3432_;
}
}
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_dec_ref(v___x_3382_);
lean_dec_ref(v_c_3302_);
v___x_3443_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3381_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3443_);
v___x_3445_ = v___x_3364_;
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
v___jp_3366_:
{
uint8_t v___x_3377_; 
v___x_3377_ = l_Lean_Meta_Grind_isIte(v_c_3302_);
if (v___x_3377_ == 0)
{
uint8_t v___x_3378_; 
v___x_3378_ = l_Lean_Meta_Grind_isDIte(v_c_3302_);
v___y_3315_ = v___y_3375_;
v___y_3316_ = v___y_3373_;
v___y_3317_ = v___y_3376_;
v___y_3318_ = v___y_3371_;
v___y_3319_ = v___y_3370_;
v___y_3320_ = v___y_3374_;
v___y_3321_ = v___y_3372_;
v___y_3322_ = v___y_3368_;
v___y_3323_ = v___y_3367_;
v___y_3324_ = v___y_3369_;
v___y_3325_ = v___x_3378_;
goto v___jp_3314_;
}
else
{
v___y_3315_ = v___y_3375_;
v___y_3316_ = v___y_3373_;
v___y_3317_ = v___y_3376_;
v___y_3318_ = v___y_3371_;
v___y_3319_ = v___y_3370_;
v___y_3320_ = v___y_3374_;
v___y_3321_ = v___y_3372_;
v___y_3322_ = v___y_3368_;
v___y_3323_ = v___y_3367_;
v___y_3324_ = v___y_3369_;
v___y_3325_ = v___x_3377_;
goto v___jp_3314_;
}
}
}
}
else
{
lean_dec_ref(v_c_3302_);
return v___x_3361_;
}
v___jp_3314_:
{
if (v___y_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_inc_ref(v_c_3302_);
v___x_3326_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3302_, v___y_3323_, v___y_3318_, v___y_3316_, v___y_3320_, v___y_3315_, v___y_3317_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3345_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3345_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3345_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_unbox(v_a_3327_);
lean_dec(v_a_3327_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3333_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v_c_3302_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_c_3302_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
lean_object* v___x_3335_; 
lean_del_object(v___x_3329_);
lean_inc_ref(v_c_3302_);
v___x_3335_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3302_, v___y_3323_, v___y_3322_, v___y_3324_, v___y_3319_, v___y_3318_, v___y_3321_, v___y_3316_, v___y_3320_, v___y_3315_, v___y_3317_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3344_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3344_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3302_, v_a_3336_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3340_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
lean_dec_ref(v_c_3302_);
return v___x_3335_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_c_3302_);
v_a_3346_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3326_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3326_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3354_ = lean_unsigned_to_nat(1u);
v___x_3355_ = l_Lean_Expr_getAppNumArgs(v_c_3302_);
v___x_3356_ = lean_nat_sub(v___x_3355_, v___x_3354_);
lean_dec(v___x_3355_);
v___x_3357_ = lean_nat_sub(v___x_3356_, v___x_3354_);
lean_dec(v___x_3356_);
v___x_3358_ = l_Lean_Expr_getRevArg_x21(v_c_3302_, v___x_3357_);
lean_dec_ref(v_c_3302_);
v___x_3359_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec(v_a_3449_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3461_, lean_object* v_major_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3463_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; uint8_t v_trace_3472_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v_trace_3472_ = lean_ctor_get_uint8(v_a_3471_, sizeof(void*)*14);
lean_dec(v_a_3471_);
if (v_trace_3472_ == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_Grind_cases(v_mvarId_3461_, v_major_3462_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; 
lean_inc(v_a_3468_);
lean_inc_ref(v_a_3467_);
lean_inc(v_a_3466_);
lean_inc_ref(v_a_3465_);
lean_inc_ref(v_major_3462_);
v___x_3474_ = lean_infer_type(v_major_3462_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l_Lean_Meta_whnfD(v_a_3475_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v___x_3478_ = l_Lean_Expr_getAppFn(v_a_3477_);
lean_dec(v_a_3477_);
if (lean_obj_tag(v___x_3478_) == 4)
{
lean_object* v_declName_3479_; lean_object* v___x_3480_; 
v_declName_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_declName_3479_);
lean_dec_ref_known(v___x_3478_, 2);
v___x_3480_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3479_, v_a_3464_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref_known(v___x_3480_, 1);
v___x_3481_ = l_Lean_Meta_Grind_cases(v_mvarId_3461_, v_major_3462_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
return v___x_3481_;
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_major_3462_);
lean_dec(v_mvarId_3461_);
v_a_3482_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3480_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v___x_3490_; 
lean_dec_ref(v___x_3478_);
v___x_3490_ = l_Lean_Meta_Grind_cases(v_mvarId_3461_, v_major_3462_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
return v___x_3490_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_major_3462_);
lean_dec(v_mvarId_3461_);
v_a_3491_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3476_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3476_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v_major_3462_);
lean_dec(v_mvarId_3461_);
v_a_3499_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3474_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3474_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v_major_3462_);
lean_dec(v_mvarId_3461_);
v_a_3507_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3470_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3470_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3515_, lean_object* v_major_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3515_, v_major_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3525_, lean_object* v_major_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3525_, v_major_3526_, v_a_3529_, v_a_3530_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3539_, lean_object* v_major_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3539_, v_major_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec(v_a_3541_);
return v_res_3552_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3553_){
_start:
{
uint64_t v_anchor_3554_; 
v_anchor_3554_ = lean_ctor_get_uint64(v_e_3553_, sizeof(void*)*3);
return v_anchor_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3555_){
_start:
{
uint64_t v_res_3556_; lean_object* v_r_3557_; 
v_res_3556_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3555_);
lean_dec_ref(v_e_3555_);
v_r_3557_ = lean_box_uint64(v_res_3556_);
return v_r_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3560_, lean_object* v_x_3561_){
_start:
{
if (lean_obj_tag(v_x_3561_) == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_box(0);
return v___x_3562_;
}
else
{
lean_object* v_key_3563_; lean_object* v_value_3564_; lean_object* v_tail_3565_; uint64_t v___x_3566_; uint8_t v___x_3567_; 
v_key_3563_ = lean_ctor_get(v_x_3561_, 0);
v_value_3564_ = lean_ctor_get(v_x_3561_, 1);
v_tail_3565_ = lean_ctor_get(v_x_3561_, 2);
v___x_3566_ = lean_unbox_uint64(v_key_3563_);
v___x_3567_ = lean_uint64_dec_eq(v___x_3566_, v_a_3560_);
if (v___x_3567_ == 0)
{
v_x_3561_ = v_tail_3565_;
goto _start;
}
else
{
lean_object* v___x_3569_; 
lean_inc(v_value_3564_);
v___x_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_value_3564_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
uint64_t v_a_boxed_3572_; lean_object* v_res_3573_; 
v_a_boxed_3572_ = lean_unbox_uint64(v_a_3570_);
lean_dec_ref(v_a_3570_);
v_res_3573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3572_, v_x_3571_);
lean_dec(v_x_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3574_, uint64_t v_a_3575_){
_start:
{
lean_object* v_buckets_3576_; lean_object* v___x_3577_; uint64_t v___x_3578_; uint64_t v___x_3579_; uint64_t v_fold_3580_; uint64_t v___x_3581_; uint64_t v___x_3582_; uint64_t v___x_3583_; size_t v___x_3584_; size_t v___x_3585_; size_t v___x_3586_; size_t v___x_3587_; size_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_buckets_3576_ = lean_ctor_get(v_m_3574_, 1);
v___x_3577_ = lean_array_get_size(v_buckets_3576_);
v___x_3578_ = 32ULL;
v___x_3579_ = lean_uint64_shift_right(v_a_3575_, v___x_3578_);
v_fold_3580_ = lean_uint64_xor(v_a_3575_, v___x_3579_);
v___x_3581_ = 16ULL;
v___x_3582_ = lean_uint64_shift_right(v_fold_3580_, v___x_3581_);
v___x_3583_ = lean_uint64_xor(v_fold_3580_, v___x_3582_);
v___x_3584_ = lean_uint64_to_usize(v___x_3583_);
v___x_3585_ = lean_usize_of_nat(v___x_3577_);
v___x_3586_ = ((size_t)1ULL);
v___x_3587_ = lean_usize_sub(v___x_3585_, v___x_3586_);
v___x_3588_ = lean_usize_land(v___x_3584_, v___x_3587_);
v___x_3589_ = lean_array_uget_borrowed(v_buckets_3576_, v___x_3588_);
v___x_3590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3575_, v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3591_, lean_object* v_a_3592_){
_start:
{
uint64_t v_a_boxed_3593_; lean_object* v_res_3594_; 
v_a_boxed_3593_ = lean_unbox_uint64(v_a_3592_);
lean_dec_ref(v_a_3592_);
v_res_3594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3591_, v_a_boxed_3593_);
lean_dec_ref(v_m_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
return v_x_3595_;
}
else
{
lean_object* v_key_3597_; lean_object* v_value_3598_; lean_object* v_tail_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3623_; 
v_key_3597_ = lean_ctor_get(v_x_3596_, 0);
v_value_3598_ = lean_ctor_get(v_x_3596_, 1);
v_tail_3599_ = lean_ctor_get(v_x_3596_, 2);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_x_3596_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3601_ = v_x_3596_;
v_isShared_3602_ = v_isSharedCheck_3623_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_tail_3599_);
lean_inc(v_value_3598_);
lean_inc(v_key_3597_);
lean_dec(v_x_3596_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3623_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; uint64_t v___x_3604_; uint64_t v___x_3605_; uint64_t v___x_3606_; uint64_t v___x_3607_; uint64_t v_fold_3608_; uint64_t v___x_3609_; uint64_t v___x_3610_; uint64_t v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; size_t v___x_3614_; size_t v___x_3615_; size_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3603_ = lean_array_get_size(v_x_3595_);
v___x_3604_ = 32ULL;
v___x_3605_ = lean_unbox_uint64(v_key_3597_);
v___x_3606_ = lean_uint64_shift_right(v___x_3605_, v___x_3604_);
v___x_3607_ = lean_unbox_uint64(v_key_3597_);
v_fold_3608_ = lean_uint64_xor(v___x_3607_, v___x_3606_);
v___x_3609_ = 16ULL;
v___x_3610_ = lean_uint64_shift_right(v_fold_3608_, v___x_3609_);
v___x_3611_ = lean_uint64_xor(v_fold_3608_, v___x_3610_);
v___x_3612_ = lean_uint64_to_usize(v___x_3611_);
v___x_3613_ = lean_usize_of_nat(v___x_3603_);
v___x_3614_ = ((size_t)1ULL);
v___x_3615_ = lean_usize_sub(v___x_3613_, v___x_3614_);
v___x_3616_ = lean_usize_land(v___x_3612_, v___x_3615_);
v___x_3617_ = lean_array_uget_borrowed(v_x_3595_, v___x_3616_);
lean_inc(v___x_3617_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 2, v___x_3617_);
v___x_3619_ = v___x_3601_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_key_3597_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_value_3598_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_array_uset(v_x_3595_, v___x_3616_, v___x_3619_);
v_x_3595_ = v___x_3620_;
v_x_3596_ = v_tail_3599_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3624_, lean_object* v_source_3625_, lean_object* v_target_3626_){
_start:
{
lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3627_ = lean_array_get_size(v_source_3625_);
v___x_3628_ = lean_nat_dec_lt(v_i_3624_, v___x_3627_);
if (v___x_3628_ == 0)
{
lean_dec_ref(v_source_3625_);
lean_dec(v_i_3624_);
return v_target_3626_;
}
else
{
lean_object* v_es_3629_; lean_object* v___x_3630_; lean_object* v_source_3631_; lean_object* v_target_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_es_3629_ = lean_array_fget(v_source_3625_, v_i_3624_);
v___x_3630_ = lean_box(0);
v_source_3631_ = lean_array_fset(v_source_3625_, v_i_3624_, v___x_3630_);
v_target_3632_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3626_, v_es_3629_);
v___x_3633_ = lean_unsigned_to_nat(1u);
v___x_3634_ = lean_nat_add(v_i_3624_, v___x_3633_);
lean_dec(v_i_3624_);
v_i_3624_ = v___x_3634_;
v_source_3625_ = v_source_3631_;
v_target_3626_ = v_target_3632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3636_){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v_nbuckets_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3637_ = lean_array_get_size(v_data_3636_);
v___x_3638_ = lean_unsigned_to_nat(2u);
v_nbuckets_3639_ = lean_nat_mul(v___x_3637_, v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_mk_array(v_nbuckets_3639_, v___x_3641_);
v___x_3643_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3640_, v_data_3636_, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3644_, lean_object* v_b_3645_, lean_object* v_x_3646_){
_start:
{
if (lean_obj_tag(v_x_3646_) == 0)
{
lean_dec(v_b_3645_);
return v_x_3646_;
}
else
{
lean_object* v_key_3647_; lean_object* v_value_3648_; lean_object* v_tail_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3663_; 
v_key_3647_ = lean_ctor_get(v_x_3646_, 0);
v_value_3648_ = lean_ctor_get(v_x_3646_, 1);
v_tail_3649_ = lean_ctor_get(v_x_3646_, 2);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_x_3646_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3651_ = v_x_3646_;
v_isShared_3652_ = v_isSharedCheck_3663_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_tail_3649_);
lean_inc(v_value_3648_);
lean_inc(v_key_3647_);
lean_dec(v_x_3646_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3663_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
uint64_t v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = lean_unbox_uint64(v_key_3647_);
v___x_3654_ = lean_uint64_dec_eq(v___x_3653_, v_a_3644_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3644_, v_b_3645_, v_tail_3649_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 2, v___x_3655_);
v___x_3657_ = v___x_3651_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_key_3647_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_value_3648_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_dec(v_value_3648_);
lean_dec(v_key_3647_);
v___x_3659_ = lean_box_uint64(v_a_3644_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v_b_3645_);
lean_ctor_set(v___x_3651_, 0, v___x_3659_);
v___x_3661_ = v___x_3651_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_b_3645_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_tail_3649_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3664_, lean_object* v_b_3665_, lean_object* v_x_3666_){
_start:
{
uint64_t v_a_boxed_3667_; lean_object* v_res_3668_; 
v_a_boxed_3667_ = lean_unbox_uint64(v_a_3664_);
lean_dec_ref(v_a_3664_);
v_res_3668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3667_, v_b_3665_, v_x_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3669_, lean_object* v_x_3670_){
_start:
{
if (lean_obj_tag(v_x_3670_) == 0)
{
uint8_t v___x_3671_; 
v___x_3671_ = 0;
return v___x_3671_;
}
else
{
lean_object* v_key_3672_; lean_object* v_tail_3673_; uint64_t v___x_3674_; uint8_t v___x_3675_; 
v_key_3672_ = lean_ctor_get(v_x_3670_, 0);
v_tail_3673_ = lean_ctor_get(v_x_3670_, 2);
v___x_3674_ = lean_unbox_uint64(v_key_3672_);
v___x_3675_ = lean_uint64_dec_eq(v___x_3674_, v_a_3669_);
if (v___x_3675_ == 0)
{
v_x_3670_ = v_tail_3673_;
goto _start;
}
else
{
return v___x_3675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3677_, lean_object* v_x_3678_){
_start:
{
uint64_t v_a_boxed_3679_; uint8_t v_res_3680_; lean_object* v_r_3681_; 
v_a_boxed_3679_ = lean_unbox_uint64(v_a_3677_);
lean_dec_ref(v_a_3677_);
v_res_3680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3679_, v_x_3678_);
lean_dec(v_x_3678_);
v_r_3681_ = lean_box(v_res_3680_);
return v_r_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3682_, uint64_t v_a_3683_, lean_object* v_b_3684_){
_start:
{
lean_object* v_size_3685_; lean_object* v_buckets_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3729_; 
v_size_3685_ = lean_ctor_get(v_m_3682_, 0);
v_buckets_3686_ = lean_ctor_get(v_m_3682_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_m_3682_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3688_ = v_m_3682_;
v_isShared_3689_ = v_isSharedCheck_3729_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_buckets_3686_);
lean_inc(v_size_3685_);
lean_dec(v_m_3682_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3729_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; uint64_t v___x_3691_; uint64_t v___x_3692_; uint64_t v_fold_3693_; uint64_t v___x_3694_; uint64_t v___x_3695_; uint64_t v___x_3696_; size_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; lean_object* v_bkt_3702_; uint8_t v___x_3703_; 
v___x_3690_ = lean_array_get_size(v_buckets_3686_);
v___x_3691_ = 32ULL;
v___x_3692_ = lean_uint64_shift_right(v_a_3683_, v___x_3691_);
v_fold_3693_ = lean_uint64_xor(v_a_3683_, v___x_3692_);
v___x_3694_ = 16ULL;
v___x_3695_ = lean_uint64_shift_right(v_fold_3693_, v___x_3694_);
v___x_3696_ = lean_uint64_xor(v_fold_3693_, v___x_3695_);
v___x_3697_ = lean_uint64_to_usize(v___x_3696_);
v___x_3698_ = lean_usize_of_nat(v___x_3690_);
v___x_3699_ = ((size_t)1ULL);
v___x_3700_ = lean_usize_sub(v___x_3698_, v___x_3699_);
v___x_3701_ = lean_usize_land(v___x_3697_, v___x_3700_);
v_bkt_3702_ = lean_array_uget_borrowed(v_buckets_3686_, v___x_3701_);
v___x_3703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3683_, v_bkt_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v_size_x27_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_buckets_x27_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3704_ = lean_unsigned_to_nat(1u);
v_size_x27_3705_ = lean_nat_add(v_size_3685_, v___x_3704_);
lean_dec(v_size_3685_);
v___x_3706_ = lean_box_uint64(v_a_3683_);
lean_inc(v_bkt_3702_);
v___x_3707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v_b_3684_);
lean_ctor_set(v___x_3707_, 2, v_bkt_3702_);
v_buckets_x27_3708_ = lean_array_uset(v_buckets_3686_, v___x_3701_, v___x_3707_);
v___x_3709_ = lean_unsigned_to_nat(4u);
v___x_3710_ = lean_nat_mul(v_size_x27_3705_, v___x_3709_);
v___x_3711_ = lean_unsigned_to_nat(3u);
v___x_3712_ = lean_nat_div(v___x_3710_, v___x_3711_);
lean_dec(v___x_3710_);
v___x_3713_ = lean_array_get_size(v_buckets_x27_3708_);
v___x_3714_ = lean_nat_dec_le(v___x_3712_, v___x_3713_);
lean_dec(v___x_3712_);
if (v___x_3714_ == 0)
{
lean_object* v_val_3715_; lean_object* v___x_3717_; 
v_val_3715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3708_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v_val_3715_);
lean_ctor_set(v___x_3688_, 0, v_size_x27_3705_);
v___x_3717_ = v___x_3688_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_size_x27_3705_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_val_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
else
{
lean_object* v___x_3720_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v_buckets_x27_3708_);
lean_ctor_set(v___x_3688_, 0, v_size_x27_3705_);
v___x_3720_ = v___x_3688_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_size_x27_3705_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_buckets_x27_3708_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_object* v___x_3722_; lean_object* v_buckets_x27_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_inc(v_bkt_3702_);
v___x_3722_ = lean_box(0);
v_buckets_x27_3723_ = lean_array_uset(v_buckets_3686_, v___x_3701_, v___x_3722_);
v___x_3724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3683_, v_b_3684_, v_bkt_3702_);
v___x_3725_ = lean_array_uset(v_buckets_x27_3723_, v___x_3701_, v___x_3724_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v___x_3725_);
v___x_3727_ = v___x_3688_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_size_3685_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3730_, lean_object* v_a_3731_, lean_object* v_b_3732_){
_start:
{
uint64_t v_a_boxed_3733_; lean_object* v_res_3734_; 
v_a_boxed_3733_ = lean_unbox_uint64(v_a_3731_);
lean_dec_ref(v_a_3731_);
v_res_3734_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3730_, v_a_boxed_3733_, v_b_3732_);
return v_res_3734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_box(0);
v___x_3736_ = lean_unsigned_to_nat(16u);
v___x_3737_ = lean_mk_array(v___x_3736_, v___x_3735_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_found_3740_; 
v___x_3738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3739_ = lean_unsigned_to_nat(0u);
v_found_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3740_, 0, v___x_3739_);
lean_ctor_set(v_found_3740_, 1, v___x_3738_);
return v_found_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_found_3741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3742_ = lean_box(0);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v_found_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3744_, lean_object* v_numDigits_3745_, lean_object* v_es_3746_, lean_object* v_as_3747_, size_t v_sz_3748_, size_t v_i_3749_, lean_object* v_b_3750_){
_start:
{
lean_object* v_a_3752_; uint8_t v___x_3756_; 
v___x_3756_ = lean_usize_dec_lt(v_i_3749_, v_sz_3748_);
if (v___x_3756_ == 0)
{
return v_b_3750_;
}
else
{
lean_object* v_snd_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3791_; 
v_snd_3757_ = lean_ctor_get(v_b_3750_, 1);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_b_3750_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; 
v_unused_3792_ = lean_ctor_get(v_b_3750_, 0);
lean_dec(v_unused_3792_);
v___x_3759_ = v_b_3750_;
v_isShared_3760_ = v_isSharedCheck_3791_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_snd_3757_);
lean_dec(v_b_3750_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3791_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_a_3761_; uint64_t v_anchor_3762_; lean_object* v___x_3763_; uint64_t v___x_3764_; uint64_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3761_ = lean_array_uget_borrowed(v_as_3747_, v_i_3749_);
v_anchor_3762_ = lean_ctor_get_uint64(v_a_3761_, sizeof(void*)*3);
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_uint64_of_nat(v_shift_3744_);
v___x_3765_ = lean_uint64_shift_right(v_anchor_3762_, v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3757_, v___x_3765_);
if (lean_obj_tag(v___x_3766_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3785_; 
v_val_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3785_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_val_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3785_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
uint64_t v___x_3771_; uint8_t v___x_3772_; 
v___x_3771_ = lean_unbox_uint64(v_val_3767_);
lean_dec(v_val_3767_);
v___x_3772_ = lean_uint64_dec_eq(v___x_3771_, v_anchor_3762_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3773_ = lean_unsigned_to_nat(1u);
v___x_3774_ = lean_nat_add(v_numDigits_3745_, v___x_3773_);
v___x_3775_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3746_, v___x_3774_);
lean_dec(v___x_3774_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3775_);
v___x_3777_ = v___x_3769_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3777_);
v___x_3779_ = v___x_3759_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_snd_3757_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v___x_3783_; 
lean_del_object(v___x_3769_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3763_);
v___x_3783_ = v___x_3759_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3757_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v_a_3752_ = v___x_3783_;
goto v___jp_3751_;
}
}
}
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_dec(v___x_3766_);
v___x_3786_ = lean_box_uint64(v_anchor_3762_);
v___x_3787_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3757_, v___x_3765_, v___x_3786_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 1, v___x_3787_);
lean_ctor_set(v___x_3759_, 0, v___x_3763_);
v___x_3789_ = v___x_3759_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v_a_3752_ = v___x_3789_;
goto v___jp_3751_;
}
}
}
}
v___jp_3751_:
{
size_t v___x_3753_; size_t v___x_3754_; 
v___x_3753_ = ((size_t)1ULL);
v___x_3754_ = lean_usize_add(v_i_3749_, v___x_3753_);
v_i_3749_ = v___x_3754_;
v_b_3750_ = v_a_3752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3793_, lean_object* v_numDigits_3794_){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3795_ = lean_unsigned_to_nat(4u);
v___x_3796_ = lean_nat_mul(v___x_3795_, v_numDigits_3794_);
v___x_3797_ = lean_unsigned_to_nat(64u);
v___x_3798_ = lean_nat_dec_lt(v___x_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_dec(v___x_3796_);
lean_inc(v_numDigits_3794_);
return v_numDigits_3794_;
}
else
{
lean_object* v_shift_3799_; lean_object* v___x_3800_; size_t v_sz_3801_; size_t v___x_3802_; lean_object* v___x_3803_; lean_object* v_fst_3804_; 
v_shift_3799_ = lean_nat_sub(v___x_3797_, v___x_3796_);
lean_dec(v___x_3796_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3801_ = lean_array_size(v_es_3793_);
v___x_3802_ = ((size_t)0ULL);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3799_, v_numDigits_3794_, v_es_3793_, v_es_3793_, v_sz_3801_, v___x_3802_, v___x_3800_);
lean_dec(v_shift_3799_);
v_fst_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_fst_3804_);
lean_dec_ref(v___x_3803_);
if (lean_obj_tag(v_fst_3804_) == 0)
{
lean_inc(v_numDigits_3794_);
return v_numDigits_3794_;
}
else
{
lean_object* v_val_3805_; 
v_val_3805_ = lean_ctor_get(v_fst_3804_, 0);
lean_inc(v_val_3805_);
lean_dec_ref_known(v_fst_3804_, 1);
return v_val_3805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3806_, lean_object* v_numDigits_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3806_, v_numDigits_3807_);
lean_dec(v_numDigits_3807_);
lean_dec_ref(v_es_3806_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3809_, lean_object* v_numDigits_3810_, lean_object* v_es_3811_, lean_object* v_as_3812_, lean_object* v_sz_3813_, lean_object* v_i_3814_, lean_object* v_b_3815_){
_start:
{
size_t v_sz_boxed_3816_; size_t v_i_boxed_3817_; lean_object* v_res_3818_; 
v_sz_boxed_3816_ = lean_unbox_usize(v_sz_3813_);
lean_dec(v_sz_3813_);
v_i_boxed_3817_ = lean_unbox_usize(v_i_3814_);
lean_dec(v_i_3814_);
v_res_3818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3809_, v_numDigits_3810_, v_es_3811_, v_as_3812_, v_sz_boxed_3816_, v_i_boxed_3817_, v_b_3815_);
lean_dec_ref(v_as_3812_);
lean_dec_ref(v_es_3811_);
lean_dec(v_numDigits_3810_);
lean_dec(v_shift_3809_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3819_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(4u);
v___x_3821_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3819_, v___x_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3822_);
lean_dec_ref(v_es_3822_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3824_, lean_object* v_as_3825_, size_t v_i_3826_, size_t v_stop_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_a_3841_; uint8_t v___x_3845_; 
v___x_3845_ = lean_usize_dec_eq(v_i_3826_, v_stop_3827_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = lean_array_uget_borrowed(v_as_3825_, v_i_3826_);
v___x_3847_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3846_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v_e_3849_; lean_object* v___x_3850_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v_e_3849_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3846_);
lean_inc(v___x_3846_);
v___x_3850_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3846_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
if (lean_obj_tag(v_a_3851_) == 2)
{
lean_object* v_numCases_3852_; uint8_t v_isRec_3853_; lean_object* v___x_3854_; 
v_numCases_3852_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_numCases_3852_);
v_isRec_3853_ = lean_ctor_get_uint8(v_a_3851_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3851_, 1);
lean_inc_ref(v_filter_3824_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc(v___y_3829_);
lean_inc_ref(v_e_3849_);
v___x_3854_ = lean_apply_12(v_filter_3824_, v_e_3849_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, lean_box(0));
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; uint8_t v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = lean_unbox(v_a_3855_);
lean_dec(v_a_3855_);
if (v___x_3856_ == 0)
{
lean_dec(v_numCases_3852_);
lean_dec_ref(v_e_3849_);
lean_dec(v_a_3848_);
v_a_3841_ = v_b_3828_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3857_; uint64_t v___x_3858_; lean_object* v___x_3859_; 
lean_inc(v___x_3846_);
v___x_3857_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3857_, 0, v___x_3846_);
lean_ctor_set(v___x_3857_, 1, v_numCases_3852_);
lean_ctor_set(v___x_3857_, 2, v_e_3849_);
lean_ctor_set_uint8(v___x_3857_, sizeof(void*)*3 + 8, v_isRec_3853_);
v___x_3858_ = lean_unbox_uint64(v_a_3848_);
lean_dec(v_a_3848_);
lean_ctor_set_uint64(v___x_3857_, sizeof(void*)*3, v___x_3858_);
v___x_3859_ = lean_array_push(v_b_3828_, v___x_3857_);
v_a_3841_ = v___x_3859_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_numCases_3852_);
lean_dec_ref(v_e_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_b_3828_);
lean_dec_ref(v_filter_3824_);
v_a_3860_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3854_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3854_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_dec(v_a_3851_);
lean_dec_ref(v_e_3849_);
lean_dec(v_a_3848_);
v_a_3841_ = v_b_3828_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v_e_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_b_3828_);
lean_dec_ref(v_filter_3824_);
v_a_3868_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3850_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3850_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_b_3828_);
lean_dec_ref(v_filter_3824_);
v_a_3876_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3847_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3847_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v___x_3884_; 
lean_dec_ref(v_filter_3824_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v_b_3828_);
return v___x_3884_;
}
v___jp_3840_:
{
size_t v___x_3842_; size_t v___x_3843_; 
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3826_, v___x_3842_);
v_i_3826_ = v___x_3843_;
v_b_3828_ = v_a_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3885_, lean_object* v_as_3886_, lean_object* v_i_3887_, lean_object* v_stop_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
size_t v_i_boxed_3901_; size_t v_stop_boxed_3902_; lean_object* v_res_3903_; 
v_i_boxed_3901_ = lean_unbox_usize(v_i_3887_);
lean_dec(v_i_3887_);
v_stop_boxed_3902_ = lean_unbox_usize(v_stop_3888_);
lean_dec(v_stop_3888_);
v_res_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3885_, v_as_3886_, v_i_boxed_3901_, v_stop_boxed_3902_, v_b_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v_as_3886_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3906_, lean_object* v_as_3907_, lean_object* v_start_3908_, lean_object* v_stop_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3922_ = lean_nat_dec_lt(v_start_3908_, v_stop_3909_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_dec_ref(v_filter_3906_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
return v___x_3923_;
}
else
{
lean_object* v___x_3924_; uint8_t v___x_3925_; 
v___x_3924_ = lean_array_get_size(v_as_3907_);
v___x_3925_ = lean_nat_dec_le(v_stop_3909_, v___x_3924_);
if (v___x_3925_ == 0)
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_lt(v_start_3908_, v___x_3924_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; 
lean_dec_ref(v_filter_3906_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3921_);
return v___x_3927_;
}
else
{
size_t v___x_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = lean_usize_of_nat(v_start_3908_);
v___x_3929_ = lean_usize_of_nat(v___x_3924_);
v___x_3930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3906_, v_as_3907_, v___x_3928_, v___x_3929_, v___x_3921_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
return v___x_3930_;
}
}
else
{
size_t v___x_3931_; size_t v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = lean_usize_of_nat(v_start_3908_);
v___x_3932_ = lean_usize_of_nat(v_stop_3909_);
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3906_, v_as_3907_, v___x_3931_, v___x_3932_, v___x_3921_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
return v___x_3933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3934_, lean_object* v_as_3935_, lean_object* v_start_3936_, lean_object* v_stop_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3934_, v_as_3935_, v_start_3936_, v_stop_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec(v_stop_3937_);
lean_dec(v_start_3936_);
lean_dec_ref(v_as_3935_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3950_, lean_object* v_candidates_x3f_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_candidates_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; 
if (lean_obj_tag(v_candidates_x3f_3951_) == 0)
{
lean_object* v___x_3997_; lean_object* v_toGoalState_3998_; lean_object* v_split_3999_; lean_object* v_candidates_4000_; 
v___x_3997_ = lean_st_ref_get(v_a_3952_);
v_toGoalState_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc_ref(v_toGoalState_3998_);
lean_dec(v___x_3997_);
v_split_3999_ = lean_ctor_get(v_toGoalState_3998_, 14);
lean_inc_ref(v_split_3999_);
lean_dec_ref(v_toGoalState_3998_);
v_candidates_4000_ = lean_ctor_get(v_split_3999_, 1);
lean_inc(v_candidates_4000_);
lean_dec_ref(v_split_3999_);
v_candidates_3964_ = v_candidates_4000_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
v___y_3970_ = v_a_3957_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
v___y_3973_ = v_a_3960_;
v___y_3974_ = v_a_3961_;
goto v___jp_3963_;
}
else
{
lean_object* v_val_4001_; 
v_val_4001_ = lean_ctor_get(v_candidates_x3f_3951_, 0);
lean_inc(v_val_4001_);
lean_dec_ref_known(v_candidates_x3f_3951_, 1);
v_candidates_3964_ = v_val_4001_;
v___y_3965_ = v_a_3952_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
v___y_3970_ = v_a_3957_;
v___y_3971_ = v_a_3958_;
v___y_3972_ = v_a_3959_;
v___y_3973_ = v_a_3960_;
v___y_3974_ = v_a_3961_;
goto v___jp_3963_;
}
v___jp_3963_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3975_ = lean_array_mk(v_candidates_3964_);
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = lean_array_get_size(v___x_3975_);
v___x_3978_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3950_, v___x_3975_, v___x_3976_, v___x_3977_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec_ref(v___x_3975_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3988_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_3988_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3988_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3983_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3979_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_a_3979_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3984_);
v___x_3986_ = v___x_3981_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3978_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3978_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4002_, lean_object* v_candidates_x3f_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4002_, v_candidates_x3f_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec(v_a_4004_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4016_, lean_object* v_m_4017_, uint64_t v_a_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4017_, v_a_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4020_, lean_object* v_m_4021_, lean_object* v_a_4022_){
_start:
{
uint64_t v_a_boxed_4023_; lean_object* v_res_4024_; 
v_a_boxed_4023_ = lean_unbox_uint64(v_a_4022_);
lean_dec_ref(v_a_4022_);
v_res_4024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4020_, v_m_4021_, v_a_boxed_4023_);
lean_dec_ref(v_m_4021_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4025_, lean_object* v_m_4026_, uint64_t v_a_4027_, lean_object* v_b_4028_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4026_, v_a_4027_, v_b_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4030_, lean_object* v_m_4031_, lean_object* v_a_4032_, lean_object* v_b_4033_){
_start:
{
uint64_t v_a_boxed_4034_; lean_object* v_res_4035_; 
v_a_boxed_4034_ = lean_unbox_uint64(v_a_4032_);
lean_dec_ref(v_a_4032_);
v_res_4035_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4030_, v_m_4031_, v_a_boxed_4034_, v_b_4033_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4036_, uint64_t v_a_4037_, lean_object* v_x_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4037_, v_x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4040_, lean_object* v_a_4041_, lean_object* v_x_4042_){
_start:
{
uint64_t v_a_boxed_4043_; lean_object* v_res_4044_; 
v_a_boxed_4043_ = lean_unbox_uint64(v_a_4041_);
lean_dec_ref(v_a_4041_);
v_res_4044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4040_, v_a_boxed_4043_, v_x_4042_);
lean_dec(v_x_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4045_, uint64_t v_a_4046_, lean_object* v_x_4047_){
_start:
{
uint8_t v___x_4048_; 
v___x_4048_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4046_, v_x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4049_, lean_object* v_a_4050_, lean_object* v_x_4051_){
_start:
{
uint64_t v_a_boxed_4052_; uint8_t v_res_4053_; lean_object* v_r_4054_; 
v_a_boxed_4052_ = lean_unbox_uint64(v_a_4050_);
lean_dec_ref(v_a_4050_);
v_res_4053_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4049_, v_a_boxed_4052_, v_x_4051_);
lean_dec(v_x_4051_);
v_r_4054_ = lean_box(v_res_4053_);
return v_r_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4055_, lean_object* v_data_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4058_, uint64_t v_a_4059_, lean_object* v_b_4060_, lean_object* v_x_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4059_, v_b_4060_, v_x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4063_, lean_object* v_a_4064_, lean_object* v_b_4065_, lean_object* v_x_4066_){
_start:
{
uint64_t v_a_boxed_4067_; lean_object* v_res_4068_; 
v_a_boxed_4067_ = lean_unbox_uint64(v_a_4064_);
lean_dec_ref(v_a_4064_);
v_res_4068_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4063_, v_a_boxed_4067_, v_b_4065_, v_x_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4069_, lean_object* v_i_4070_, lean_object* v_source_4071_, lean_object* v_target_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4070_, v_source_4071_, v_target_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4074_, lean_object* v_x_4075_, lean_object* v_x_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4075_, v_x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4090_ = 1;
v___x_4091_ = lean_box(v___x_4090_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v_x_4093_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4106_, uint64_t v_a_4107_, lean_object* v_c_4108_, lean_object* v_numDigits_4109_, lean_object* v_as_4110_, size_t v_sz_4111_, size_t v_i_4112_, lean_object* v_b_4113_){
_start:
{
lean_object* v_a_4116_; uint8_t v___x_4120_; 
v___x_4120_ = lean_usize_dec_lt(v_i_4112_, v_sz_4111_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; 
lean_dec(v_numDigits_4109_);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_b_4113_);
return v___x_4121_;
}
else
{
lean_object* v_snd_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4148_; 
v_snd_4122_ = lean_ctor_get(v_b_4113_, 1);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_b_4113_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; 
v_unused_4149_ = lean_ctor_get(v_b_4113_, 0);
lean_dec(v_unused_4149_);
v___x_4124_ = v_b_4113_;
v_isShared_4125_ = v_isSharedCheck_4148_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_snd_4122_);
lean_dec(v_b_4113_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4148_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v_a_4126_; lean_object* v_c_4127_; uint64_t v_anchor_4128_; lean_object* v___x_4129_; uint64_t v___x_4130_; uint64_t v___x_4131_; uint8_t v___x_4132_; 
v_a_4126_ = lean_array_uget_borrowed(v_as_4110_, v_i_4112_);
v_c_4127_ = lean_ctor_get(v_a_4126_, 0);
v_anchor_4128_ = lean_ctor_get_uint64(v_a_4126_, sizeof(void*)*3);
v___x_4129_ = lean_box(0);
v___x_4130_ = lean_uint64_shift_right(v_anchor_4128_, v___x_4106_);
v___x_4131_ = lean_uint64_shift_right(v_a_4107_, v___x_4106_);
v___x_4132_ = lean_uint64_dec_eq(v___x_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4134_; 
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4129_);
v___x_4134_ = v___x_4124_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_snd_4122_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v_a_4116_ = v___x_4134_;
goto v___jp_4115_;
}
}
else
{
uint8_t v___x_4136_; 
v___x_4136_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4127_, v_c_4108_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4137_ = lean_unsigned_to_nat(1u);
v___x_4138_ = lean_nat_add(v_snd_4122_, v___x_4137_);
lean_dec(v_snd_4122_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 1, v___x_4138_);
lean_ctor_set(v___x_4124_, 0, v___x_4129_);
v___x_4140_ = v___x_4124_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
v_a_4116_ = v___x_4140_;
goto v___jp_4115_;
}
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
lean_inc(v_snd_4122_);
v___x_4142_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4142_, 0, v_numDigits_4109_);
lean_ctor_set(v___x_4142_, 1, v_snd_4122_);
lean_ctor_set_uint64(v___x_4142_, sizeof(void*)*2, v_a_4107_);
v___x_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4143_);
v___x_4145_ = v___x_4124_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4143_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_snd_4122_);
v___x_4145_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
}
}
}
v___jp_4115_:
{
size_t v___x_4117_; size_t v___x_4118_; 
v___x_4117_ = ((size_t)1ULL);
v___x_4118_ = lean_usize_add(v_i_4112_, v___x_4117_);
v_i_4112_ = v___x_4118_;
v_b_4113_ = v_a_4116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4150_, lean_object* v_a_4151_, lean_object* v_c_4152_, lean_object* v_numDigits_4153_, lean_object* v_as_4154_, lean_object* v_sz_4155_, lean_object* v_i_4156_, lean_object* v_b_4157_, lean_object* v___y_4158_){
_start:
{
uint64_t v___x_7681__boxed_4159_; uint64_t v_a_7682__boxed_4160_; size_t v_sz_boxed_4161_; size_t v_i_boxed_4162_; lean_object* v_res_4163_; 
v___x_7681__boxed_4159_ = lean_unbox_uint64(v___x_4150_);
lean_dec_ref(v___x_4150_);
v_a_7682__boxed_4160_ = lean_unbox_uint64(v_a_4151_);
lean_dec_ref(v_a_4151_);
v_sz_boxed_4161_ = lean_unbox_usize(v_sz_4155_);
lean_dec(v_sz_4155_);
v_i_boxed_4162_ = lean_unbox_usize(v_i_4156_);
lean_dec(v_i_4156_);
v_res_4163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7681__boxed_4159_, v_a_7682__boxed_4160_, v_c_4152_, v_numDigits_4153_, v_as_4154_, v_sz_boxed_4161_, v_i_boxed_4162_, v_b_4157_);
lean_dec_ref(v_as_4154_);
lean_dec_ref(v_c_4152_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4168_, lean_object* v_candidates_x3f_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v___f_4181_; lean_object* v___x_4182_; 
v___f_4181_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4182_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4181_, v_candidates_x3f_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_candidates_4184_; lean_object* v_numDigits_4185_; lean_object* v___x_4186_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v_candidates_4184_ = lean_ctor_get(v_a_4183_, 0);
lean_inc_ref(v_candidates_4184_);
v_numDigits_4185_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_numDigits_4185_);
lean_dec(v_a_4183_);
v___x_4186_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4168_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; uint64_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; size_t v_sz_4195_; size_t v___x_4196_; uint64_t v___x_4197_; lean_object* v___x_4198_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v___x_4188_ = lean_unsigned_to_nat(64u);
v___x_4189_ = lean_unsigned_to_nat(4u);
v___x_4190_ = lean_nat_mul(v___x_4189_, v_numDigits_4185_);
v___x_4191_ = lean_nat_sub(v___x_4188_, v___x_4190_);
lean_dec(v___x_4190_);
v___x_4192_ = lean_uint64_of_nat(v___x_4191_);
lean_dec(v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4195_ = lean_array_size(v_candidates_4184_);
v___x_4196_ = ((size_t)0ULL);
v___x_4197_ = lean_unbox_uint64(v_a_4187_);
lean_inc(v_numDigits_4185_);
v___x_4198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4192_, v___x_4197_, v_c_4168_, v_numDigits_4185_, v_candidates_4184_, v_sz_4195_, v___x_4196_, v___x_4194_);
lean_dec_ref(v_candidates_4184_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4213_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4201_ = v___x_4198_;
v_isShared_4202_ = v_isSharedCheck_4213_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4198_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4213_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v_fst_4203_; 
v_fst_4203_ = lean_ctor_get(v_a_4199_, 0);
lean_inc(v_fst_4203_);
lean_dec(v_a_4199_);
if (lean_obj_tag(v_fst_4203_) == 0)
{
lean_object* v___x_4204_; uint64_t v___x_4205_; lean_object* v___x_4207_; 
v___x_4204_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4204_, 0, v_numDigits_4185_);
lean_ctor_set(v___x_4204_, 1, v___x_4193_);
v___x_4205_ = lean_unbox_uint64(v_a_4187_);
lean_dec(v_a_4187_);
lean_ctor_set_uint64(v___x_4204_, sizeof(void*)*2, v___x_4205_);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 0, v___x_4204_);
v___x_4207_ = v___x_4201_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4204_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
else
{
lean_object* v_val_4209_; lean_object* v___x_4211_; 
lean_dec(v_a_4187_);
lean_dec(v_numDigits_4185_);
v_val_4209_ = lean_ctor_get(v_fst_4203_, 0);
lean_inc(v_val_4209_);
lean_dec_ref_known(v_fst_4203_, 1);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 0, v_val_4209_);
v___x_4211_ = v___x_4201_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_val_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v_a_4187_);
lean_dec(v_numDigits_4185_);
v_a_4214_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4198_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4198_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_numDigits_4185_);
lean_dec_ref(v_candidates_4184_);
v_a_4222_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4186_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4186_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
v_a_4230_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4182_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4182_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4238_, lean_object* v_candidates_x3f_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4238_, v_candidates_x3f_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_c_4238_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4252_, uint64_t v_a_4253_, lean_object* v_c_4254_, lean_object* v_numDigits_4255_, lean_object* v_as_4256_, size_t v_sz_4257_, size_t v_i_4258_, lean_object* v_b_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4252_, v_a_4253_, v_c_4254_, v_numDigits_4255_, v_as_4256_, v_sz_4257_, v_i_4258_, v_b_4259_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4272_ = _args[0];
lean_object* v_a_4273_ = _args[1];
lean_object* v_c_4274_ = _args[2];
lean_object* v_numDigits_4275_ = _args[3];
lean_object* v_as_4276_ = _args[4];
lean_object* v_sz_4277_ = _args[5];
lean_object* v_i_4278_ = _args[6];
lean_object* v_b_4279_ = _args[7];
lean_object* v___y_4280_ = _args[8];
lean_object* v___y_4281_ = _args[9];
lean_object* v___y_4282_ = _args[10];
lean_object* v___y_4283_ = _args[11];
lean_object* v___y_4284_ = _args[12];
lean_object* v___y_4285_ = _args[13];
lean_object* v___y_4286_ = _args[14];
lean_object* v___y_4287_ = _args[15];
lean_object* v___y_4288_ = _args[16];
lean_object* v___y_4289_ = _args[17];
lean_object* v___y_4290_ = _args[18];
_start:
{
uint64_t v___x_7880__boxed_4291_; uint64_t v_a_7881__boxed_4292_; size_t v_sz_boxed_4293_; size_t v_i_boxed_4294_; lean_object* v_res_4295_; 
v___x_7880__boxed_4291_ = lean_unbox_uint64(v___x_4272_);
lean_dec_ref(v___x_4272_);
v_a_7881__boxed_4292_ = lean_unbox_uint64(v_a_4273_);
lean_dec_ref(v_a_4273_);
v_sz_boxed_4293_ = lean_unbox_usize(v_sz_4277_);
lean_dec(v_sz_4277_);
v_i_boxed_4294_ = lean_unbox_usize(v_i_4278_);
lean_dec(v_i_4278_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7880__boxed_4291_, v_a_7881__boxed_4292_, v_c_4274_, v_numDigits_4275_, v_as_4276_, v_sz_boxed_4293_, v_i_boxed_4294_, v_b_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v_as_4276_);
lean_dec_ref(v_c_4274_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_numDigits_4323_; uint64_t v_anchor_4324_; lean_object* v_ordinal_4325_; lean_object* v___x_4326_; 
v_numDigits_4323_ = lean_ctor_get(v_info_4320_, 0);
v_anchor_4324_ = lean_ctor_get_uint64(v_info_4320_, sizeof(void*)*2);
v_ordinal_4325_ = lean_ctor_get(v_info_4320_, 1);
v___x_4326_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4323_, v_anchor_4324_, v_a_4321_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4363_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4363_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4363_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4331_ = lean_unsigned_to_nat(0u);
v___x_4332_ = lean_nat_dec_eq(v_ordinal_4325_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_object* v_ref_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v_ref_4333_ = lean_ctor_get(v_a_4321_, 5);
v___x_4334_ = l_Lean_SourceInfo_fromRef(v_ref_4333_, v___x_4332_);
v___x_4335_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4336_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4334_, 3);
v___x_4337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4334_);
lean_ctor_set(v___x_4337_, 1, v___x_4335_);
v___x_4338_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4339_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4334_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = lean_unsigned_to_nat(1u);
v___x_4342_ = lean_nat_add(v_ordinal_4325_, v___x_4341_);
v___x_4343_ = l_Nat_reprFast(v___x_4342_);
v___x_4344_ = lean_box(2);
v___x_4345_ = l_Lean_Syntax_mkNumLit(v___x_4343_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_node3(v___x_4334_, v___x_4338_, v_a_4327_, v___x_4340_, v___x_4345_);
v___x_4347_ = l_Lean_Syntax_node2(v___x_4334_, v___x_4336_, v___x_4337_, v___x_4346_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4347_);
v___x_4349_ = v___x_4329_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
else
{
lean_object* v_ref_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4361_; 
v_ref_4351_ = lean_ctor_get(v_a_4321_, 5);
v___x_4352_ = 0;
v___x_4353_ = l_Lean_SourceInfo_fromRef(v_ref_4351_, v___x_4352_);
v___x_4354_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4355_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4353_, 2);
v___x_4356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4353_);
lean_ctor_set(v___x_4356_, 1, v___x_4354_);
v___x_4357_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4358_ = l_Lean_Syntax_node1(v___x_4353_, v___x_4357_, v_a_4327_);
v___x_4359_ = l_Lean_Syntax_node2(v___x_4353_, v___x_4355_, v___x_4356_, v___x_4358_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4359_);
v___x_4361_ = v___x_4329_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
else
{
return v___x_4326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4364_, v_a_4365_);
lean_dec_ref(v_a_4365_);
lean_dec_ref(v_info_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4368_, v_a_4369_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4373_, v_a_4374_, v_a_4375_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec_ref(v_info_4373_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_p_4397_; lean_object* v___x_4400_; 
lean_inc_ref(v_proof_4390_);
v___x_4400_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4390_, v_a_4392_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4439_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4439_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4439_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_4421_ = l_Lean_Expr_cleanupAnnotations(v_a_4401_);
v___x_4422_ = l_Lean_Expr_isApp(v___x_4421_);
if (v___x_4422_ == 0)
{
lean_dec_ref(v___x_4421_);
v___y_4406_ = v_a_4391_;
v___y_4407_ = v_a_4392_;
v___y_4408_ = v_a_4393_;
v___y_4409_ = v_a_4394_;
goto v___jp_4405_;
}
else
{
lean_object* v_arg_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_arg_4423_ = lean_ctor_get(v___x_4421_, 1);
lean_inc_ref(v_arg_4423_);
v___x_4424_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4421_);
v___x_4425_ = l_Lean_Expr_isApp(v___x_4424_);
if (v___x_4425_ == 0)
{
lean_dec_ref(v___x_4424_);
lean_dec_ref(v_arg_4423_);
v___y_4406_ = v_a_4391_;
v___y_4407_ = v_a_4392_;
v___y_4408_ = v_a_4393_;
v___y_4409_ = v_a_4394_;
goto v___jp_4405_;
}
else
{
lean_object* v_arg_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; uint8_t v___x_4429_; 
v_arg_4426_ = lean_ctor_get(v___x_4424_, 1);
lean_inc_ref(v_arg_4426_);
v___x_4427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4424_);
v___x_4428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4429_ = l_Lean_Expr_isConstOf(v___x_4427_, v___x_4428_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
lean_dec_ref(v_arg_4426_);
v___x_4430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4431_ = l_Lean_Expr_isConstOf(v___x_4427_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4433_ = l_Lean_Expr_isConstOf(v___x_4427_, v___x_4432_);
lean_dec_ref(v___x_4427_);
if (v___x_4433_ == 0)
{
lean_dec_ref(v_arg_4423_);
v___y_4406_ = v_a_4391_;
v___y_4407_ = v_a_4392_;
v___y_4408_ = v_a_4393_;
v___y_4409_ = v_a_4394_;
goto v___jp_4405_;
}
else
{
lean_del_object(v___x_4403_);
lean_dec_ref(v_proof_4390_);
v_p_4397_ = v_arg_4423_;
goto v___jp_4396_;
}
}
else
{
lean_dec_ref(v___x_4427_);
lean_del_object(v___x_4403_);
lean_dec_ref(v_proof_4390_);
v_p_4397_ = v_arg_4423_;
goto v___jp_4396_;
}
}
else
{
uint8_t v___x_4434_; 
lean_dec_ref(v___x_4427_);
lean_del_object(v___x_4403_);
lean_dec_ref(v_proof_4390_);
v___x_4434_ = l_Lean_Expr_isFalse(v_arg_4426_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec_ref(v_arg_4423_);
v___x_4435_ = lean_box(0);
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_arg_4423_);
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
return v___x_4438_;
}
}
}
}
v___jp_4405_:
{
if (lean_obj_tag(v_proof_4390_) == 6)
{
lean_object* v_body_4410_; uint8_t v___x_4411_; 
v_body_4410_ = lean_ctor_get(v_proof_4390_, 2);
lean_inc_ref(v_body_4410_);
lean_dec_ref_known(v_proof_4390_, 3);
v___x_4411_ = l_Lean_Expr_hasLooseBVars(v_body_4410_);
if (v___x_4411_ == 0)
{
lean_del_object(v___x_4403_);
v_proof_4390_ = v_body_4410_;
v_a_4391_ = v___y_4406_;
v_a_4392_ = v___y_4407_;
v_a_4393_ = v___y_4408_;
v_a_4394_ = v___y_4409_;
goto _start;
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4415_; 
lean_dec_ref(v_body_4410_);
v___x_4413_ = lean_box(0);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4413_);
v___x_4415_ = v___x_4403_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4419_; 
lean_dec_ref(v_proof_4390_);
v___x_4417_ = lean_box(0);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4417_);
v___x_4419_ = v___x_4403_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref(v_proof_4390_);
v_a_4440_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4400_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4400_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
v___jp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_p_4397_);
v___x_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4398_);
return v___x_4399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v___x_4458_; 
v___x_4458_ = l_Lean_Expr_hasMVar(v_e_4455_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_e_4455_);
return v___x_4459_;
}
else
{
lean_object* v___x_4460_; lean_object* v_mctx_4461_; lean_object* v___x_4462_; lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___x_4465_; lean_object* v_cache_4466_; lean_object* v_zetaDeltaFVarIds_4467_; lean_object* v_postponed_4468_; lean_object* v_diag_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4478_; 
v___x_4460_ = lean_st_ref_get(v___y_4456_);
v_mctx_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc_ref(v_mctx_4461_);
lean_dec(v___x_4460_);
v___x_4462_ = l_Lean_instantiateMVarsCore(v_mctx_4461_, v_e_4455_);
v_fst_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_fst_4463_);
v_snd_4464_ = lean_ctor_get(v___x_4462_, 1);
lean_inc(v_snd_4464_);
lean_dec_ref(v___x_4462_);
v___x_4465_ = lean_st_ref_take(v___y_4456_);
v_cache_4466_ = lean_ctor_get(v___x_4465_, 1);
v_zetaDeltaFVarIds_4467_ = lean_ctor_get(v___x_4465_, 2);
v_postponed_4468_ = lean_ctor_get(v___x_4465_, 3);
v_diag_4469_ = lean_ctor_get(v___x_4465_, 4);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v___x_4465_, 0);
lean_dec(v_unused_4479_);
v___x_4471_ = v___x_4465_;
v_isShared_4472_ = v_isSharedCheck_4478_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_diag_4469_);
lean_inc(v_postponed_4468_);
lean_inc(v_zetaDeltaFVarIds_4467_);
lean_inc(v_cache_4466_);
lean_dec(v___x_4465_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4478_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v_snd_4464_);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_snd_4464_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_cache_4466_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_zetaDeltaFVarIds_4467_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_postponed_4468_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_diag_4469_);
v___x_4474_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = lean_st_ref_put(v___y_4456_, v___x_4474_);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v_fst_4463_);
return v___x_4476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4480_, v___y_4481_);
lean_dec(v___y_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4484_, v___y_4486_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4498_, lean_object* v_x_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4498_, v_x_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4505_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4505_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_a_4514_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4505_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4505_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4522_, lean_object* v_x_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4522_, v_x_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4530_, lean_object* v_mvarId_4531_, lean_object* v_x_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4531_, v_x_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4539_, lean_object* v_mvarId_4540_, lean_object* v_x_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4539_, v_mvarId_4540_, v_x_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v___x_4554_; lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4565_; 
v___x_4554_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4548_, v___y_4550_);
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4557_ = v___x_4554_;
v_isShared_4558_ = v_isSharedCheck_4565_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4554_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4565_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
uint8_t v___x_4559_; 
v___x_4559_ = l_Lean_Expr_hasSyntheticSorry(v_a_4555_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; 
lean_del_object(v___x_4557_);
v___x_4560_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4555_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4560_;
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4563_; 
lean_dec(v_a_4555_);
v___x_4561_ = lean_box(0);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 0, v___x_4561_);
v___x_4563_ = v___x_4557_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; 
lean_inc(v_mvarId_4573_);
v___x_4579_ = l_Lean_mkMVar(v_mvarId_4573_);
v___f_4580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4580_, 0, v___x_4579_);
v___x_4581_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4573_, v___f_4580_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4610_){
_start:
{
if (lean_obj_tag(v_x_4610_) == 0)
{
uint8_t v___x_4611_; 
v___x_4611_ = 1;
return v___x_4611_;
}
else
{
lean_object* v_head_4612_; lean_object* v_tail_4613_; uint8_t v___y_4615_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v_head_4612_ = lean_ctor_get(v_x_4610_, 0);
lean_inc_n(v_head_4612_, 2);
v_tail_4613_ = lean_ctor_get(v_x_4610_, 1);
lean_inc(v_tail_4613_);
lean_dec_ref_known(v_x_4610_, 2);
v___x_4617_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4618_ = l_Lean_Syntax_isOfKind(v_head_4612_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4619_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4612_);
v___x_4620_ = l_Lean_Syntax_isOfKind(v_head_4612_, v___x_4619_);
if (v___x_4620_ == 0)
{
lean_dec(v_head_4612_);
v_x_4610_ = v_tail_4613_;
goto _start;
}
else
{
if (v___x_4618_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4622_ = lean_unsigned_to_nat(1u);
v___x_4623_ = l_Lean_Syntax_getArg(v_head_4612_, v___x_4622_);
lean_dec(v_head_4612_);
v___x_4624_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4625_ = l_Lean_Syntax_isOfKind(v___x_4623_, v___x_4624_);
if (v___x_4625_ == 0)
{
v_x_4610_ = v_tail_4613_;
goto _start;
}
else
{
v___y_4615_ = v___x_4618_;
goto v___jp_4614_;
}
}
else
{
lean_dec(v_head_4612_);
v___y_4615_ = v___x_4618_;
goto v___jp_4614_;
}
}
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4627_ = lean_unsigned_to_nat(3u);
v___x_4628_ = l_Lean_Syntax_getArg(v_head_4612_, v___x_4627_);
lean_dec(v_head_4612_);
v___x_4629_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4630_ = l_Lean_Syntax_isOfKind(v___x_4628_, v___x_4629_);
if (v___x_4630_ == 0)
{
v_x_4610_ = v_tail_4613_;
goto _start;
}
else
{
uint8_t v___x_4632_; 
lean_dec(v_tail_4613_);
v___x_4632_ = 0;
return v___x_4632_;
}
}
v___jp_4614_:
{
if (v___y_4615_ == 0)
{
lean_dec(v_tail_4613_);
return v___y_4615_;
}
else
{
v_x_4610_ = v_tail_4613_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4633_){
_start:
{
uint8_t v_res_4634_; lean_object* v_r_4635_; 
v_res_4634_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4633_);
v_r_4635_ = lean_box(v_res_4634_);
return v_r_4635_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4636_){
_start:
{
uint8_t v___x_4637_; 
v___x_4637_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4638_){
_start:
{
uint8_t v_res_4639_; lean_object* v_r_4640_; 
v_res_4639_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4638_);
v_r_4640_ = lean_box(v_res_4639_);
return v_r_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4656_, lean_object* v_a_4657_){
_start:
{
if (lean_obj_tag(v_seq_4656_) == 0)
{
lean_object* v_ref_4659_; uint8_t v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v_ref_4659_ = lean_ctor_get(v_a_4657_, 5);
v___x_4660_ = 0;
v___x_4661_ = l_Lean_SourceInfo_fromRef(v_ref_4659_, v___x_4660_);
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4661_);
v___x_4664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4661_);
lean_ctor_set(v___x_4664_, 1, v___x_4662_);
v___x_4665_ = l_Lean_Syntax_node1(v___x_4661_, v___x_4663_, v___x_4664_);
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
return v___x_4666_;
}
else
{
lean_object* v_tail_4667_; 
v_tail_4667_ = lean_ctor_get(v_seq_4656_, 1);
if (lean_obj_tag(v_tail_4667_) == 0)
{
lean_object* v_head_4668_; lean_object* v___x_4669_; 
v_head_4668_ = lean_ctor_get(v_seq_4656_, 0);
lean_inc(v_head_4668_);
lean_dec_ref_known(v_seq_4656_, 2);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v_head_4668_);
return v___x_4669_;
}
else
{
lean_object* v_head_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4692_; 
lean_inc(v_tail_4667_);
v_head_4670_ = lean_ctor_get(v_seq_4656_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_seq_4656_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; 
v_unused_4693_ = lean_ctor_get(v_seq_4656_, 1);
lean_dec(v_unused_4693_);
v___x_4672_ = v_seq_4656_;
v_isShared_4673_ = v_isSharedCheck_4692_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_head_4670_);
lean_dec(v_seq_4656_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4692_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4691_; 
v___x_4674_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4667_, v_a_4657_);
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4677_ = v___x_4674_;
v_isShared_4678_ = v_isSharedCheck_4691_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4674_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4691_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v_ref_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4685_; 
v_ref_4679_ = lean_ctor_get(v_a_4657_, 5);
v___x_4680_ = 0;
v___x_4681_ = l_Lean_SourceInfo_fromRef(v_ref_4679_, v___x_4680_);
v___x_4682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4681_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set_tag(v___x_4672_, 2);
lean_ctor_set(v___x_4672_, 1, v___x_4683_);
lean_ctor_set(v___x_4672_, 0, v___x_4681_);
v___x_4685_ = v___x_4672_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4681_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4686_ = l_Lean_Syntax_node3(v___x_4681_, v___x_4682_, v_head_4670_, v___x_4685_, v_a_4675_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 0, v___x_4686_);
v___x_4688_ = v___x_4677_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4686_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4694_, v_a_4695_);
lean_dec_ref(v_a_4695_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4698_, v_a_4699_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4703_, v_a_4704_, v_a_4705_);
lean_dec(v_a_4705_);
lean_dec_ref(v_a_4704_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4708_, lean_object* v_seq_4709_, lean_object* v_a_4710_){
_start:
{
if (lean_obj_tag(v_seq_4709_) == 0)
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_cases_4708_);
return v___x_4712_;
}
else
{
lean_object* v___x_4713_; lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4728_; 
v___x_4713_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4709_, v_a_4710_);
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4728_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4728_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v_ref_4718_; uint8_t v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4726_; 
v_ref_4718_ = lean_ctor_get(v_a_4710_, 5);
v___x_4719_ = 0;
v___x_4720_ = l_Lean_SourceInfo_fromRef(v_ref_4718_, v___x_4719_);
v___x_4721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4720_);
v___x_4723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4720_);
lean_ctor_set(v___x_4723_, 1, v___x_4722_);
v___x_4724_ = l_Lean_Syntax_node3(v___x_4720_, v___x_4721_, v_cases_4708_, v___x_4723_, v_a_4714_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4724_);
v___x_4726_ = v___x_4716_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4724_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4729_, lean_object* v_seq_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4729_, v_seq_4730_, v_a_4731_);
lean_dec_ref(v_a_4731_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4734_, lean_object* v_seq_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4734_, v_seq_4735_, v_a_4736_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4740_, lean_object* v_seq_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4740_, v_seq_4741_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
return v_res_4745_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4746_, lean_object* v_x_4747_){
_start:
{
if (lean_obj_tag(v_x_4746_) == 0)
{
if (lean_obj_tag(v_x_4747_) == 0)
{
uint8_t v___x_4748_; 
v___x_4748_ = 1;
return v___x_4748_;
}
else
{
uint8_t v___x_4749_; 
v___x_4749_ = 0;
return v___x_4749_;
}
}
else
{
if (lean_obj_tag(v_x_4747_) == 0)
{
uint8_t v___x_4750_; 
v___x_4750_ = 0;
return v___x_4750_;
}
else
{
lean_object* v_head_4751_; lean_object* v_tail_4752_; lean_object* v_head_4753_; lean_object* v_tail_4754_; uint8_t v___x_4755_; 
v_head_4751_ = lean_ctor_get(v_x_4746_, 0);
v_tail_4752_ = lean_ctor_get(v_x_4746_, 1);
v_head_4753_ = lean_ctor_get(v_x_4747_, 0);
v_tail_4754_ = lean_ctor_get(v_x_4747_, 1);
v___x_4755_ = l_Lean_Syntax_structEq(v_head_4751_, v_head_4753_);
if (v___x_4755_ == 0)
{
return v___x_4755_;
}
else
{
v_x_4746_ = v_tail_4752_;
v_x_4747_ = v_tail_4754_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4757_, lean_object* v_x_4758_){
_start:
{
uint8_t v_res_4759_; lean_object* v_r_4760_; 
v_res_4759_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4757_, v_x_4758_);
lean_dec(v_x_4758_);
lean_dec(v_x_4757_);
v_r_4760_ = lean_box(v_res_4759_);
return v_r_4760_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4761_, lean_object* v___x_4762_, lean_object* v_as_4763_, size_t v_i_4764_, size_t v_stop_4765_){
_start:
{
uint8_t v___x_4770_; 
v___x_4770_ = lean_usize_dec_eq(v_i_4764_, v_stop_4765_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; uint8_t v___x_4772_; 
v___x_4771_ = lean_array_uget_borrowed(v_as_4763_, v_i_4764_);
v___x_4772_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4771_, v_alt_4761_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; uint8_t v___x_4774_; 
v___x_4773_ = lean_unsigned_to_nat(0u);
v___x_4774_ = lean_nat_dec_lt(v___x_4773_, v___x_4762_);
if (v___x_4774_ == 0)
{
goto v___jp_4766_;
}
else
{
return v___x_4774_;
}
}
else
{
goto v___jp_4766_;
}
}
else
{
uint8_t v___x_4775_; 
v___x_4775_ = 0;
return v___x_4775_;
}
v___jp_4766_:
{
size_t v___x_4767_; size_t v___x_4768_; 
v___x_4767_ = ((size_t)1ULL);
v___x_4768_ = lean_usize_add(v_i_4764_, v___x_4767_);
v_i_4764_ = v___x_4768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4776_, lean_object* v___x_4777_, lean_object* v_as_4778_, lean_object* v_i_4779_, lean_object* v_stop_4780_){
_start:
{
size_t v_i_boxed_4781_; size_t v_stop_boxed_4782_; uint8_t v_res_4783_; lean_object* v_r_4784_; 
v_i_boxed_4781_ = lean_unbox_usize(v_i_4779_);
lean_dec(v_i_4779_);
v_stop_boxed_4782_ = lean_unbox_usize(v_stop_4780_);
lean_dec(v_stop_4780_);
v_res_4783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4776_, v___x_4777_, v_as_4778_, v_i_boxed_4781_, v_stop_boxed_4782_);
lean_dec_ref(v_as_4778_);
lean_dec(v___x_4777_);
lean_dec(v_alt_4776_);
v_r_4784_ = lean_box(v_res_4783_);
return v_r_4784_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4785_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = lean_unsigned_to_nat(0u);
v___x_4787_ = lean_array_get_size(v_alts_4785_);
v___x_4788_ = lean_nat_dec_lt(v___x_4786_, v___x_4787_);
if (v___x_4788_ == 0)
{
uint8_t v___x_4789_; 
v___x_4789_ = 1;
return v___x_4789_;
}
else
{
lean_object* v_alt_4790_; uint8_t v___x_4791_; 
v_alt_4790_ = lean_array_fget_borrowed(v_alts_4785_, v___x_4786_);
lean_inc(v_alt_4790_);
v___x_4791_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4790_);
if (v___x_4791_ == 0)
{
return v___x_4791_;
}
else
{
if (v___x_4788_ == 0)
{
return v___x_4788_;
}
else
{
if (v___x_4788_ == 0)
{
return v___x_4788_;
}
else
{
size_t v___x_4792_; size_t v___x_4793_; uint8_t v___x_4794_; 
v___x_4792_ = ((size_t)0ULL);
v___x_4793_ = lean_usize_of_nat(v___x_4787_);
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4790_, v___x_4787_, v_alts_4785_, v___x_4792_, v___x_4793_);
if (v___x_4794_ == 0)
{
return v___x_4788_;
}
else
{
uint8_t v___x_4795_; 
v___x_4795_ = 0;
return v___x_4795_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4796_){
_start:
{
uint8_t v_res_4797_; lean_object* v_r_4798_; 
v_res_4797_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4796_);
lean_dec_ref(v_alts_4796_);
v_r_4798_ = lean_box(v_res_4797_);
return v_r_4798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4806_){
_start:
{
if (lean_obj_tag(v_alt_4806_) == 1)
{
lean_object* v_tail_4807_; 
v_tail_4807_ = lean_ctor_get(v_alt_4806_, 1);
if (lean_obj_tag(v_tail_4807_) == 0)
{
lean_object* v_head_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_head_4808_ = lean_ctor_get(v_alt_4806_, 0);
lean_inc(v_head_4808_);
lean_dec_ref_known(v_alt_4806_, 2);
v___x_4809_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4810_ = l_Lean_Syntax_isOfKind(v_head_4808_, v___x_4809_);
return v___x_4810_;
}
else
{
uint8_t v___x_4811_; 
lean_dec_ref_known(v_alt_4806_, 2);
v___x_4811_ = 0;
return v___x_4811_;
}
}
else
{
uint8_t v___x_4812_; 
lean_dec(v_alt_4806_);
v___x_4812_ = 0;
return v___x_4812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4813_){
_start:
{
uint8_t v_res_4814_; lean_object* v_r_4815_; 
v_res_4814_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4813_);
v_r_4815_ = lean_box(v_res_4814_);
return v_r_4815_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4816_, lean_object* v_x_4817_, lean_object* v___y_4818_){
_start:
{
if (lean_obj_tag(v_x_4816_) == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = l_List_reverse___redArg(v_x_4817_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
else
{
lean_object* v_head_4822_; lean_object* v_tail_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4841_; 
v_head_4822_ = lean_ctor_get(v_x_4816_, 0);
v_tail_4823_ = lean_ctor_get(v_x_4816_, 1);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_x_4816_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4825_ = v_x_4816_;
v_isShared_4826_ = v_isSharedCheck_4841_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_tail_4823_);
lean_inc(v_head_4822_);
lean_dec(v_x_4816_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4841_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4822_, v___y_4818_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 1, v_x_4817_);
lean_ctor_set(v___x_4825_, 0, v_a_4828_);
v___x_4830_ = v___x_4825_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4828_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_x_4817_);
v___x_4830_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
v_x_4816_ = v_tail_4823_;
v_x_4817_ = v___x_4830_;
goto _start;
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_del_object(v___x_4825_);
lean_dec(v_tail_4823_);
lean_dec(v_x_4817_);
v_a_4833_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4827_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4827_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4842_, lean_object* v_x_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4842_, v_x_4843_, v___y_4844_);
lean_dec_ref(v___y_4844_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4847_, lean_object* v_alts_4848_, uint8_t v_compress_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v_seq_4854_; 
if (v_compress_4849_ == 0)
{
goto v___jp_4857_;
}
else
{
uint8_t v___x_4867_; 
v___x_4867_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4848_);
if (v___x_4867_ == 0)
{
goto v___jp_4857_;
}
else
{
lean_object* v___x_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4868_ = lean_unsigned_to_nat(0u);
v___x_4869_ = lean_array_get_size(v_alts_4848_);
v___x_4870_ = lean_nat_dec_lt(v___x_4868_, v___x_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_dec_ref(v_alts_4848_);
v___x_4871_ = lean_box(0);
v___x_4872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4872_, 0, v_cases_4847_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
return v___x_4873_;
}
else
{
lean_object* v___x_4874_; lean_object* v_firstAlt_4875_; uint8_t v___x_4876_; 
v___x_4874_ = lean_box(0);
v_firstAlt_4875_ = lean_array_get(v___x_4874_, v_alts_4848_, v___x_4868_);
lean_dec_ref(v_alts_4848_);
lean_inc(v_firstAlt_4875_);
v___x_4876_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4875_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4886_; 
v___x_4877_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4847_, v_firstAlt_4875_, v_a_4850_);
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4886_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4886_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4882_, 0, v_a_4878_);
lean_ctor_set(v___x_4882_, 1, v___x_4874_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4882_);
v___x_4884_ = v___x_4880_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
else
{
lean_object* v___x_4887_; 
lean_dec(v_cases_4847_);
v___x_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4887_, 0, v_firstAlt_4875_);
return v___x_4887_;
}
}
}
}
v___jp_4853_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4855_, 0, v_cases_4847_);
lean_ctor_set(v___x_4855_, 1, v_seq_4854_);
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
return v___x_4856_;
}
v___jp_4857_:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4858_ = lean_array_get_size(v_alts_4848_);
v___x_4859_ = lean_unsigned_to_nat(1u);
v___x_4860_ = lean_nat_dec_eq(v___x_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4861_ = lean_array_to_list(v_alts_4848_);
v___x_4862_ = lean_box(0);
v___x_4863_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4861_, v___x_4862_, v_a_4850_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v_seq_4854_ = v_a_4864_;
goto v___jp_4853_;
}
else
{
lean_dec(v_cases_4847_);
return v___x_4863_;
}
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_unsigned_to_nat(0u);
v___x_4866_ = lean_array_fget(v_alts_4848_, v___x_4865_);
lean_dec_ref(v_alts_4848_);
v_seq_4854_ = v___x_4866_;
goto v___jp_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4888_, lean_object* v_alts_4889_, lean_object* v_compress_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
uint8_t v_compress_boxed_4894_; lean_object* v_res_4895_; 
v_compress_boxed_4894_ = lean_unbox(v_compress_4890_);
v_res_4895_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4888_, v_alts_4889_, v_compress_boxed_4894_, v_a_4891_, v_a_4892_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4896_, lean_object* v_x_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4896_, v_x_4897_, v___y_4898_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4902_, lean_object* v_x_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4902_, v_x_4903_, v___y_4904_, v___y_4905_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v___x_4911_; lean_object* v_env_4912_; uint8_t v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4911_ = lean_st_ref_get(v___y_4909_);
v_env_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc_ref(v_env_4912_);
lean_dec(v___x_4911_);
v___x_4913_ = l_Lean_Meta_isMatcherAppCore(v_env_4912_, v_e_4908_);
v___x_4914_ = lean_box(v___x_4913_);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v_e_4916_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4920_, v___y_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec(v___y_4934_);
lean_dec_ref(v_e_4933_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
lean_inc(v___y_4951_);
lean_inc_ref(v___y_4950_);
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc(v___y_4947_);
v___x_4957_ = lean_apply_10(v_x_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4970_, lean_object* v_x_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v___f_4982_; lean_object* v___x_4983_; 
lean_inc(v___y_4976_);
lean_inc_ref(v___y_4975_);
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
lean_inc(v___y_4972_);
v___f_4982_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4982_, 0, v_x_4971_);
lean_closure_set(v___f_4982_, 1, v___y_4972_);
lean_closure_set(v___f_4982_, 2, v___y_4973_);
lean_closure_set(v___f_4982_, 3, v___y_4974_);
lean_closure_set(v___f_4982_, 4, v___y_4975_);
lean_closure_set(v___f_4982_, 5, v___y_4976_);
v___x_4983_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4970_, v___f_4982_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
if (lean_obj_tag(v___x_4983_) == 0)
{
return v___x_4983_;
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4983_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4983_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_4992_, lean_object* v_x_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_4992_, v_x_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5005_, lean_object* v_mvarId_5006_, lean_object* v_x_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5006_, v_x_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5019_, lean_object* v_mvarId_5020_, lean_object* v_x_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5019_, v_mvarId_5020_, v_x_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5033_, lean_object* v___y_5034_){
_start:
{
uint8_t v___x_5036_; 
v___x_5036_ = l_Lean_Expr_hasMVar(v_e_5033_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v_e_5033_);
return v___x_5037_;
}
else
{
lean_object* v___x_5038_; lean_object* v_mctx_5039_; lean_object* v___x_5040_; lean_object* v_fst_5041_; lean_object* v_snd_5042_; lean_object* v___x_5043_; lean_object* v_cache_5044_; lean_object* v_zetaDeltaFVarIds_5045_; lean_object* v_postponed_5046_; lean_object* v_diag_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5056_; 
v___x_5038_ = lean_st_ref_get(v___y_5034_);
v_mctx_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc_ref(v_mctx_5039_);
lean_dec(v___x_5038_);
v___x_5040_ = l_Lean_instantiateMVarsCore(v_mctx_5039_, v_e_5033_);
v_fst_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_fst_5041_);
v_snd_5042_ = lean_ctor_get(v___x_5040_, 1);
lean_inc(v_snd_5042_);
lean_dec_ref(v___x_5040_);
v___x_5043_ = lean_st_ref_take(v___y_5034_);
v_cache_5044_ = lean_ctor_get(v___x_5043_, 1);
v_zetaDeltaFVarIds_5045_ = lean_ctor_get(v___x_5043_, 2);
v_postponed_5046_ = lean_ctor_get(v___x_5043_, 3);
v_diag_5047_ = lean_ctor_get(v___x_5043_, 4);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5056_ == 0)
{
lean_object* v_unused_5057_; 
v_unused_5057_ = lean_ctor_get(v___x_5043_, 0);
lean_dec(v_unused_5057_);
v___x_5049_ = v___x_5043_;
v_isShared_5050_ = v_isSharedCheck_5056_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_diag_5047_);
lean_inc(v_postponed_5046_);
lean_inc(v_zetaDeltaFVarIds_5045_);
lean_inc(v_cache_5044_);
lean_dec(v___x_5043_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5056_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 0, v_snd_5042_);
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_snd_5042_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_cache_5044_);
lean_ctor_set(v_reuseFailAlloc_5055_, 2, v_zetaDeltaFVarIds_5045_);
lean_ctor_set(v_reuseFailAlloc_5055_, 3, v_postponed_5046_);
lean_ctor_set(v_reuseFailAlloc_5055_, 4, v_diag_5047_);
v___x_5052_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_st_ref_put(v___y_5034_, v___x_5052_);
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v_fst_5041_);
return v___x_5054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5058_, v___y_5059_);
lean_dec(v___y_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v___x_5073_; 
v___x_5073_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5062_, v___y_5069_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
return v_res_5085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5088_ = l_Lean_stringToMessageData(v___x_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5089_, lean_object* v_c_5090_, lean_object* v_a_5091_, lean_object* v_numCases_5092_, uint8_t v_isRec_5093_, lean_object* v_anchorInfo_x3f_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v_mvarIds_5107_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5089_, v___y_5095_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___y_5170_; lean_object* v___x_5221_; uint8_t v___x_5224_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
v___x_5221_ = lean_unsigned_to_nat(1u);
v___x_5224_ = lean_nat_dec_lt(v___x_5221_, v_numCases_5092_);
if (v___x_5224_ == 0)
{
if (v_isRec_5093_ == 0)
{
lean_inc(v_a_5168_);
v___y_5170_ = v_a_5168_;
goto v___jp_5169_;
}
else
{
goto v___jp_5222_;
}
}
else
{
goto v___jp_5222_;
}
v___jp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5171_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5090_);
lean_inc_ref(v___x_5089_);
v___x_5172_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5089_, v___y_5170_, v_numCases_5092_, v___x_5171_, v___y_5098_, v___y_5101_, v___y_5103_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v___x_5173_; 
lean_dec_ref_known(v___x_5172_, 1);
lean_inc_ref(v___x_5089_);
v___x_5173_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5089_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_options_5174_; uint8_t v_hasTrace_5175_; 
lean_dec_ref_known(v___x_5173_, 1);
v_options_5174_ = lean_ctor_get(v___y_5103_, 2);
v_hasTrace_5175_ = lean_ctor_get_uint8(v_options_5174_, sizeof(void*)*1);
if (v_hasTrace_5175_ == 0)
{
lean_dec(v_a_5168_);
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
v___y_5115_ = v___y_5099_;
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
goto v___jp_5110_;
}
else
{
lean_object* v_inheritedTraceOptions_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; uint8_t v___x_5179_; 
v_inheritedTraceOptions_5176_ = lean_ctor_get(v___y_5103_, 13);
v___x_5177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5178_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5176_, v_options_5174_, v___x_5178_);
if (v___x_5179_ == 0)
{
lean_dec(v_a_5168_);
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
v___y_5115_ = v___y_5099_;
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
goto v___jp_5110_;
}
else
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Meta_Grind_updateLastTag(v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
lean_dec_ref_known(v___x_5180_, 1);
lean_inc_ref(v___x_5089_);
v___x_5181_ = l_Lean_MessageData_ofExpr(v___x_5089_);
v___x_5182_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5181_);
lean_ctor_set(v___x_5183_, 1, v___x_5182_);
v___x_5184_ = l_Nat_reprFast(v_a_5168_);
v___x_5185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
v___x_5186_ = l_Lean_MessageData_ofFormat(v___x_5185_);
v___x_5187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5183_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5177_, v___x_5187_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_dec_ref_known(v___x_5188_, 1);
v___y_5111_ = v___y_5095_;
v___y_5112_ = v___y_5096_;
v___y_5113_ = v___y_5097_;
v___y_5114_ = v___y_5098_;
v___y_5115_ = v___y_5099_;
v___y_5116_ = v___y_5100_;
v___y_5117_ = v___y_5101_;
v___y_5118_ = v___y_5102_;
v___y_5119_ = v___y_5103_;
v___y_5120_ = v___y_5104_;
goto v___jp_5110_;
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_a_5091_);
lean_dec_ref(v_c_5090_);
lean_dec_ref(v___x_5089_);
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_5188_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5188_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec(v_a_5168_);
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_a_5091_);
lean_dec_ref(v_c_5090_);
lean_dec_ref(v___x_5089_);
v_a_5197_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5180_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5180_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_dec(v_a_5168_);
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_a_5091_);
lean_dec_ref(v_c_5090_);
lean_dec_ref(v___x_5089_);
v_a_5205_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5173_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5173_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_dec(v_a_5168_);
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_a_5091_);
lean_dec_ref(v_c_5090_);
lean_dec_ref(v___x_5089_);
v_a_5213_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5172_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5172_);
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
v___jp_5222_:
{
lean_object* v___x_5223_; 
v___x_5223_ = lean_nat_add(v_a_5168_, v___x_5221_);
v___y_5170_ = v___x_5223_;
goto v___jp_5169_;
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_numCases_5092_);
lean_dec(v_a_5091_);
lean_dec_ref(v_c_5090_);
lean_dec_ref(v___x_5089_);
v_a_5225_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5167_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5167_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
v___jp_5106_:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5108_, 0, v_mvarIds_5107_);
lean_ctor_set(v___x_5108_, 1, v_anchorInfo_x3f_5094_);
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
v___jp_5110_:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5089_, v___y_5120_);
if (lean_obj_tag(v_c_5090_) == 1)
{
lean_object* v_e_5122_; lean_object* v_binderType_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec_ref(v___x_5121_);
lean_dec_ref(v___x_5089_);
v_e_5122_ = lean_ctor_get(v_c_5090_, 0);
lean_inc_ref(v_e_5122_);
lean_dec_ref_known(v_c_5090_, 2);
v_binderType_5123_ = lean_ctor_get(v_e_5122_, 1);
lean_inc_ref(v_binderType_5123_);
lean_dec_ref(v_e_5122_);
v___x_5124_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5123_);
v___x_5125_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5091_, v___x_5124_, v___y_5113_, v___y_5114_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
v_mvarIds_5107_ = v_a_5126_;
goto v___jp_5106_;
}
else
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5134_; 
lean_dec(v_anchorInfo_x3f_5094_);
v_a_5127_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5129_ = v___x_5125_;
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5125_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5134_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
else
{
lean_object* v_a_5135_; uint8_t v___x_5136_; 
lean_dec_ref(v_c_5090_);
v_a_5135_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5135_);
lean_dec_ref(v___x_5121_);
v___x_5136_ = lean_unbox(v_a_5135_);
lean_dec(v_a_5135_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; 
v___x_5137_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5089_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v___x_5139_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
lean_dec_ref_known(v___x_5137_, 1);
v___x_5139_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5091_, v_a_5138_, v___y_5113_, v___y_5114_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5139_, 1);
v_mvarIds_5107_ = v_a_5140_;
goto v___jp_5106_;
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
lean_dec(v_anchorInfo_x3f_5094_);
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
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec(v_anchorInfo_x3f_5094_);
lean_dec(v_a_5091_);
v_a_5149_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5137_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5137_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v___x_5157_; 
v___x_5157_ = l_Lean_Meta_Grind_casesMatch(v_a_5091_, v___x_5089_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
lean_dec_ref_known(v___x_5157_, 1);
v_mvarIds_5107_ = v_a_5158_;
goto v___jp_5106_;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec(v_anchorInfo_x3f_5094_);
v_a_5159_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5157_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5157_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5233_ = _args[0];
lean_object* v_c_5234_ = _args[1];
lean_object* v_a_5235_ = _args[2];
lean_object* v_numCases_5236_ = _args[3];
lean_object* v_isRec_5237_ = _args[4];
lean_object* v_anchorInfo_x3f_5238_ = _args[5];
lean_object* v___y_5239_ = _args[6];
lean_object* v___y_5240_ = _args[7];
lean_object* v___y_5241_ = _args[8];
lean_object* v___y_5242_ = _args[9];
lean_object* v___y_5243_ = _args[10];
lean_object* v___y_5244_ = _args[11];
lean_object* v___y_5245_ = _args[12];
lean_object* v___y_5246_ = _args[13];
lean_object* v___y_5247_ = _args[14];
lean_object* v___y_5248_ = _args[15];
lean_object* v___y_5249_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5250_; lean_object* v_res_5251_; 
v_isRec_boxed_5250_ = lean_unbox(v_isRec_5237_);
v_res_5251_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5233_, v_c_5234_, v_a_5235_, v_numCases_5236_, v_isRec_boxed_5250_, v_anchorInfo_x3f_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec(v___y_5239_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5252_, uint8_t v_trace_5253_, lean_object* v___f_5254_, lean_object* v_c_5255_, lean_object* v_candidates_x3f_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v___x_5267_; lean_object* v___y_5269_; 
v___x_5267_ = lean_st_mk_ref(v_goal_5252_);
if (v_trace_5253_ == 0)
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec(v_candidates_x3f_5256_);
v___x_5288_ = lean_box(0);
lean_inc(v___x_5267_);
v___x_5289_ = lean_apply_12(v___f_5254_, v___x_5288_, v___x_5267_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, lean_box(0));
v___y_5269_ = v___x_5289_;
goto v___jp_5268_;
}
else
{
lean_object* v___x_5290_; 
v___x_5290_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5255_, v_candidates_x3f_5256_, v___x_5267_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
lean_inc(v_a_5291_);
lean_dec_ref_known(v___x_5290_, 1);
v___x_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5292_, 0, v_a_5291_);
lean_inc(v___x_5267_);
v___x_5293_ = lean_apply_12(v___f_5254_, v___x_5292_, v___x_5267_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, lean_box(0));
v___y_5269_ = v___x_5293_;
goto v___jp_5268_;
}
else
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
lean_dec(v___x_5267_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___f_5254_);
v_a_5294_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5290_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5290_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
v___jp_5268_:
{
if (lean_obj_tag(v___y_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5279_; 
v_a_5270_ = lean_ctor_get(v___y_5269_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___y_5269_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5272_ = v___y_5269_;
v_isShared_5273_ = v_isSharedCheck_5279_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___y_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5279_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5277_; 
v___x_5274_ = lean_st_ref_get(v___x_5267_);
lean_dec(v___x_5267_);
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v_a_5270_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 0, v___x_5275_);
v___x_5277_ = v___x_5272_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5275_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec(v___x_5267_);
v_a_5280_ = lean_ctor_get(v___y_5269_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___y_5269_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___y_5269_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___y_5269_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5302_, lean_object* v_trace_5303_, lean_object* v___f_5304_, lean_object* v_c_5305_, lean_object* v_candidates_x3f_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
uint8_t v_trace_boxed_5317_; lean_object* v_res_5318_; 
v_trace_boxed_5317_ = lean_unbox(v_trace_5303_);
v_res_5318_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5302_, v_trace_boxed_5317_, v___f_5304_, v_c_5305_, v_candidates_x3f_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
lean_dec_ref(v_c_5305_);
return v_res_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5319_, lean_object* v_x_5320_, lean_object* v_x_5321_, lean_object* v_x_5322_){
_start:
{
lean_object* v_ks_5323_; lean_object* v_vs_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5348_; 
v_ks_5323_ = lean_ctor_get(v_x_5319_, 0);
v_vs_5324_ = lean_ctor_get(v_x_5319_, 1);
v_isSharedCheck_5348_ = !lean_is_exclusive(v_x_5319_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5326_ = v_x_5319_;
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_vs_5324_);
lean_inc(v_ks_5323_);
lean_dec(v_x_5319_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5328_; uint8_t v___x_5329_; 
v___x_5328_ = lean_array_get_size(v_ks_5323_);
v___x_5329_ = lean_nat_dec_lt(v_x_5320_, v___x_5328_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; 
lean_dec(v_x_5320_);
v___x_5330_ = lean_array_push(v_ks_5323_, v_x_5321_);
v___x_5331_ = lean_array_push(v_vs_5324_, v_x_5322_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 1, v___x_5331_);
lean_ctor_set(v___x_5326_, 0, v___x_5330_);
v___x_5333_ = v___x_5326_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
else
{
lean_object* v_k_x27_5335_; uint8_t v___x_5336_; 
v_k_x27_5335_ = lean_array_fget_borrowed(v_ks_5323_, v_x_5320_);
v___x_5336_ = l_Lean_instBEqMVarId_beq(v_x_5321_, v_k_x27_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5338_; 
if (v_isShared_5327_ == 0)
{
v___x_5338_ = v___x_5326_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_ks_5323_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_vs_5324_);
v___x_5338_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5339_ = lean_unsigned_to_nat(1u);
v___x_5340_ = lean_nat_add(v_x_5320_, v___x_5339_);
lean_dec(v_x_5320_);
v_x_5319_ = v___x_5338_;
v_x_5320_ = v___x_5340_;
goto _start;
}
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5346_; 
v___x_5343_ = lean_array_fset(v_ks_5323_, v_x_5320_, v_x_5321_);
v___x_5344_ = lean_array_fset(v_vs_5324_, v_x_5320_, v_x_5322_);
lean_dec(v_x_5320_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 1, v___x_5344_);
lean_ctor_set(v___x_5326_, 0, v___x_5343_);
v___x_5346_ = v___x_5326_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5347_, 1, v___x_5344_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5349_, lean_object* v_k_5350_, lean_object* v_v_5351_){
_start:
{
lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5352_ = lean_unsigned_to_nat(0u);
v___x_5353_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5349_, v___x_5352_, v_k_5350_, v_v_5351_);
return v___x_5353_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5354_; 
v___x_5354_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5355_, size_t v_x_5356_, size_t v_x_5357_, lean_object* v_x_5358_, lean_object* v_x_5359_){
_start:
{
if (lean_obj_tag(v_x_5355_) == 0)
{
lean_object* v_es_5360_; size_t v___x_5361_; size_t v___x_5362_; lean_object* v_j_5363_; lean_object* v___x_5364_; uint8_t v___x_5365_; 
v_es_5360_ = lean_ctor_get(v_x_5355_, 0);
v___x_5361_ = ((size_t)31ULL);
v___x_5362_ = lean_usize_land(v_x_5356_, v___x_5361_);
v_j_5363_ = lean_usize_to_nat(v___x_5362_);
v___x_5364_ = lean_array_get_size(v_es_5360_);
v___x_5365_ = lean_nat_dec_lt(v_j_5363_, v___x_5364_);
if (v___x_5365_ == 0)
{
lean_dec(v_j_5363_);
lean_dec(v_x_5359_);
lean_dec(v_x_5358_);
return v_x_5355_;
}
else
{
lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5404_; 
lean_inc_ref(v_es_5360_);
v_isSharedCheck_5404_ = !lean_is_exclusive(v_x_5355_);
if (v_isSharedCheck_5404_ == 0)
{
lean_object* v_unused_5405_; 
v_unused_5405_ = lean_ctor_get(v_x_5355_, 0);
lean_dec(v_unused_5405_);
v___x_5367_ = v_x_5355_;
v_isShared_5368_ = v_isSharedCheck_5404_;
goto v_resetjp_5366_;
}
else
{
lean_dec(v_x_5355_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5404_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v_v_5369_; lean_object* v___x_5370_; lean_object* v_xs_x27_5371_; lean_object* v___y_5373_; 
v_v_5369_ = lean_array_fget(v_es_5360_, v_j_5363_);
v___x_5370_ = lean_box(0);
v_xs_x27_5371_ = lean_array_fset(v_es_5360_, v_j_5363_, v___x_5370_);
switch(lean_obj_tag(v_v_5369_))
{
case 0:
{
lean_object* v_key_5378_; lean_object* v_val_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5389_; 
v_key_5378_ = lean_ctor_get(v_v_5369_, 0);
v_val_5379_ = lean_ctor_get(v_v_5369_, 1);
v_isSharedCheck_5389_ = !lean_is_exclusive(v_v_5369_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5381_ = v_v_5369_;
v_isShared_5382_ = v_isSharedCheck_5389_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_val_5379_);
lean_inc(v_key_5378_);
lean_dec(v_v_5369_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5389_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
uint8_t v___x_5383_; 
v___x_5383_ = l_Lean_instBEqMVarId_beq(v_x_5358_, v_key_5378_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
lean_del_object(v___x_5381_);
v___x_5384_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5378_, v_val_5379_, v_x_5358_, v_x_5359_);
v___x_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5384_);
v___y_5373_ = v___x_5385_;
goto v___jp_5372_;
}
else
{
lean_object* v___x_5387_; 
lean_dec(v_val_5379_);
lean_dec(v_key_5378_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 1, v_x_5359_);
lean_ctor_set(v___x_5381_, 0, v_x_5358_);
v___x_5387_ = v___x_5381_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_x_5358_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_x_5359_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
v___y_5373_ = v___x_5387_;
goto v___jp_5372_;
}
}
}
}
case 1:
{
lean_object* v_node_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5402_; 
v_node_5390_ = lean_ctor_get(v_v_5369_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_v_5369_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5392_ = v_v_5369_;
v_isShared_5393_ = v_isSharedCheck_5402_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_node_5390_);
lean_dec(v_v_5369_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5402_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
size_t v___x_5394_; size_t v___x_5395_; size_t v___x_5396_; size_t v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5400_; 
v___x_5394_ = ((size_t)5ULL);
v___x_5395_ = lean_usize_shift_right(v_x_5356_, v___x_5394_);
v___x_5396_ = ((size_t)1ULL);
v___x_5397_ = lean_usize_add(v_x_5357_, v___x_5396_);
v___x_5398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5390_, v___x_5395_, v___x_5397_, v_x_5358_, v_x_5359_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5398_);
v___x_5400_ = v___x_5392_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
v___y_5373_ = v___x_5400_;
goto v___jp_5372_;
}
}
}
default: 
{
lean_object* v___x_5403_; 
v___x_5403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5403_, 0, v_x_5358_);
lean_ctor_set(v___x_5403_, 1, v_x_5359_);
v___y_5373_ = v___x_5403_;
goto v___jp_5372_;
}
}
v___jp_5372_:
{
lean_object* v___x_5374_; lean_object* v___x_5376_; 
v___x_5374_ = lean_array_fset(v_xs_x27_5371_, v_j_5363_, v___y_5373_);
lean_dec(v_j_5363_);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v___x_5374_);
v___x_5376_ = v___x_5367_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v___x_5374_);
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
}
else
{
lean_object* v_ks_5406_; lean_object* v_vs_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5425_; 
v_ks_5406_ = lean_ctor_get(v_x_5355_, 0);
v_vs_5407_ = lean_ctor_get(v_x_5355_, 1);
v_isSharedCheck_5425_ = !lean_is_exclusive(v_x_5355_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5409_ = v_x_5355_;
v_isShared_5410_ = v_isSharedCheck_5425_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_vs_5407_);
lean_inc(v_ks_5406_);
lean_dec(v_x_5355_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5425_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_ks_5406_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_vs_5407_);
v___x_5412_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v_newNode_5413_; size_t v___x_5414_; uint8_t v___x_5415_; 
v_newNode_5413_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5412_, v_x_5358_, v_x_5359_);
v___x_5414_ = ((size_t)7ULL);
v___x_5415_ = lean_usize_dec_le(v___x_5414_, v_x_5357_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5416_; lean_object* v___x_5417_; uint8_t v___x_5418_; 
v___x_5416_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5413_);
v___x_5417_ = lean_unsigned_to_nat(4u);
v___x_5418_ = lean_nat_dec_lt(v___x_5416_, v___x_5417_);
lean_dec(v___x_5416_);
if (v___x_5418_ == 0)
{
lean_object* v_ks_5419_; lean_object* v_vs_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
v_ks_5419_ = lean_ctor_get(v_newNode_5413_, 0);
lean_inc_ref(v_ks_5419_);
v_vs_5420_ = lean_ctor_get(v_newNode_5413_, 1);
lean_inc_ref(v_vs_5420_);
lean_dec_ref(v_newNode_5413_);
v___x_5421_ = lean_unsigned_to_nat(0u);
v___x_5422_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5357_, v_ks_5419_, v_vs_5420_, v___x_5421_, v___x_5422_);
lean_dec_ref(v_vs_5420_);
lean_dec_ref(v_ks_5419_);
return v___x_5423_;
}
else
{
return v_newNode_5413_;
}
}
else
{
return v_newNode_5413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5426_, lean_object* v_keys_5427_, lean_object* v_vals_5428_, lean_object* v_i_5429_, lean_object* v_entries_5430_){
_start:
{
lean_object* v___x_5431_; uint8_t v___x_5432_; 
v___x_5431_ = lean_array_get_size(v_keys_5427_);
v___x_5432_ = lean_nat_dec_lt(v_i_5429_, v___x_5431_);
if (v___x_5432_ == 0)
{
lean_dec(v_i_5429_);
return v_entries_5430_;
}
else
{
lean_object* v_k_5433_; lean_object* v_v_5434_; uint64_t v___x_5435_; size_t v_h_5436_; size_t v___x_5437_; lean_object* v___x_5438_; size_t v___x_5439_; size_t v___x_5440_; size_t v___x_5441_; size_t v_h_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v_k_5433_ = lean_array_fget_borrowed(v_keys_5427_, v_i_5429_);
v_v_5434_ = lean_array_fget_borrowed(v_vals_5428_, v_i_5429_);
v___x_5435_ = l_Lean_instHashableMVarId_hash(v_k_5433_);
v_h_5436_ = lean_uint64_to_usize(v___x_5435_);
v___x_5437_ = ((size_t)5ULL);
v___x_5438_ = lean_unsigned_to_nat(1u);
v___x_5439_ = ((size_t)1ULL);
v___x_5440_ = lean_usize_sub(v_depth_5426_, v___x_5439_);
v___x_5441_ = lean_usize_mul(v___x_5437_, v___x_5440_);
v_h_5442_ = lean_usize_shift_right(v_h_5436_, v___x_5441_);
v___x_5443_ = lean_nat_add(v_i_5429_, v___x_5438_);
lean_dec(v_i_5429_);
lean_inc(v_v_5434_);
lean_inc(v_k_5433_);
v___x_5444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5430_, v_h_5442_, v_depth_5426_, v_k_5433_, v_v_5434_);
v_i_5429_ = v___x_5443_;
v_entries_5430_ = v___x_5444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5446_, lean_object* v_keys_5447_, lean_object* v_vals_5448_, lean_object* v_i_5449_, lean_object* v_entries_5450_){
_start:
{
size_t v_depth_boxed_5451_; lean_object* v_res_5452_; 
v_depth_boxed_5451_ = lean_unbox_usize(v_depth_5446_);
lean_dec(v_depth_5446_);
v_res_5452_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5451_, v_keys_5447_, v_vals_5448_, v_i_5449_, v_entries_5450_);
lean_dec_ref(v_vals_5448_);
lean_dec_ref(v_keys_5447_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5453_, lean_object* v_x_5454_, lean_object* v_x_5455_, lean_object* v_x_5456_, lean_object* v_x_5457_){
_start:
{
size_t v_x_66690__boxed_5458_; size_t v_x_66691__boxed_5459_; lean_object* v_res_5460_; 
v_x_66690__boxed_5458_ = lean_unbox_usize(v_x_5454_);
lean_dec(v_x_5454_);
v_x_66691__boxed_5459_ = lean_unbox_usize(v_x_5455_);
lean_dec(v_x_5455_);
v_res_5460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5453_, v_x_66690__boxed_5458_, v_x_66691__boxed_5459_, v_x_5456_, v_x_5457_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5461_, lean_object* v_x_5462_, lean_object* v_x_5463_){
_start:
{
uint64_t v___x_5464_; size_t v___x_5465_; size_t v___x_5466_; lean_object* v___x_5467_; 
v___x_5464_ = l_Lean_instHashableMVarId_hash(v_x_5462_);
v___x_5465_ = lean_uint64_to_usize(v___x_5464_);
v___x_5466_ = ((size_t)1ULL);
v___x_5467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5461_, v___x_5465_, v___x_5466_, v_x_5462_, v_x_5463_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5468_, lean_object* v_val_5469_, lean_object* v___y_5470_){
_start:
{
lean_object* v___x_5472_; lean_object* v_mctx_5473_; lean_object* v_cache_5474_; lean_object* v_zetaDeltaFVarIds_5475_; lean_object* v_postponed_5476_; lean_object* v_diag_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5506_; 
v___x_5472_ = lean_st_ref_take(v___y_5470_);
v_mctx_5473_ = lean_ctor_get(v___x_5472_, 0);
v_cache_5474_ = lean_ctor_get(v___x_5472_, 1);
v_zetaDeltaFVarIds_5475_ = lean_ctor_get(v___x_5472_, 2);
v_postponed_5476_ = lean_ctor_get(v___x_5472_, 3);
v_diag_5477_ = lean_ctor_get(v___x_5472_, 4);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5479_ = v___x_5472_;
v_isShared_5480_ = v_isSharedCheck_5506_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_diag_5477_);
lean_inc(v_postponed_5476_);
lean_inc(v_zetaDeltaFVarIds_5475_);
lean_inc(v_cache_5474_);
lean_inc(v_mctx_5473_);
lean_dec(v___x_5472_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5506_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v_depth_5481_; lean_object* v_levelAssignDepth_5482_; lean_object* v_lmvarCounter_5483_; lean_object* v_mvarCounter_5484_; lean_object* v_lDecls_5485_; lean_object* v_decls_5486_; lean_object* v_userNames_5487_; lean_object* v_lAssignment_5488_; lean_object* v_eAssignment_5489_; lean_object* v_dAssignment_5490_; lean_object* v_instanceTypedMVars_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5505_; 
v_depth_5481_ = lean_ctor_get(v_mctx_5473_, 0);
v_levelAssignDepth_5482_ = lean_ctor_get(v_mctx_5473_, 1);
v_lmvarCounter_5483_ = lean_ctor_get(v_mctx_5473_, 2);
v_mvarCounter_5484_ = lean_ctor_get(v_mctx_5473_, 3);
v_lDecls_5485_ = lean_ctor_get(v_mctx_5473_, 4);
v_decls_5486_ = lean_ctor_get(v_mctx_5473_, 5);
v_userNames_5487_ = lean_ctor_get(v_mctx_5473_, 6);
v_lAssignment_5488_ = lean_ctor_get(v_mctx_5473_, 7);
v_eAssignment_5489_ = lean_ctor_get(v_mctx_5473_, 8);
v_dAssignment_5490_ = lean_ctor_get(v_mctx_5473_, 9);
v_instanceTypedMVars_5491_ = lean_ctor_get(v_mctx_5473_, 10);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_mctx_5473_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5493_ = v_mctx_5473_;
v_isShared_5494_ = v_isSharedCheck_5505_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_instanceTypedMVars_5491_);
lean_inc(v_dAssignment_5490_);
lean_inc(v_eAssignment_5489_);
lean_inc(v_lAssignment_5488_);
lean_inc(v_userNames_5487_);
lean_inc(v_decls_5486_);
lean_inc(v_lDecls_5485_);
lean_inc(v_mvarCounter_5484_);
lean_inc(v_lmvarCounter_5483_);
lean_inc(v_levelAssignDepth_5482_);
lean_inc(v_depth_5481_);
lean_dec(v_mctx_5473_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5505_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5495_; lean_object* v___x_5497_; 
v___x_5495_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5489_, v_mvarId_5468_, v_val_5469_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 8, v___x_5495_);
v___x_5497_ = v___x_5493_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_depth_5481_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_levelAssignDepth_5482_);
lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_lmvarCounter_5483_);
lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_mvarCounter_5484_);
lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_lDecls_5485_);
lean_ctor_set(v_reuseFailAlloc_5504_, 5, v_decls_5486_);
lean_ctor_set(v_reuseFailAlloc_5504_, 6, v_userNames_5487_);
lean_ctor_set(v_reuseFailAlloc_5504_, 7, v_lAssignment_5488_);
lean_ctor_set(v_reuseFailAlloc_5504_, 8, v___x_5495_);
lean_ctor_set(v_reuseFailAlloc_5504_, 9, v_dAssignment_5490_);
lean_ctor_set(v_reuseFailAlloc_5504_, 10, v_instanceTypedMVars_5491_);
v___x_5497_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
lean_object* v___x_5499_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 0, v___x_5497_);
v___x_5499_ = v___x_5479_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_cache_5474_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_zetaDeltaFVarIds_5475_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_postponed_5476_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_diag_5477_);
v___x_5499_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5500_ = lean_st_ref_put(v___y_5470_, v___x_5499_);
v___x_5501_ = lean_box(0);
v___x_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5502_, 0, v___x_5501_);
return v___x_5502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5507_, lean_object* v_val_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5507_, v_val_5508_, v___y_5509_);
lean_dec(v___y_5509_);
return v_res_5511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5512_, lean_object* v_snd_5513_, uint8_t v_stopAtFirstFailure_5514_, lean_object* v_as_x27_5515_, lean_object* v_b_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_){
_start:
{
if (lean_obj_tag(v_as_x27_5515_) == 0)
{
lean_object* v___x_5527_; 
lean_dec_ref(v_snd_5513_);
lean_dec_ref(v_kp_5512_);
v___x_5527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5527_, 0, v_b_5516_);
return v___x_5527_;
}
else
{
lean_object* v_head_5528_; lean_object* v_tail_5529_; lean_object* v___x_5530_; 
v_head_5528_ = lean_ctor_get(v_as_x27_5515_, 0);
v_tail_5529_ = lean_ctor_get(v_as_x27_5515_, 1);
lean_inc_ref(v_kp_5512_);
lean_inc(v___y_5525_);
lean_inc_ref(v___y_5524_);
lean_inc(v___y_5523_);
lean_inc_ref(v___y_5522_);
lean_inc(v___y_5521_);
lean_inc_ref(v___y_5520_);
lean_inc(v___y_5519_);
lean_inc_ref(v___y_5518_);
lean_inc(v___y_5517_);
lean_inc(v_head_5528_);
v___x_5530_ = lean_apply_11(v_kp_5512_, v_head_5528_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, lean_box(0));
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_object* v_snd_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5626_; 
v_snd_5531_ = lean_ctor_get(v_b_5516_, 1);
v_isSharedCheck_5626_ = !lean_is_exclusive(v_b_5516_);
if (v_isSharedCheck_5626_ == 0)
{
lean_object* v_unused_5627_; 
v_unused_5627_ = lean_ctor_get(v_b_5516_, 0);
lean_dec(v_unused_5627_);
v___x_5533_ = v_b_5516_;
v_isShared_5534_ = v_isSharedCheck_5626_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_snd_5531_);
lean_dec(v_b_5516_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5626_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5625_; 
v_a_5535_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5537_ = v___x_5530_;
v_isShared_5538_ = v_isSharedCheck_5625_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5530_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5625_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v_fst_5539_; lean_object* v_snd_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5624_; 
v_fst_5539_ = lean_ctor_get(v_snd_5531_, 0);
v_snd_5540_ = lean_ctor_get(v_snd_5531_, 1);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_snd_5531_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5542_ = v_snd_5531_;
v_isShared_5543_ = v_isSharedCheck_5624_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_snd_5540_);
lean_inc(v_fst_5539_);
lean_dec(v_snd_5531_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5624_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5544_; 
v___x_5544_ = lean_box(0);
if (lean_obj_tag(v_a_5535_) == 0)
{
lean_object* v_seq_5545_; lean_object* v_mvarId_5546_; lean_object* v___x_5547_; 
lean_del_object(v___x_5537_);
v_seq_5545_ = lean_ctor_get(v_a_5535_, 0);
v_mvarId_5546_ = lean_ctor_get(v_head_5528_, 1);
lean_inc(v_mvarId_5546_);
v___x_5547_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5546_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_a_5548_);
lean_dec_ref_known(v___x_5547_, 1);
if (lean_obj_tag(v_a_5548_) == 1)
{
lean_object* v_val_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5580_; 
lean_dec_ref(v_kp_5512_);
v_val_5549_ = lean_ctor_get(v_a_5548_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v_a_5548_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5551_ = v_a_5548_;
v_isShared_5552_ = v_isSharedCheck_5580_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_val_5549_);
lean_dec(v_a_5548_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5580_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v_mvarId_5553_; lean_object* v___x_5554_; 
v_mvarId_5553_ = lean_ctor_get(v_snd_5513_, 1);
lean_inc(v_mvarId_5553_);
lean_dec_ref(v_snd_5513_);
v___x_5554_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5553_, v_val_5549_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5570_; 
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5570_ == 0)
{
lean_object* v_unused_5571_; 
v_unused_5571_ = lean_ctor_get(v___x_5554_, 0);
lean_dec(v_unused_5571_);
v___x_5556_ = v___x_5554_;
v_isShared_5557_ = v_isSharedCheck_5570_;
goto v_resetjp_5555_;
}
else
{
lean_dec(v___x_5554_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5570_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 0, v_a_5535_);
v___x_5559_ = v___x_5551_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5535_);
v___x_5559_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5561_; 
if (v_isShared_5543_ == 0)
{
v___x_5561_ = v___x_5542_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_fst_5539_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_snd_5540_);
v___x_5561_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v___x_5561_);
lean_ctor_set(v___x_5533_, 0, v___x_5559_);
v___x_5563_ = v___x_5533_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5565_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v___x_5563_);
v___x_5565_ = v___x_5556_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5563_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
}
}
else
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5579_; 
lean_del_object(v___x_5551_);
lean_dec_ref_known(v_a_5535_, 1);
lean_del_object(v___x_5542_);
lean_dec(v_snd_5540_);
lean_dec(v_fst_5539_);
lean_del_object(v___x_5533_);
v_a_5572_ = lean_ctor_get(v___x_5554_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5554_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5574_ = v___x_5554_;
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5554_);
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
}
else
{
uint8_t v___x_5581_; 
lean_inc(v_seq_5545_);
lean_dec(v_a_5548_);
lean_dec_ref_known(v_a_5535_, 1);
v___x_5581_ = l_List_isEmpty___redArg(v_seq_5545_);
if (v___x_5581_ == 0)
{
lean_object* v___x_5582_; lean_object* v___x_5584_; 
v___x_5582_ = lean_array_push(v_fst_5539_, v_seq_5545_);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 0, v___x_5582_);
v___x_5584_ = v___x_5542_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5589_, 1, v_snd_5540_);
v___x_5584_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5586_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v___x_5584_);
lean_ctor_set(v___x_5533_, 0, v___x_5544_);
v___x_5586_ = v___x_5533_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5584_);
v___x_5586_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
v_as_x27_5515_ = v_tail_5529_;
v_b_5516_ = v___x_5586_;
goto _start;
}
}
}
else
{
lean_object* v___x_5591_; 
lean_dec(v_seq_5545_);
if (v_isShared_5543_ == 0)
{
v___x_5591_ = v___x_5542_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_fst_5539_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_snd_5540_);
v___x_5591_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5593_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v___x_5591_);
lean_ctor_set(v___x_5533_, 0, v___x_5544_);
v___x_5593_ = v___x_5533_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
v_as_x27_5515_ = v_tail_5529_;
v_b_5516_ = v___x_5593_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
lean_dec_ref_known(v_a_5535_, 1);
lean_del_object(v___x_5542_);
lean_dec(v_snd_5540_);
lean_dec(v_fst_5539_);
lean_del_object(v___x_5533_);
lean_dec_ref(v_snd_5513_);
lean_dec_ref(v_kp_5512_);
v_a_5597_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5547_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5547_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5514_ == 0)
{
lean_object* v_gs_5605_; lean_object* v___x_5606_; lean_object* v___x_5608_; 
lean_del_object(v___x_5537_);
v_gs_5605_ = lean_ctor_get(v_a_5535_, 0);
lean_inc(v_gs_5605_);
lean_dec_ref_known(v_a_5535_, 1);
v___x_5606_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5540_, v_gs_5605_);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 1, v___x_5606_);
v___x_5608_ = v___x_5542_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_fst_5539_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v___x_5606_);
v___x_5608_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
lean_object* v___x_5610_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v___x_5608_);
lean_ctor_set(v___x_5533_, 0, v___x_5544_);
v___x_5610_ = v___x_5533_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5608_);
v___x_5610_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
v_as_x27_5515_ = v_tail_5529_;
v_b_5516_ = v___x_5610_;
goto _start;
}
}
}
else
{
lean_object* v___x_5614_; lean_object* v___x_5616_; 
lean_dec_ref(v_snd_5513_);
lean_dec_ref(v_kp_5512_);
v___x_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5614_, 0, v_a_5535_);
if (v_isShared_5543_ == 0)
{
v___x_5616_ = v___x_5542_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_fst_5539_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_snd_5540_);
v___x_5616_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
lean_object* v___x_5618_; 
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 1, v___x_5616_);
lean_ctor_set(v___x_5533_, 0, v___x_5614_);
v___x_5618_ = v___x_5533_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5614_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5620_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v___x_5618_);
v___x_5620_ = v___x_5537_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5618_);
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
}
else
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5635_; 
lean_dec_ref(v_b_5516_);
lean_dec_ref(v_snd_5513_);
lean_dec_ref(v_kp_5512_);
v_a_5628_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5630_ = v___x_5530_;
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5530_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5631_ == 0)
{
v___x_5633_ = v___x_5630_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
v___x_5633_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
return v___x_5633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5636_, lean_object* v_snd_5637_, lean_object* v_stopAtFirstFailure_5638_, lean_object* v_as_x27_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5651_; lean_object* v_res_5652_; 
v_stopAtFirstFailure_boxed_5651_ = lean_unbox(v_stopAtFirstFailure_5638_);
v_res_5652_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5636_, v_snd_5637_, v_stopAtFirstFailure_boxed_5651_, v_as_x27_5639_, v_b_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
lean_dec(v___y_5649_);
lean_dec_ref(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec(v_as_x27_5639_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5653_, lean_object* v_c_5654_, lean_object* v___x_5655_, lean_object* v___x_5656_, uint8_t v_isRec_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_){
_start:
{
if (lean_obj_tag(v_a_5658_) == 0)
{
lean_object* v___x_5660_; 
lean_dec(v___x_5656_);
lean_dec_ref(v___x_5655_);
lean_dec_ref(v_snd_5653_);
v___x_5660_ = lean_array_to_list(v_a_5659_);
return v___x_5660_;
}
else
{
lean_object* v_toGoalState_5661_; lean_object* v_split_5662_; lean_object* v_head_5663_; lean_object* v_tail_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5724_; 
v_toGoalState_5661_ = lean_ctor_get(v_snd_5653_, 0);
lean_inc_ref(v_toGoalState_5661_);
v_split_5662_ = lean_ctor_get(v_toGoalState_5661_, 14);
lean_inc_ref(v_split_5662_);
v_head_5663_ = lean_ctor_get(v_a_5658_, 0);
v_tail_5664_ = lean_ctor_get(v_a_5658_, 1);
v_isSharedCheck_5724_ = !lean_is_exclusive(v_a_5658_);
if (v_isSharedCheck_5724_ == 0)
{
v___x_5666_ = v_a_5658_;
v_isShared_5667_ = v_isSharedCheck_5724_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_tail_5664_);
lean_inc(v_head_5663_);
lean_dec(v_a_5658_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5724_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v_nextDeclIdx_5668_; lean_object* v_enodeMap_5669_; lean_object* v_exprs_5670_; lean_object* v_parents_5671_; lean_object* v_congrTable_5672_; lean_object* v_appMap_5673_; lean_object* v_indicesFound_5674_; lean_object* v_newFacts_5675_; uint8_t v_inconsistent_5676_; lean_object* v_nextIdx_5677_; lean_object* v_newRawFacts_5678_; lean_object* v_facts_5679_; lean_object* v_extThms_5680_; lean_object* v_ematch_5681_; lean_object* v_inj_5682_; lean_object* v_clean_5683_; lean_object* v_sstates_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5722_; 
v_nextDeclIdx_5668_ = lean_ctor_get(v_toGoalState_5661_, 0);
v_enodeMap_5669_ = lean_ctor_get(v_toGoalState_5661_, 1);
v_exprs_5670_ = lean_ctor_get(v_toGoalState_5661_, 2);
v_parents_5671_ = lean_ctor_get(v_toGoalState_5661_, 3);
v_congrTable_5672_ = lean_ctor_get(v_toGoalState_5661_, 4);
v_appMap_5673_ = lean_ctor_get(v_toGoalState_5661_, 5);
v_indicesFound_5674_ = lean_ctor_get(v_toGoalState_5661_, 6);
v_newFacts_5675_ = lean_ctor_get(v_toGoalState_5661_, 7);
v_inconsistent_5676_ = lean_ctor_get_uint8(v_toGoalState_5661_, sizeof(void*)*17);
v_nextIdx_5677_ = lean_ctor_get(v_toGoalState_5661_, 8);
v_newRawFacts_5678_ = lean_ctor_get(v_toGoalState_5661_, 9);
v_facts_5679_ = lean_ctor_get(v_toGoalState_5661_, 10);
v_extThms_5680_ = lean_ctor_get(v_toGoalState_5661_, 11);
v_ematch_5681_ = lean_ctor_get(v_toGoalState_5661_, 12);
v_inj_5682_ = lean_ctor_get(v_toGoalState_5661_, 13);
v_clean_5683_ = lean_ctor_get(v_toGoalState_5661_, 15);
v_sstates_5684_ = lean_ctor_get(v_toGoalState_5661_, 16);
v_isSharedCheck_5722_ = !lean_is_exclusive(v_toGoalState_5661_);
if (v_isSharedCheck_5722_ == 0)
{
lean_object* v_unused_5723_; 
v_unused_5723_ = lean_ctor_get(v_toGoalState_5661_, 14);
lean_dec(v_unused_5723_);
v___x_5686_ = v_toGoalState_5661_;
v_isShared_5687_ = v_isSharedCheck_5722_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_sstates_5684_);
lean_inc(v_clean_5683_);
lean_inc(v_inj_5682_);
lean_inc(v_ematch_5681_);
lean_inc(v_extThms_5680_);
lean_inc(v_facts_5679_);
lean_inc(v_newRawFacts_5678_);
lean_inc(v_nextIdx_5677_);
lean_inc(v_newFacts_5675_);
lean_inc(v_indicesFound_5674_);
lean_inc(v_appMap_5673_);
lean_inc(v_congrTable_5672_);
lean_inc(v_parents_5671_);
lean_inc(v_exprs_5670_);
lean_inc(v_enodeMap_5669_);
lean_inc(v_nextDeclIdx_5668_);
lean_dec(v_toGoalState_5661_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5722_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v_num_5688_; lean_object* v_candidates_5689_; lean_object* v_added_5690_; lean_object* v_resolved_5691_; lean_object* v_trace_5692_; lean_object* v_lookaheads_5693_; lean_object* v_argPosMap_5694_; lean_object* v_argsAt_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5721_; 
v_num_5688_ = lean_ctor_get(v_split_5662_, 0);
v_candidates_5689_ = lean_ctor_get(v_split_5662_, 1);
v_added_5690_ = lean_ctor_get(v_split_5662_, 2);
v_resolved_5691_ = lean_ctor_get(v_split_5662_, 3);
v_trace_5692_ = lean_ctor_get(v_split_5662_, 4);
v_lookaheads_5693_ = lean_ctor_get(v_split_5662_, 5);
v_argPosMap_5694_ = lean_ctor_get(v_split_5662_, 6);
v_argsAt_5695_ = lean_ctor_get(v_split_5662_, 7);
v_isSharedCheck_5721_ = !lean_is_exclusive(v_split_5662_);
if (v_isSharedCheck_5721_ == 0)
{
v___x_5697_ = v_split_5662_;
v_isShared_5698_ = v_isSharedCheck_5721_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_argsAt_5695_);
lean_inc(v_argPosMap_5694_);
lean_inc(v_lookaheads_5693_);
lean_inc(v_trace_5692_);
lean_inc(v_resolved_5691_);
lean_inc(v_added_5690_);
lean_inc(v_candidates_5689_);
lean_inc(v_num_5688_);
lean_dec(v_split_5662_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5721_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5699_; lean_object* v___y_5701_; lean_object* v___x_5719_; uint8_t v___x_5720_; 
v___x_5699_ = lean_array_get_size(v_a_5659_);
v___x_5719_ = lean_unsigned_to_nat(0u);
v___x_5720_ = lean_nat_dec_lt(v___x_5719_, v___x_5699_);
if (v___x_5720_ == 0)
{
if (v_isRec_5657_ == 0)
{
v___y_5701_ = v_num_5688_;
goto v___jp_5700_;
}
else
{
goto v___jp_5716_;
}
}
else
{
goto v___jp_5716_;
}
v___jp_5700_:
{
lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5705_; 
v___x_5702_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5654_);
lean_inc(v___x_5656_);
lean_inc_ref(v___x_5655_);
v___x_5703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5655_);
lean_ctor_set(v___x_5703_, 1, v___x_5699_);
lean_ctor_set(v___x_5703_, 2, v___x_5656_);
lean_ctor_set(v___x_5703_, 3, v___x_5702_);
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 1, v_trace_5692_);
lean_ctor_set(v___x_5666_, 0, v___x_5703_);
v___x_5705_ = v___x_5666_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5703_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v_trace_5692_);
v___x_5705_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
lean_object* v___x_5707_; 
if (v_isShared_5698_ == 0)
{
lean_ctor_set(v___x_5697_, 4, v___x_5705_);
lean_ctor_set(v___x_5697_, 0, v___y_5701_);
v___x_5707_ = v___x_5697_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___y_5701_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v_candidates_5689_);
lean_ctor_set(v_reuseFailAlloc_5714_, 2, v_added_5690_);
lean_ctor_set(v_reuseFailAlloc_5714_, 3, v_resolved_5691_);
lean_ctor_set(v_reuseFailAlloc_5714_, 4, v___x_5705_);
lean_ctor_set(v_reuseFailAlloc_5714_, 5, v_lookaheads_5693_);
lean_ctor_set(v_reuseFailAlloc_5714_, 6, v_argPosMap_5694_);
lean_ctor_set(v_reuseFailAlloc_5714_, 7, v_argsAt_5695_);
v___x_5707_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5709_; 
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 14, v___x_5707_);
v___x_5709_ = v___x_5686_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_nextDeclIdx_5668_);
lean_ctor_set(v_reuseFailAlloc_5713_, 1, v_enodeMap_5669_);
lean_ctor_set(v_reuseFailAlloc_5713_, 2, v_exprs_5670_);
lean_ctor_set(v_reuseFailAlloc_5713_, 3, v_parents_5671_);
lean_ctor_set(v_reuseFailAlloc_5713_, 4, v_congrTable_5672_);
lean_ctor_set(v_reuseFailAlloc_5713_, 5, v_appMap_5673_);
lean_ctor_set(v_reuseFailAlloc_5713_, 6, v_indicesFound_5674_);
lean_ctor_set(v_reuseFailAlloc_5713_, 7, v_newFacts_5675_);
lean_ctor_set(v_reuseFailAlloc_5713_, 8, v_nextIdx_5677_);
lean_ctor_set(v_reuseFailAlloc_5713_, 9, v_newRawFacts_5678_);
lean_ctor_set(v_reuseFailAlloc_5713_, 10, v_facts_5679_);
lean_ctor_set(v_reuseFailAlloc_5713_, 11, v_extThms_5680_);
lean_ctor_set(v_reuseFailAlloc_5713_, 12, v_ematch_5681_);
lean_ctor_set(v_reuseFailAlloc_5713_, 13, v_inj_5682_);
lean_ctor_set(v_reuseFailAlloc_5713_, 14, v___x_5707_);
lean_ctor_set(v_reuseFailAlloc_5713_, 15, v_clean_5683_);
lean_ctor_set(v_reuseFailAlloc_5713_, 16, v_sstates_5684_);
lean_ctor_set_uint8(v_reuseFailAlloc_5713_, sizeof(void*)*17, v_inconsistent_5676_);
v___x_5709_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
lean_ctor_set(v___x_5710_, 1, v_head_5663_);
v___x_5711_ = lean_array_push(v_a_5659_, v___x_5710_);
v_a_5658_ = v_tail_5664_;
v_a_5659_ = v___x_5711_;
goto _start;
}
}
}
}
v___jp_5716_:
{
lean_object* v___x_5717_; lean_object* v___x_5718_; 
v___x_5717_ = lean_unsigned_to_nat(1u);
v___x_5718_ = lean_nat_add(v_num_5688_, v___x_5717_);
lean_dec(v_num_5688_);
v___y_5701_ = v___x_5718_;
goto v___jp_5700_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5725_, lean_object* v_c_5726_, lean_object* v___x_5727_, lean_object* v___x_5728_, lean_object* v_isRec_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_){
_start:
{
uint8_t v_isRec_boxed_5732_; lean_object* v_res_5733_; 
v_isRec_boxed_5732_ = lean_unbox(v_isRec_5729_);
v_res_5733_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5725_, v_c_5726_, v___x_5727_, v___x_5728_, v_isRec_boxed_5732_, v_a_5730_, v_a_5731_);
lean_dec_ref(v_c_5726_);
return v_res_5733_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5745_ = lean_box(0);
v___x_5746_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5747_ = l_Lean_mkConst(v___x_5746_, v___x_5745_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5748_, lean_object* v_numCases_5749_, uint8_t v_isRec_5750_, uint8_t v_stopAtFirstFailure_5751_, uint8_t v_compress_5752_, lean_object* v_candidates_x3f_5753_, lean_object* v_goal_5754_, lean_object* v_kp_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v___x_5766_; 
v___x_5766_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5757_);
if (lean_obj_tag(v___x_5766_) == 0)
{
lean_object* v_a_5767_; lean_object* v___x_5768_; 
v_a_5767_ = lean_ctor_get(v___x_5766_, 0);
lean_inc(v_a_5767_);
lean_dec_ref_known(v___x_5766_, 1);
lean_inc_ref(v_goal_5754_);
v___x_5768_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5754_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_object* v_a_5769_; uint8_t v_trace_5770_; lean_object* v_mvarId_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___f_5774_; lean_object* v___x_5775_; lean_object* v___f_5776_; lean_object* v___x_5777_; 
v_a_5769_ = lean_ctor_get(v___x_5768_, 0);
lean_inc_n(v_a_5769_, 2);
lean_dec_ref_known(v___x_5768_, 1);
v_trace_5770_ = lean_ctor_get_uint8(v_a_5767_, sizeof(void*)*14);
lean_dec(v_a_5767_);
v_mvarId_5771_ = lean_ctor_get(v_goal_5754_, 1);
lean_inc(v_mvarId_5771_);
v___x_5772_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5748_);
v___x_5773_ = lean_box(v_isRec_5750_);
lean_inc_ref_n(v_c_5748_, 2);
lean_inc_ref(v___x_5772_);
v___f_5774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5774_, 0, v___x_5772_);
lean_closure_set(v___f_5774_, 1, v_c_5748_);
lean_closure_set(v___f_5774_, 2, v_a_5769_);
lean_closure_set(v___f_5774_, 3, v_numCases_5749_);
lean_closure_set(v___f_5774_, 4, v___x_5773_);
v___x_5775_ = lean_box(v_trace_5770_);
v___f_5776_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5776_, 0, v_goal_5754_);
lean_closure_set(v___f_5776_, 1, v___x_5775_);
lean_closure_set(v___f_5776_, 2, v___f_5774_);
lean_closure_set(v___f_5776_, 3, v_c_5748_);
lean_closure_set(v___f_5776_, 4, v_candidates_x3f_5753_);
v___x_5777_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5771_, v___f_5776_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v_a_5778_; lean_object* v_fst_5779_; lean_object* v_snd_5780_; lean_object* v_fst_5781_; lean_object* v_snd_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; 
v_a_5778_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_a_5778_);
lean_dec_ref_known(v___x_5777_, 1);
v_fst_5779_ = lean_ctor_get(v_a_5778_, 0);
lean_inc(v_fst_5779_);
v_snd_5780_ = lean_ctor_get(v_a_5778_, 1);
lean_inc_n(v_snd_5780_, 3);
lean_dec(v_a_5778_);
v_fst_5781_ = lean_ctor_get(v_fst_5779_, 0);
lean_inc(v_fst_5781_);
v_snd_5782_ = lean_ctor_get(v_fst_5779_, 1);
lean_inc(v_snd_5782_);
lean_dec(v_fst_5779_);
v___x_5783_ = l_List_lengthTR___redArg(v_fst_5781_);
v___x_5784_ = lean_unsigned_to_nat(0u);
v___x_5785_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5786_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5780_, v_c_5748_, v___x_5772_, v___x_5783_, v_isRec_5750_, v_fst_5781_, v___x_5785_);
lean_dec_ref(v_c_5748_);
v___x_5787_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5788_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5755_, v_snd_5780_, v_stopAtFirstFailure_5751_, v___x_5786_, v___x_5787_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
lean_dec(v___x_5786_);
if (lean_obj_tag(v___x_5788_) == 0)
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5876_; 
v_a_5789_ = lean_ctor_get(v___x_5788_, 0);
v_isSharedCheck_5876_ = !lean_is_exclusive(v___x_5788_);
if (v_isSharedCheck_5876_ == 0)
{
v___x_5791_ = v___x_5788_;
v_isShared_5792_ = v_isSharedCheck_5876_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5788_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5876_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v_fst_5793_; 
v_fst_5793_ = lean_ctor_get(v_a_5789_, 0);
if (lean_obj_tag(v_fst_5793_) == 0)
{
lean_object* v_snd_5794_; lean_object* v_mvarId_5795_; lean_object* v___x_5796_; 
lean_del_object(v___x_5791_);
v_snd_5794_ = lean_ctor_get(v_a_5789_, 1);
lean_inc(v_snd_5794_);
lean_dec(v_a_5789_);
v_mvarId_5795_ = lean_ctor_get(v_snd_5780_, 1);
lean_inc_n(v_mvarId_5795_, 2);
lean_dec(v_snd_5780_);
v___x_5796_ = l_Lean_MVarId_getType(v_mvarId_5795_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
if (lean_obj_tag(v___x_5796_) == 0)
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5863_; 
v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5799_ = v___x_5796_;
v_isShared_5800_ = v_isSharedCheck_5863_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5796_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5863_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v_fst_5801_; lean_object* v_snd_5802_; lean_object* v___y_5804_; lean_object* v___y_5805_; uint8_t v___x_5852_; 
v_fst_5801_ = lean_ctor_get(v_snd_5794_, 0);
lean_inc(v_fst_5801_);
v_snd_5802_ = lean_ctor_get(v_snd_5794_, 1);
lean_inc(v_snd_5802_);
lean_dec(v_snd_5794_);
v___x_5852_ = l_Lean_Expr_isFalse(v_a_5797_);
if (v___x_5852_ == 0)
{
lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v_a_5855_; lean_object* v___x_5856_; 
v___x_5853_ = l_Lean_mkMVar(v_a_5769_);
v___x_5854_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5853_, v_a_5762_);
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5855_);
lean_dec_ref(v___x_5854_);
v___x_5856_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5795_, v_a_5855_, v_a_5762_);
lean_dec_ref(v___x_5856_);
v___y_5804_ = v_a_5763_;
v___y_5805_ = v_a_5764_;
goto v___jp_5803_;
}
else
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v_a_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5857_ = l_Lean_mkMVar(v_a_5769_);
v___x_5858_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5857_, v_a_5762_);
v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
lean_inc(v_a_5859_);
lean_dec_ref(v___x_5858_);
v___x_5860_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5861_ = l_Lean_Meta_mkExpectedPropHint(v_a_5859_, v___x_5860_);
v___x_5862_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5795_, v___x_5861_, v_a_5762_);
lean_dec_ref(v___x_5862_);
v___y_5804_ = v_a_5763_;
v___y_5805_ = v_a_5764_;
goto v___jp_5803_;
}
v___jp_5803_:
{
lean_object* v___x_5806_; uint8_t v___x_5807_; 
v___x_5806_ = lean_array_get_size(v_snd_5802_);
v___x_5807_ = lean_nat_dec_eq(v___x_5806_, v___x_5784_);
if (v___x_5807_ == 0)
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5811_; 
lean_dec(v_fst_5801_);
lean_dec(v_snd_5782_);
v___x_5808_ = lean_array_to_list(v_snd_5802_);
v___x_5809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5808_);
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 0, v___x_5809_);
v___x_5811_ = v___x_5799_;
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
else
{
lean_dec(v_snd_5802_);
if (lean_obj_tag(v_snd_5782_) == 1)
{
lean_object* v_val_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5847_; 
lean_del_object(v___x_5799_);
v_val_5813_ = lean_ctor_get(v_snd_5782_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v_snd_5782_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5815_ = v_snd_5782_;
v_isShared_5816_ = v_isSharedCheck_5847_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_val_5813_);
lean_dec(v_snd_5782_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5847_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5817_; 
v___x_5817_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5813_, v___y_5804_);
lean_dec(v_val_5813_);
if (lean_obj_tag(v___x_5817_) == 0)
{
lean_object* v_a_5818_; lean_object* v___x_5819_; 
v_a_5818_ = lean_ctor_get(v___x_5817_, 0);
lean_inc(v_a_5818_);
lean_dec_ref_known(v___x_5817_, 1);
v___x_5819_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5818_, v_fst_5801_, v_compress_5752_, v___y_5804_, v___y_5805_);
if (lean_obj_tag(v___x_5819_) == 0)
{
lean_object* v_a_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5830_; 
v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5819_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5822_ = v___x_5819_;
v_isShared_5823_ = v_isSharedCheck_5830_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_a_5820_);
lean_dec(v___x_5819_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5830_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5825_; 
if (v_isShared_5816_ == 0)
{
lean_ctor_set_tag(v___x_5815_, 0);
lean_ctor_set(v___x_5815_, 0, v_a_5820_);
v___x_5825_ = v___x_5815_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5820_);
v___x_5825_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
lean_object* v___x_5827_; 
if (v_isShared_5823_ == 0)
{
lean_ctor_set(v___x_5822_, 0, v___x_5825_);
v___x_5827_ = v___x_5822_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5825_);
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
else
{
lean_object* v_a_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5838_; 
lean_del_object(v___x_5815_);
v_a_5831_ = lean_ctor_get(v___x_5819_, 0);
v_isSharedCheck_5838_ = !lean_is_exclusive(v___x_5819_);
if (v_isSharedCheck_5838_ == 0)
{
v___x_5833_ = v___x_5819_;
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_a_5831_);
lean_dec(v___x_5819_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v___x_5836_; 
if (v_isShared_5834_ == 0)
{
v___x_5836_ = v___x_5833_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5831_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_del_object(v___x_5815_);
lean_dec(v_fst_5801_);
v_a_5839_ = lean_ctor_get(v___x_5817_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5817_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5817_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5817_);
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
}
else
{
lean_object* v___x_5848_; lean_object* v___x_5850_; 
lean_dec(v_fst_5801_);
lean_dec(v_snd_5782_);
v___x_5848_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 0, v___x_5848_);
v___x_5850_ = v___x_5799_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___x_5848_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
}
}
else
{
lean_object* v_a_5864_; lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5871_; 
lean_dec(v_mvarId_5795_);
lean_dec(v_snd_5794_);
lean_dec(v_snd_5782_);
lean_dec(v_a_5769_);
v_a_5864_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5866_ = v___x_5796_;
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
else
{
lean_inc(v_a_5864_);
lean_dec(v___x_5796_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v___x_5869_; 
if (v_isShared_5867_ == 0)
{
v___x_5869_ = v___x_5866_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
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
lean_object* v_val_5872_; lean_object* v___x_5874_; 
lean_inc_ref(v_fst_5793_);
lean_dec(v_a_5789_);
lean_dec(v_snd_5782_);
lean_dec(v_snd_5780_);
lean_dec(v_a_5769_);
v_val_5872_ = lean_ctor_get(v_fst_5793_, 0);
lean_inc(v_val_5872_);
lean_dec_ref_known(v_fst_5793_, 1);
if (v_isShared_5792_ == 0)
{
lean_ctor_set(v___x_5791_, 0, v_val_5872_);
v___x_5874_ = v___x_5791_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_val_5872_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
}
else
{
lean_object* v_a_5877_; lean_object* v___x_5879_; uint8_t v_isShared_5880_; uint8_t v_isSharedCheck_5884_; 
lean_dec(v_snd_5782_);
lean_dec(v_snd_5780_);
lean_dec(v_a_5769_);
v_a_5877_ = lean_ctor_get(v___x_5788_, 0);
v_isSharedCheck_5884_ = !lean_is_exclusive(v___x_5788_);
if (v_isSharedCheck_5884_ == 0)
{
v___x_5879_ = v___x_5788_;
v_isShared_5880_ = v_isSharedCheck_5884_;
goto v_resetjp_5878_;
}
else
{
lean_inc(v_a_5877_);
lean_dec(v___x_5788_);
v___x_5879_ = lean_box(0);
v_isShared_5880_ = v_isSharedCheck_5884_;
goto v_resetjp_5878_;
}
v_resetjp_5878_:
{
lean_object* v___x_5882_; 
if (v_isShared_5880_ == 0)
{
v___x_5882_ = v___x_5879_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_a_5877_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
}
else
{
lean_object* v_a_5885_; lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5892_; 
lean_dec_ref(v___x_5772_);
lean_dec(v_a_5769_);
lean_dec_ref(v_kp_5755_);
lean_dec_ref(v_c_5748_);
v_a_5885_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5887_ = v___x_5777_;
v_isShared_5888_ = v_isSharedCheck_5892_;
goto v_resetjp_5886_;
}
else
{
lean_inc(v_a_5885_);
lean_dec(v___x_5777_);
v___x_5887_ = lean_box(0);
v_isShared_5888_ = v_isSharedCheck_5892_;
goto v_resetjp_5886_;
}
v_resetjp_5886_:
{
lean_object* v___x_5890_; 
if (v_isShared_5888_ == 0)
{
v___x_5890_ = v___x_5887_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_a_5885_);
v___x_5890_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
return v___x_5890_;
}
}
}
}
else
{
lean_object* v_a_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5900_; 
lean_dec(v_a_5767_);
lean_dec_ref(v_kp_5755_);
lean_dec_ref(v_goal_5754_);
lean_dec(v_candidates_x3f_5753_);
lean_dec(v_numCases_5749_);
lean_dec_ref(v_c_5748_);
v_a_5893_ = lean_ctor_get(v___x_5768_, 0);
v_isSharedCheck_5900_ = !lean_is_exclusive(v___x_5768_);
if (v_isSharedCheck_5900_ == 0)
{
v___x_5895_ = v___x_5768_;
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_a_5893_);
lean_dec(v___x_5768_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5898_; 
if (v_isShared_5896_ == 0)
{
v___x_5898_ = v___x_5895_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_a_5893_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
}
else
{
lean_object* v_a_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5908_; 
lean_dec_ref(v_kp_5755_);
lean_dec_ref(v_goal_5754_);
lean_dec(v_candidates_x3f_5753_);
lean_dec(v_numCases_5749_);
lean_dec_ref(v_c_5748_);
v_a_5901_ = lean_ctor_get(v___x_5766_, 0);
v_isSharedCheck_5908_ = !lean_is_exclusive(v___x_5766_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5903_ = v___x_5766_;
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_a_5901_);
lean_dec(v___x_5766_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5906_; 
if (v_isShared_5904_ == 0)
{
v___x_5906_ = v___x_5903_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v_a_5901_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
return v___x_5906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5909_ = _args[0];
lean_object* v_numCases_5910_ = _args[1];
lean_object* v_isRec_5911_ = _args[2];
lean_object* v_stopAtFirstFailure_5912_ = _args[3];
lean_object* v_compress_5913_ = _args[4];
lean_object* v_candidates_x3f_5914_ = _args[5];
lean_object* v_goal_5915_ = _args[6];
lean_object* v_kp_5916_ = _args[7];
lean_object* v_a_5917_ = _args[8];
lean_object* v_a_5918_ = _args[9];
lean_object* v_a_5919_ = _args[10];
lean_object* v_a_5920_ = _args[11];
lean_object* v_a_5921_ = _args[12];
lean_object* v_a_5922_ = _args[13];
lean_object* v_a_5923_ = _args[14];
lean_object* v_a_5924_ = _args[15];
lean_object* v_a_5925_ = _args[16];
lean_object* v_a_5926_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5927_; uint8_t v_stopAtFirstFailure_boxed_5928_; uint8_t v_compress_boxed_5929_; lean_object* v_res_5930_; 
v_isRec_boxed_5927_ = lean_unbox(v_isRec_5911_);
v_stopAtFirstFailure_boxed_5928_ = lean_unbox(v_stopAtFirstFailure_5912_);
v_compress_boxed_5929_ = lean_unbox(v_compress_5913_);
v_res_5930_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5909_, v_numCases_5910_, v_isRec_boxed_5927_, v_stopAtFirstFailure_boxed_5928_, v_compress_boxed_5929_, v_candidates_x3f_5914_, v_goal_5915_, v_kp_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
lean_dec(v_a_5925_);
lean_dec_ref(v_a_5924_);
lean_dec(v_a_5923_);
lean_dec_ref(v_a_5922_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5931_, lean_object* v_numCases_5932_, uint8_t v_isRec_5933_, uint8_t v_stopAtFirstFailure_5934_, uint8_t v_compress_5935_, lean_object* v_candidates_x3f_5936_, lean_object* v_goal_5937_, lean_object* v_x_5938_, lean_object* v_kp_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_){
_start:
{
lean_object* v___x_5950_; 
v___x_5950_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5931_, v_numCases_5932_, v_isRec_5933_, v_stopAtFirstFailure_5934_, v_compress_5935_, v_candidates_x3f_5936_, v_goal_5937_, v_kp_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
return v___x_5950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5951_ = _args[0];
lean_object* v_numCases_5952_ = _args[1];
lean_object* v_isRec_5953_ = _args[2];
lean_object* v_stopAtFirstFailure_5954_ = _args[3];
lean_object* v_compress_5955_ = _args[4];
lean_object* v_candidates_x3f_5956_ = _args[5];
lean_object* v_goal_5957_ = _args[6];
lean_object* v_x_5958_ = _args[7];
lean_object* v_kp_5959_ = _args[8];
lean_object* v_a_5960_ = _args[9];
lean_object* v_a_5961_ = _args[10];
lean_object* v_a_5962_ = _args[11];
lean_object* v_a_5963_ = _args[12];
lean_object* v_a_5964_ = _args[13];
lean_object* v_a_5965_ = _args[14];
lean_object* v_a_5966_ = _args[15];
lean_object* v_a_5967_ = _args[16];
lean_object* v_a_5968_ = _args[17];
lean_object* v_a_5969_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5970_; uint8_t v_stopAtFirstFailure_boxed_5971_; uint8_t v_compress_boxed_5972_; lean_object* v_res_5973_; 
v_isRec_boxed_5970_ = lean_unbox(v_isRec_5953_);
v_stopAtFirstFailure_boxed_5971_ = lean_unbox(v_stopAtFirstFailure_5954_);
v_compress_boxed_5972_ = lean_unbox(v_compress_5955_);
v_res_5973_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5951_, v_numCases_5952_, v_isRec_boxed_5970_, v_stopAtFirstFailure_boxed_5971_, v_compress_boxed_5972_, v_candidates_x3f_5956_, v_goal_5957_, v_x_5958_, v_kp_5959_, v_a_5960_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
lean_dec(v_a_5968_);
lean_dec_ref(v_a_5967_);
lean_dec(v_a_5966_);
lean_dec_ref(v_a_5965_);
lean_dec(v_a_5964_);
lean_dec_ref(v_a_5963_);
lean_dec(v_a_5962_);
lean_dec_ref(v_a_5961_);
lean_dec(v_a_5960_);
lean_dec_ref(v_x_5958_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5974_, lean_object* v_snd_5975_, uint8_t v_stopAtFirstFailure_5976_, lean_object* v_as_5977_, lean_object* v_as_x27_5978_, lean_object* v_b_5979_, lean_object* v_a_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_){
_start:
{
lean_object* v___x_5991_; 
v___x_5991_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5974_, v_snd_5975_, v_stopAtFirstFailure_5976_, v_as_x27_5978_, v_b_5979_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
return v___x_5991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5992_ = _args[0];
lean_object* v_snd_5993_ = _args[1];
lean_object* v_stopAtFirstFailure_5994_ = _args[2];
lean_object* v_as_5995_ = _args[3];
lean_object* v_as_x27_5996_ = _args[4];
lean_object* v_b_5997_ = _args[5];
lean_object* v_a_5998_ = _args[6];
lean_object* v___y_5999_ = _args[7];
lean_object* v___y_6000_ = _args[8];
lean_object* v___y_6001_ = _args[9];
lean_object* v___y_6002_ = _args[10];
lean_object* v___y_6003_ = _args[11];
lean_object* v___y_6004_ = _args[12];
lean_object* v___y_6005_ = _args[13];
lean_object* v___y_6006_ = _args[14];
lean_object* v___y_6007_ = _args[15];
lean_object* v___y_6008_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6009_; lean_object* v_res_6010_; 
v_stopAtFirstFailure_boxed_6009_ = lean_unbox(v_stopAtFirstFailure_5994_);
v_res_6010_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5992_, v_snd_5993_, v_stopAtFirstFailure_boxed_6009_, v_as_5995_, v_as_x27_5996_, v_b_5997_, v_a_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec(v___y_6003_);
lean_dec_ref(v___y_6002_);
lean_dec(v___y_6001_);
lean_dec_ref(v___y_6000_);
lean_dec(v___y_5999_);
lean_dec(v_as_x27_5996_);
lean_dec(v_as_5995_);
return v_res_6010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6011_, lean_object* v_val_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6011_, v_val_6012_, v___y_6019_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6024_, lean_object* v_val_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_){
_start:
{
lean_object* v_res_6036_; 
v_res_6036_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6024_, v_val_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec(v___y_6028_);
lean_dec_ref(v___y_6027_);
lean_dec(v___y_6026_);
return v_res_6036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6037_, lean_object* v_x_6038_, lean_object* v_x_6039_, lean_object* v_x_6040_){
_start:
{
lean_object* v___x_6041_; 
v___x_6041_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6038_, v_x_6039_, v_x_6040_);
return v___x_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6042_, lean_object* v_x_6043_, size_t v_x_6044_, size_t v_x_6045_, lean_object* v_x_6046_, lean_object* v_x_6047_){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6043_, v_x_6044_, v_x_6045_, v_x_6046_, v_x_6047_);
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6049_, lean_object* v_x_6050_, lean_object* v_x_6051_, lean_object* v_x_6052_, lean_object* v_x_6053_, lean_object* v_x_6054_){
_start:
{
size_t v_x_67645__boxed_6055_; size_t v_x_67646__boxed_6056_; lean_object* v_res_6057_; 
v_x_67645__boxed_6055_ = lean_unbox_usize(v_x_6051_);
lean_dec(v_x_6051_);
v_x_67646__boxed_6056_ = lean_unbox_usize(v_x_6052_);
lean_dec(v_x_6052_);
v_res_6057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6049_, v_x_6050_, v_x_67645__boxed_6055_, v_x_67646__boxed_6056_, v_x_6053_, v_x_6054_);
return v_res_6057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6058_, lean_object* v_n_6059_, lean_object* v_k_6060_, lean_object* v_v_6061_){
_start:
{
lean_object* v___x_6062_; 
v___x_6062_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6059_, v_k_6060_, v_v_6061_);
return v___x_6062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6063_, size_t v_depth_6064_, lean_object* v_keys_6065_, lean_object* v_vals_6066_, lean_object* v_heq_6067_, lean_object* v_i_6068_, lean_object* v_entries_6069_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6064_, v_keys_6065_, v_vals_6066_, v_i_6068_, v_entries_6069_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6071_, lean_object* v_depth_6072_, lean_object* v_keys_6073_, lean_object* v_vals_6074_, lean_object* v_heq_6075_, lean_object* v_i_6076_, lean_object* v_entries_6077_){
_start:
{
size_t v_depth_boxed_6078_; lean_object* v_res_6079_; 
v_depth_boxed_6078_ = lean_unbox_usize(v_depth_6072_);
lean_dec(v_depth_6072_);
v_res_6079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6071_, v_depth_boxed_6078_, v_keys_6073_, v_vals_6074_, v_heq_6075_, v_i_6076_, v_entries_6077_);
lean_dec_ref(v_vals_6074_);
lean_dec_ref(v_keys_6073_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6080_, lean_object* v_x_6081_, lean_object* v_x_6082_, lean_object* v_x_6083_, lean_object* v_x_6084_){
_start:
{
lean_object* v___x_6085_; 
v___x_6085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6081_, v_x_6082_, v_x_6083_, v_x_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v_goal_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; 
v___x_6097_ = lean_st_mk_ref(v_goal_6086_);
v___x_6098_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6097_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
if (lean_obj_tag(v___x_6098_) == 0)
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6108_; 
v_a_6099_ = lean_ctor_get(v___x_6098_, 0);
v_isSharedCheck_6108_ = !lean_is_exclusive(v___x_6098_);
if (v_isSharedCheck_6108_ == 0)
{
v___x_6101_ = v___x_6098_;
v_isShared_6102_ = v_isSharedCheck_6108_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_6098_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6108_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6106_; 
v___x_6103_ = lean_st_ref_get(v___x_6097_);
lean_dec(v___x_6097_);
v___x_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6104_, 0, v_a_6099_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
if (v_isShared_6102_ == 0)
{
lean_ctor_set(v___x_6101_, 0, v___x_6104_);
v___x_6106_ = v___x_6101_;
goto v_reusejp_6105_;
}
else
{
lean_object* v_reuseFailAlloc_6107_; 
v_reuseFailAlloc_6107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6107_, 0, v___x_6104_);
v___x_6106_ = v_reuseFailAlloc_6107_;
goto v_reusejp_6105_;
}
v_reusejp_6105_:
{
return v___x_6106_;
}
}
}
else
{
lean_object* v_a_6109_; lean_object* v___x_6111_; uint8_t v_isShared_6112_; uint8_t v_isSharedCheck_6116_; 
lean_dec(v___x_6097_);
v_a_6109_ = lean_ctor_get(v___x_6098_, 0);
v_isSharedCheck_6116_ = !lean_is_exclusive(v___x_6098_);
if (v_isSharedCheck_6116_ == 0)
{
v___x_6111_ = v___x_6098_;
v_isShared_6112_ = v_isSharedCheck_6116_;
goto v_resetjp_6110_;
}
else
{
lean_inc(v_a_6109_);
lean_dec(v___x_6098_);
v___x_6111_ = lean_box(0);
v_isShared_6112_ = v_isSharedCheck_6116_;
goto v_resetjp_6110_;
}
v_resetjp_6110_:
{
lean_object* v___x_6114_; 
if (v_isShared_6112_ == 0)
{
v___x_6114_ = v___x_6111_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6115_; 
v_reuseFailAlloc_6115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6115_, 0, v_a_6109_);
v___x_6114_ = v_reuseFailAlloc_6115_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
return v___x_6114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v_goal_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v_goal_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
lean_dec(v___y_6126_);
lean_dec_ref(v___y_6125_);
lean_dec(v___y_6124_);
lean_dec_ref(v___y_6123_);
lean_dec(v___y_6122_);
lean_dec_ref(v___y_6121_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
lean_dec(v___y_6118_);
return v_res_6128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
lean_object* v___x_6142_; 
v___x_6142_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6129_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
return v___x_6142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_){
_start:
{
lean_object* v_res_6156_; 
v_res_6156_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_);
lean_dec(v___y_6154_);
lean_dec_ref(v___y_6153_);
lean_dec(v___y_6152_);
lean_dec_ref(v___y_6151_);
lean_dec(v___y_6150_);
lean_dec_ref(v___y_6149_);
lean_dec(v___y_6148_);
lean_dec_ref(v___y_6147_);
lean_dec(v___y_6146_);
lean_dec_ref(v___y_6144_);
return v_res_6156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6157_, lean_object* v___f_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6172_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6172_, 0, v___y_6157_);
v___x_6173_ = l_Lean_Meta_Grind_Action_andThen(v___x_6172_, v___f_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6174_, lean_object* v___f_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_){
_start:
{
lean_object* v_res_6189_; 
v_res_6189_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6174_, v___f_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_);
lean_dec(v___y_6187_);
lean_dec_ref(v___y_6186_);
lean_dec(v___y_6185_);
lean_dec_ref(v___y_6184_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec(v___y_6179_);
return v_res_6189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6191_, uint8_t v_compress_6192_, lean_object* v_goal_6193_, lean_object* v_kna_6194_, lean_object* v_kp_6195_, lean_object* v_a_6196_, lean_object* v_a_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_){
_start:
{
lean_object* v_toGoalState_6206_; lean_object* v_mvarId_6207_; lean_object* v___f_6208_; lean_object* v___x_6209_; 
v_toGoalState_6206_ = lean_ctor_get(v_goal_6193_, 0);
lean_inc_ref(v_toGoalState_6206_);
v_mvarId_6207_ = lean_ctor_get(v_goal_6193_, 1);
lean_inc(v_mvarId_6207_);
v___f_6208_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed), 11, 1);
lean_closure_set(v___f_6208_, 0, v_goal_6193_);
v___x_6209_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6207_, v___f_6208_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_, v_a_6204_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_object* v_a_6210_; lean_object* v_fst_6211_; 
v_a_6210_ = lean_ctor_get(v___x_6209_, 0);
lean_inc(v_a_6210_);
lean_dec_ref_known(v___x_6209_, 1);
v_fst_6211_ = lean_ctor_get(v_a_6210_, 0);
if (lean_obj_tag(v_fst_6211_) == 1)
{
lean_object* v_split_6212_; lean_object* v_snd_6213_; lean_object* v_c_6214_; lean_object* v_numCases_6215_; uint8_t v_isRec_6216_; lean_object* v_candidates_6217_; lean_object* v___f_6218_; lean_object* v___y_6220_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; uint8_t v___x_6233_; 
lean_inc_ref(v_fst_6211_);
v_split_6212_ = lean_ctor_get(v_toGoalState_6206_, 14);
lean_inc_ref(v_split_6212_);
lean_dec_ref(v_toGoalState_6206_);
v_snd_6213_ = lean_ctor_get(v_a_6210_, 1);
lean_inc(v_snd_6213_);
lean_dec(v_a_6210_);
v_c_6214_ = lean_ctor_get(v_fst_6211_, 0);
lean_inc_ref(v_c_6214_);
v_numCases_6215_ = lean_ctor_get(v_fst_6211_, 1);
lean_inc(v_numCases_6215_);
v_isRec_6216_ = lean_ctor_get_uint8(v_fst_6211_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6211_, 2);
v_candidates_6217_ = lean_ctor_get(v_split_6212_, 1);
lean_inc(v_candidates_6217_);
lean_dec_ref(v_split_6212_);
v___f_6218_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___x_6228_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6214_);
v___x_6229_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6213_, v___x_6228_);
lean_dec_ref(v___x_6228_);
v___x_6230_ = lean_unsigned_to_nat(1u);
v___x_6233_ = lean_nat_dec_lt(v___x_6230_, v_numCases_6215_);
if (v___x_6233_ == 0)
{
if (v_isRec_6216_ == 0)
{
v___y_6220_ = v___x_6229_;
goto v___jp_6219_;
}
else
{
goto v___jp_6231_;
}
}
else
{
goto v___jp_6231_;
}
v___jp_6219_:
{
lean_object* v___f_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___f_6221_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6221_, 0, v___y_6220_);
lean_closure_set(v___f_6221_, 1, v___f_6218_);
v___x_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6222_, 0, v_candidates_6217_);
v___x_6223_ = lean_box(v_isRec_6216_);
v___x_6224_ = lean_box(v_stopAtFirstFailure_6191_);
v___x_6225_ = lean_box(v_compress_6192_);
v___x_6226_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6226_, 0, v_c_6214_);
lean_closure_set(v___x_6226_, 1, v_numCases_6215_);
lean_closure_set(v___x_6226_, 2, v___x_6223_);
lean_closure_set(v___x_6226_, 3, v___x_6224_);
lean_closure_set(v___x_6226_, 4, v___x_6225_);
lean_closure_set(v___x_6226_, 5, v___x_6222_);
v___x_6227_ = l_Lean_Meta_Grind_Action_andThen(v___x_6226_, v___f_6221_, v_snd_6213_, v_kna_6194_, v_kp_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_, v_a_6204_);
return v___x_6227_;
}
v___jp_6231_:
{
lean_object* v___x_6232_; 
v___x_6232_ = lean_nat_add(v___x_6229_, v___x_6230_);
lean_dec(v___x_6229_);
v___y_6220_ = v___x_6232_;
goto v___jp_6219_;
}
}
else
{
lean_object* v_snd_6234_; lean_object* v___x_6235_; 
lean_dec_ref(v_toGoalState_6206_);
lean_dec_ref(v_kp_6195_);
v_snd_6234_ = lean_ctor_get(v_a_6210_, 1);
lean_inc(v_snd_6234_);
lean_dec(v_a_6210_);
lean_inc(v_a_6204_);
lean_inc_ref(v_a_6203_);
lean_inc(v_a_6202_);
lean_inc_ref(v_a_6201_);
lean_inc(v_a_6200_);
lean_inc_ref(v_a_6199_);
lean_inc(v_a_6198_);
lean_inc_ref(v_a_6197_);
lean_inc(v_a_6196_);
v___x_6235_ = lean_apply_11(v_kna_6194_, v_snd_6234_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_, v_a_6204_, lean_box(0));
return v___x_6235_;
}
}
else
{
lean_object* v_a_6236_; lean_object* v___x_6238_; uint8_t v_isShared_6239_; uint8_t v_isSharedCheck_6243_; 
lean_dec_ref(v_toGoalState_6206_);
lean_dec_ref(v_kp_6195_);
lean_dec_ref(v_kna_6194_);
v_a_6236_ = lean_ctor_get(v___x_6209_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6209_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6238_ = v___x_6209_;
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
else
{
lean_inc(v_a_6236_);
lean_dec(v___x_6209_);
v___x_6238_ = lean_box(0);
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
v_resetjp_6237_:
{
lean_object* v___x_6241_; 
if (v_isShared_6239_ == 0)
{
v___x_6241_ = v___x_6238_;
goto v_reusejp_6240_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_a_6236_);
v___x_6241_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6240_;
}
v_reusejp_6240_:
{
return v___x_6241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6244_, lean_object* v_compress_6245_, lean_object* v_goal_6246_, lean_object* v_kna_6247_, lean_object* v_kp_6248_, lean_object* v_a_6249_, lean_object* v_a_6250_, lean_object* v_a_6251_, lean_object* v_a_6252_, lean_object* v_a_6253_, lean_object* v_a_6254_, lean_object* v_a_6255_, lean_object* v_a_6256_, lean_object* v_a_6257_, lean_object* v_a_6258_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6259_; uint8_t v_compress_boxed_6260_; lean_object* v_res_6261_; 
v_stopAtFirstFailure_boxed_6259_ = lean_unbox(v_stopAtFirstFailure_6244_);
v_compress_boxed_6260_ = lean_unbox(v_compress_6245_);
v_res_6261_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6259_, v_compress_boxed_6260_, v_goal_6246_, v_kna_6247_, v_kp_6248_, v_a_6249_, v_a_6250_, v_a_6251_, v_a_6252_, v_a_6253_, v_a_6254_, v_a_6255_, v_a_6256_, v_a_6257_);
lean_dec(v_a_6257_);
lean_dec_ref(v_a_6256_);
lean_dec(v_a_6255_);
lean_dec_ref(v_a_6254_);
lean_dec(v_a_6253_);
lean_dec_ref(v_a_6252_);
lean_dec(v_a_6251_);
lean_dec_ref(v_a_6250_);
lean_dec(v_a_6249_);
return v_res_6261_;
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
