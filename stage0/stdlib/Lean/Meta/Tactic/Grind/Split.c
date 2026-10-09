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
uint8_t l_Lean_Meta_Grind_instBEqSplitStatus_beq(lean_object* v_x_51_, lean_object* v_x_52_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqSplitStatus_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_51_ = stack[0].m_obj;
lean_object* v_x_52_ = stack[1].m_obj;
uint8_t v_res_67_;
v_res_67_ = l_Lean_Meta_Grind_instBEqSplitStatus_beq(v_x_51_, v_x_52_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus_beq___boxed(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_Meta_Grind_instBEqSplitStatus_beq(v_x_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_x_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_to_int(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___y_93_; lean_object* v___y_100_; 
switch(lean_obj_tag(v_x_90_))
{
case 0:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_91_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_100_ = v___x_108_;
goto v___jp_99_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_100_ = v___x_109_;
goto v___jp_99_;
}
}
case 1:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_91_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_93_ = v___x_112_;
goto v___jp_92_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_93_ = v___x_113_;
goto v___jp_92_;
}
}
default: 
{
lean_object* v_numCases_114_; uint8_t v_isRec_115_; uint8_t v_tryPostpone_116_; lean_object* v___y_118_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_numCases_114_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_numCases_114_);
v_isRec_115_ = lean_ctor_get_uint8(v_x_90_, sizeof(void*)*1);
v_tryPostpone_116_ = lean_ctor_get_uint8(v_x_90_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_90_, 1);
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = lean_nat_dec_le(v___x_134_, v_prec_91_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__4);
v___y_118_ = v___x_136_;
goto v___jp_117_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5, &l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5_once, _init_l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__5);
v___y_118_ = v___x_137_;
goto v___jp_117_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_119_ = lean_box(1);
v___x_120_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__8));
v___x_121_ = l_Nat_reprFast(v_numCases_114_);
v___x_122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_120_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_119_);
v___x_125_ = l_Bool_repr___redArg(v_isRec_115_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_119_);
v___x_128_ = l_Bool_repr___redArg(v_tryPostpone_116_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_inc(v___y_118_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_118_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = l_Repr_addAppParen(v___x_132_, v_prec_91_);
return v___x_133_;
}
}
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__1));
lean_inc(v___y_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_91_);
return v___x_98_;
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_101_ = ((lean_object*)(l_Lean_Meta_Grind_instReprSplitStatus_repr___closed__3));
lean_inc(v___y_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___y_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
v___x_105_ = l_Repr_addAppParen(v___x_104_, v_prec_91_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus_repr___boxed(lean_object* v_x_138_, lean_object* v_prec_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_Grind_instReprSplitStatus_repr(v_x_138_, v_prec_139_);
lean_dec(v_prec_139_);
return v_res_140_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object* v_c_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___y_152_; lean_object* v___x_178_; 
lean_inc_ref(v_c_143_);
v___x_178_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; uint8_t v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v___x_180_ = lean_unbox(v_a_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec_ref_known(v___x_178_, 1);
v___x_181_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
v___y_152_ = v___x_181_;
goto v___jp_151_;
}
else
{
lean_dec_ref(v_c_143_);
v___y_152_ = v___x_178_;
goto v___jp_151_;
}
}
else
{
lean_dec_ref(v_c_143_);
v___y_152_ = v___x_178_;
goto v___jp_151_;
}
v___jp_151_:
{
if (lean_obj_tag(v___y_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_169_; 
v_a_153_ = lean_ctor_get(v___y_152_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___y_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_155_ = v___y_152_;
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___y_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v___x_157_; 
v___x_157_ = lean_unbox(v_a_153_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; uint8_t v___x_161_; lean_object* v___x_163_; 
v___x_158_ = lean_unsigned_to_nat(2u);
v___x_159_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_unbox(v_a_153_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_160_);
v___x_161_ = lean_unbox(v_a_153_);
lean_dec(v_a_153_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1 + 1, v___x_161_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_159_);
v___x_163_ = v___x_155_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_159_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_a_153_);
v___x_165_ = lean_box(0);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_165_);
v___x_167_ = v___x_155_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___y_152_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___y_152_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___y_152_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___y_152_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_143_ = stack[0].m_obj;
lean_object* v_a_144_ = stack[1].m_obj;
lean_object* v_a_145_ = stack[2].m_obj;
lean_object* v_a_146_ = stack[3].m_obj;
lean_object* v_a_147_ = stack[4].m_obj;
lean_object* v_a_148_ = stack[5].m_obj;
lean_object* v_a_149_ = stack[6].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
stack->m_obj
 = v_res_182_;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* v_c_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_192_, v_a_193_, v_a_197_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_192_ = stack[0].m_obj;
lean_object* v_a_193_ = stack[1].m_obj;
lean_object* v_a_194_ = stack[2].m_obj;
lean_object* v_a_195_ = stack[3].m_obj;
lean_object* v_a_196_ = stack[4].m_obj;
lean_object* v_a_197_ = stack[5].m_obj;
lean_object* v_a_198_ = stack[6].m_obj;
lean_object* v_a_199_ = stack[7].m_obj;
lean_object* v_a_200_ = stack[8].m_obj;
lean_object* v_a_201_ = stack[9].m_obj;
lean_object* v_a_202_ = stack[10].m_obj;
lean_object* v_res_205_;
v_res_205_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* v_c_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
return v_res_218_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___y_230_; lean_object* v___x_256_; 
lean_inc_ref(v_e_219_);
v___x_256_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_219_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; uint8_t v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = lean_unbox(v_a_257_);
lean_dec(v_a_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v_b_221_);
lean_dec_ref(v_a_220_);
v___x_259_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_219_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_273_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_273_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_273_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_273_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
uint8_t v___x_264_; 
v___x_264_ = lean_unbox(v_a_260_);
lean_dec(v_a_260_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_box(1);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_box(0);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_269_);
v___x_271_ = v___x_262_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_259_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_259_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v_e_219_);
v___x_282_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_220_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; uint8_t v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v___x_284_ = lean_unbox(v_a_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
lean_dec_ref_known(v___x_282_, 1);
v___x_285_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
v___y_230_ = v___x_285_;
goto v___jp_229_;
}
else
{
lean_dec_ref(v_b_221_);
v___y_230_ = v___x_282_;
goto v___jp_229_;
}
}
else
{
lean_dec_ref(v_b_221_);
v___y_230_ = v___x_282_;
goto v___jp_229_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_b_221_);
lean_dec_ref(v_a_220_);
lean_dec_ref(v_e_219_);
v_a_286_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_256_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_256_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
v___jp_229_:
{
if (lean_obj_tag(v___y_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_247_; 
v_a_231_ = lean_ctor_get(v___y_230_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___y_230_);
if (v_isSharedCheck_247_ == 0)
{
v___x_233_ = v___y_230_;
v_isShared_234_ = v_isSharedCheck_247_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___y_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_247_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; 
v___x_235_ = lean_unbox(v_a_231_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; uint8_t v___x_239_; lean_object* v___x_241_; 
v___x_236_ = lean_unsigned_to_nat(2u);
v___x_237_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_unbox(v_a_231_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_238_);
v___x_239_ = lean_unbox(v_a_231_);
lean_dec(v_a_231_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1 + 1, v___x_239_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_237_);
v___x_241_ = v___x_233_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_237_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_245_; 
lean_dec(v_a_231_);
v___x_243_ = lean_box(0);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_243_);
v___x_245_ = v___x_233_;
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
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_a_248_ = lean_ctor_get(v___y_230_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___y_230_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___y_230_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___y_230_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_219_ = stack[0].m_obj;
lean_object* v_a_220_ = stack[1].m_obj;
lean_object* v_b_221_ = stack[2].m_obj;
lean_object* v_a_222_ = stack[3].m_obj;
lean_object* v_a_223_ = stack[4].m_obj;
lean_object* v_a_224_ = stack[5].m_obj;
lean_object* v_a_225_ = stack[6].m_obj;
lean_object* v_a_226_ = stack[7].m_obj;
lean_object* v_a_227_ = stack[8].m_obj;
lean_object* v_res_294_;
v_res_294_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_219_, v_a_220_, v_b_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_295_, v_a_296_, v_b_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
return v_res_305_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* v_e_306_, lean_object* v_a_307_, lean_object* v_b_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_306_, v_a_307_, v_b_308_, v_a_309_, v_a_313_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_306_ = stack[0].m_obj;
lean_object* v_a_307_ = stack[1].m_obj;
lean_object* v_b_308_ = stack[2].m_obj;
lean_object* v_a_309_ = stack[3].m_obj;
lean_object* v_a_310_ = stack[4].m_obj;
lean_object* v_a_311_ = stack[5].m_obj;
lean_object* v_a_312_ = stack[6].m_obj;
lean_object* v_a_313_ = stack[7].m_obj;
lean_object* v_a_314_ = stack[8].m_obj;
lean_object* v_a_315_ = stack[9].m_obj;
lean_object* v_a_316_ = stack[10].m_obj;
lean_object* v_a_317_ = stack[11].m_obj;
lean_object* v_a_318_ = stack[12].m_obj;
lean_object* v_res_321_;
v_res_321_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_306_, v_a_307_, v_b_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* v_e_322_, lean_object* v_a_323_, lean_object* v_b_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_322_, v_a_323_, v_b_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_336_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_b_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___y_348_; lean_object* v___x_374_; 
lean_inc_ref(v_e_337_);
v___x_374_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_337_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_407_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_407_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_407_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_407_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_unbox(v_a_375_);
lean_dec(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_del_object(v___x_377_);
v___x_380_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_337_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_394_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_394_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_394_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_394_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_a_338_);
v___x_386_ = lean_box(1);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_390_; 
lean_del_object(v___x_383_);
v___x_390_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_338_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; uint8_t v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v___x_392_ = lean_unbox(v_a_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec_ref_known(v___x_390_, 1);
v___x_393_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
v___y_348_ = v___x_393_;
goto v___jp_347_;
}
else
{
lean_dec_ref(v_b_339_);
v___y_348_ = v___x_390_;
goto v___jp_347_;
}
}
else
{
lean_dec_ref(v_b_339_);
v___y_348_ = v___x_390_;
goto v___jp_347_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_a_338_);
v_a_395_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_380_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_380_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
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
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_a_338_);
lean_dec_ref(v_e_337_);
v___x_403_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_403_);
v___x_405_ = v___x_377_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_b_339_);
lean_dec_ref(v_a_338_);
lean_dec_ref(v_e_337_);
v_a_408_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_374_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_374_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
v___jp_347_:
{
if (lean_obj_tag(v___y_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_365_; 
v_a_349_ = lean_ctor_get(v___y_348_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___y_348_);
if (v_isSharedCheck_365_ == 0)
{
v___x_351_ = v___y_348_;
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___y_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
uint8_t v___x_353_; 
v___x_353_ = lean_unbox(v_a_349_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; lean_object* v___x_359_; 
v___x_354_ = lean_unsigned_to_nat(2u);
v___x_355_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_355_, 0, v___x_354_);
v___x_356_ = lean_unbox(v_a_349_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_356_);
v___x_357_ = lean_unbox(v_a_349_);
lean_dec(v_a_349_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 1, v___x_357_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_355_);
v___x_359_ = v___x_351_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_355_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_dec(v_a_349_);
v___x_361_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_361_);
v___x_363_ = v___x_351_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___y_348_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___y_348_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___y_348_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___y_348_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_337_ = stack[0].m_obj;
lean_object* v_a_338_ = stack[1].m_obj;
lean_object* v_b_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_a_344_ = stack[7].m_obj;
lean_object* v_a_345_ = stack[8].m_obj;
lean_object* v_res_416_;
v_res_416_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_337_, v_a_338_, v_b_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_b_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_417_, v_a_418_, v_b_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
return v_res_427_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_b_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_428_, v_a_429_, v_b_430_, v_a_431_, v_a_435_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_442_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_428_ = stack[0].m_obj;
lean_object* v_a_429_ = stack[1].m_obj;
lean_object* v_b_430_ = stack[2].m_obj;
lean_object* v_a_431_ = stack[3].m_obj;
lean_object* v_a_432_ = stack[4].m_obj;
lean_object* v_a_433_ = stack[5].m_obj;
lean_object* v_a_434_ = stack[6].m_obj;
lean_object* v_a_435_ = stack[7].m_obj;
lean_object* v_a_436_ = stack[8].m_obj;
lean_object* v_a_437_ = stack[9].m_obj;
lean_object* v_a_438_ = stack[10].m_obj;
lean_object* v_a_439_ = stack[11].m_obj;
lean_object* v_a_440_ = stack[12].m_obj;
lean_object* v_res_443_;
v_res_443_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_428_, v_a_429_, v_b_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* v_e_444_, lean_object* v_a_445_, lean_object* v_b_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_444_, v_a_445_, v_b_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
return v_res_458_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* v_e_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___y_473_; lean_object* v___y_496_; lean_object* v___y_515_; lean_object* v___y_538_; lean_object* v___x_553_; 
lean_inc_ref(v_e_459_);
v___x_553_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_459_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_459_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_570_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; 
v___x_561_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
v___x_562_ = lean_box(1);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_562_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v___x_566_; 
lean_del_object(v___x_559_);
lean_inc_ref(v_a_460_);
v___x_566_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_460_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; uint8_t v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v___x_568_ = lean_unbox(v_a_567_);
if (v___x_568_ == 0)
{
v___y_496_ = v___x_566_;
goto v___jp_495_;
}
else
{
lean_object* v___x_569_; 
lean_dec_ref_known(v___x_566_, 1);
lean_inc_ref(v_b_461_);
v___x_569_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
v___y_496_ = v___x_569_;
goto v___jp_495_;
}
}
else
{
v___y_496_ = v___x_566_;
goto v___jp_495_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
v_a_571_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_556_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_556_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec_ref(v_e_459_);
lean_inc_ref(v_a_460_);
v___x_579_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_460_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; uint8_t v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v___x_581_ = lean_unbox(v_a_580_);
if (v___x_581_ == 0)
{
v___y_538_ = v___x_579_;
goto v___jp_537_;
}
else
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_579_, 1);
lean_inc_ref(v_b_461_);
v___x_582_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
v___y_538_ = v___x_582_;
goto v___jp_537_;
}
}
else
{
v___y_538_ = v___x_579_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
lean_dec_ref(v_e_459_);
v_a_583_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_553_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_553_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
v___jp_469_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
v___jp_472_:
{
if (lean_obj_tag(v___y_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_486_; 
v_a_474_ = lean_ctor_get(v___y_473_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___y_473_);
if (v_isSharedCheck_486_ == 0)
{
v___x_476_ = v___y_473_;
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___y_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_unbox(v_a_474_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; uint8_t v___x_482_; lean_object* v___x_484_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = lean_unbox(v_a_474_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_481_);
v___x_482_ = lean_unbox(v_a_474_);
lean_dec(v_a_474_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1 + 1, v___x_482_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_480_);
v___x_484_ = v___x_476_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_480_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
else
{
lean_del_object(v___x_476_);
lean_dec(v_a_474_);
goto v___jp_469_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___y_473_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___y_473_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___y_473_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___y_473_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
v___jp_495_:
{
if (lean_obj_tag(v___y_496_) == 0)
{
lean_object* v_a_497_; uint8_t v___x_498_; 
v_a_497_ = lean_ctor_get(v___y_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___y_496_, 1);
v___x_498_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_460_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; uint8_t v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v___x_501_ = lean_unbox(v_a_500_);
if (v___x_501_ == 0)
{
lean_dec_ref(v_b_461_);
v___y_473_ = v___x_499_;
goto v___jp_472_;
}
else
{
lean_object* v___x_502_; 
lean_dec_ref_known(v___x_499_, 1);
v___x_502_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
v___y_473_ = v___x_502_;
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v_b_461_);
v___y_473_ = v___x_499_;
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
goto v___jp_469_;
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
v_a_503_ = lean_ctor_get(v___y_496_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___y_496_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___y_496_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
v___jp_511_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
v___jp_514_:
{
if (lean_obj_tag(v___y_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_528_; 
v_a_516_ = lean_ctor_get(v___y_515_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___y_515_);
if (v_isSharedCheck_528_ == 0)
{
v___x_518_ = v___y_515_;
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___y_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint8_t v___x_520_; 
v___x_520_ = lean_unbox(v_a_516_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; uint8_t v___x_524_; lean_object* v___x_526_; 
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_unbox(v_a_516_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_523_);
v___x_524_ = lean_unbox(v_a_516_);
lean_dec(v_a_516_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1 + 1, v___x_524_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_522_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_522_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_del_object(v___x_518_);
lean_dec(v_a_516_);
goto v___jp_511_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___y_515_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___y_515_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___y_515_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___y_515_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_537_:
{
if (lean_obj_tag(v___y_538_) == 0)
{
lean_object* v_a_539_; uint8_t v___x_540_; 
v_a_539_ = lean_ctor_get(v___y_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___y_538_, 1);
v___x_540_ = lean_unbox(v_a_539_);
lean_dec(v_a_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_460_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; uint8_t v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v___x_543_ = lean_unbox(v_a_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_b_461_);
v___y_515_ = v___x_541_;
goto v___jp_514_;
}
else
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_541_, 1);
v___x_544_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
v___y_515_ = v___x_544_;
goto v___jp_514_;
}
}
else
{
lean_dec_ref(v_b_461_);
v___y_515_ = v___x_541_;
goto v___jp_514_;
}
}
else
{
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
goto v___jp_511_;
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_b_461_);
lean_dec_ref(v_a_460_);
v_a_545_ = lean_ctor_get(v___y_538_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___y_538_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___y_538_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___y_538_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_459_ = stack[0].m_obj;
lean_object* v_a_460_ = stack[1].m_obj;
lean_object* v_b_461_ = stack[2].m_obj;
lean_object* v_a_462_ = stack[3].m_obj;
lean_object* v_a_463_ = stack[4].m_obj;
lean_object* v_a_464_ = stack[5].m_obj;
lean_object* v_a_465_ = stack[6].m_obj;
lean_object* v_a_466_ = stack[7].m_obj;
lean_object* v_a_467_ = stack[8].m_obj;
lean_object* v_res_591_;
v_res_591_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_459_, v_a_460_, v_b_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_b_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_592_, v_a_593_, v_b_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
return v_res_602_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_603_, v_a_604_, v_b_605_, v_a_606_, v_a_610_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
return v___x_617_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_603_ = stack[0].m_obj;
lean_object* v_a_604_ = stack[1].m_obj;
lean_object* v_b_605_ = stack[2].m_obj;
lean_object* v_a_606_ = stack[3].m_obj;
lean_object* v_a_607_ = stack[4].m_obj;
lean_object* v_a_608_ = stack[5].m_obj;
lean_object* v_a_609_ = stack[6].m_obj;
lean_object* v_a_610_ = stack[7].m_obj;
lean_object* v_a_611_ = stack[8].m_obj;
lean_object* v_a_612_ = stack[9].m_obj;
lean_object* v_a_613_ = stack[10].m_obj;
lean_object* v_a_614_ = stack[11].m_obj;
lean_object* v_a_615_ = stack[12].m_obj;
lean_object* v_res_618_;
v_res_618_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_603_, v_a_604_, v_b_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* v_e_619_, lean_object* v_a_620_, lean_object* v_b_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_619_, v_a_620_, v_b_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec(v_a_622_);
return v_res_633_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* v_c_634_, uint8_t v___x_635_, uint8_t v_d_636_, lean_object* v_a_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
if (v_d_636_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_st_ref_get(v___y_639_);
v___x_651_ = l_Lean_Expr_isApp(v_a_637_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v___x_650_);
lean_dec_ref(v_a_637_);
lean_dec_ref(v_c_634_);
v___x_652_ = lean_box(v_d_636_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
else
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = l_Lean_Meta_Grind_Goal_isCongruent(v___x_650_, v_c_634_, v_a_637_);
lean_dec(v___x_650_);
v___x_655_ = lean_box(v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v_a_637_);
lean_dec_ref(v_c_634_);
v___x_657_ = lean_box(v___x_635_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_634_ = stack[0].m_obj;
uint8_t v___x_635_ = stack[1].m_num;
uint8_t v_d_636_ = stack[2].m_num;
lean_object* v_a_637_ = stack[3].m_obj;
lean_object* v_x_638_ = stack[4].m_obj;
lean_object* v___y_639_ = stack[5].m_obj;
lean_object* v___y_640_ = stack[6].m_obj;
lean_object* v___y_641_ = stack[7].m_obj;
lean_object* v___y_642_ = stack[8].m_obj;
lean_object* v___y_643_ = stack[9].m_obj;
lean_object* v___y_644_ = stack[10].m_obj;
lean_object* v___y_645_ = stack[11].m_obj;
lean_object* v___y_646_ = stack[12].m_obj;
lean_object* v___y_647_ = stack[13].m_obj;
lean_object* v___y_648_ = stack[14].m_obj;
lean_object* v_res_659_;
v_res_659_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_634_, v___x_635_, v_d_636_, v_a_637_, v_x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* v_c_660_, lean_object* v___x_661_, lean_object* v_d_662_, lean_object* v_a_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___x_7896__boxed_676_; uint8_t v_d_boxed_677_; lean_object* v_res_678_; 
v___x_7896__boxed_676_ = lean_unbox(v___x_661_);
v_d_boxed_677_ = lean_unbox(v_d_662_);
v_res_678_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_660_, v___x_7896__boxed_676_, v_d_boxed_677_, v_a_663_, v_x_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec(v___y_665_);
return v_res_678_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object* v_f_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_i_682_, lean_object* v_acc_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_array_get_size(v_keys_680_);
v___x_696_ = lean_nat_dec_lt(v_i_682_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_dec(v_i_682_);
lean_dec_ref(v_f_679_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_acc_683_);
return v___x_697_;
}
else
{
lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v___x_700_; 
v_k_698_ = lean_array_fget_borrowed(v_keys_680_, v_i_682_);
v_v_699_ = lean_array_fget_borrowed(v_vals_681_, v_i_682_);
lean_inc_ref(v_f_679_);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc(v___y_684_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v___x_700_ = lean_apply_14(v_f_679_, v_acc_683_, v_k_698_, v_v_699_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_add(v_i_682_, v___x_702_);
lean_dec(v_i_682_);
v_i_682_ = v___x_703_;
v_acc_683_ = v_a_701_;
goto _start;
}
else
{
lean_dec(v_i_682_);
lean_dec_ref(v_f_679_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_679_ = stack[0].m_obj;
lean_object* v_keys_680_ = stack[1].m_obj;
lean_object* v_vals_681_ = stack[2].m_obj;
lean_object* v_i_682_ = stack[3].m_obj;
lean_object* v_acc_683_ = stack[4].m_obj;
lean_object* v___y_684_ = stack[5].m_obj;
lean_object* v___y_685_ = stack[6].m_obj;
lean_object* v___y_686_ = stack[7].m_obj;
lean_object* v___y_687_ = stack[8].m_obj;
lean_object* v___y_688_ = stack[9].m_obj;
lean_object* v___y_689_ = stack[10].m_obj;
lean_object* v___y_690_ = stack[11].m_obj;
lean_object* v___y_691_ = stack[12].m_obj;
lean_object* v___y_692_ = stack[13].m_obj;
lean_object* v___y_693_ = stack[14].m_obj;
lean_object* v_res_705_;
v_res_705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_679_, v_keys_680_, v_vals_681_, v_i_682_, v_acc_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_706_, lean_object* v_keys_707_, lean_object* v_vals_708_, lean_object* v_i_709_, lean_object* v_acc_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_706_, v_keys_707_, v_vals_708_, v_i_709_, v_acc_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v_vals_708_);
lean_dec_ref(v_keys_707_);
return v_res_722_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_723_, lean_object* v_as_724_, size_t v_i_725_, size_t v_stop_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_a_740_; lean_object* v___y_745_; uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_725_, v_stop_726_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_array_uget_borrowed(v_as_724_, v_i_725_);
switch(lean_obj_tag(v___x_748_))
{
case 0:
{
lean_object* v_key_749_; lean_object* v_val_750_; lean_object* v___x_751_; 
v_key_749_ = lean_ctor_get(v___x_748_, 0);
v_val_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc_ref(v_f_723_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v___y_729_);
lean_inc(v___y_728_);
lean_inc(v_val_750_);
lean_inc(v_key_749_);
v___x_751_ = lean_apply_14(v_f_723_, v_b_727_, v_key_749_, v_val_750_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, lean_box(0));
v___y_745_ = v___x_751_;
goto v___jp_744_;
}
case 1:
{
lean_object* v_node_752_; lean_object* v___x_753_; 
v_node_752_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_node_752_);
lean_inc_ref(v_f_723_);
v___x_753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_723_, v_node_752_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
v___y_745_ = v___x_753_;
goto v___jp_744_;
}
default: 
{
v_a_740_ = v_b_727_;
goto v___jp_739_;
}
}
}
else
{
lean_object* v___x_754_; 
lean_dec_ref(v_f_723_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_b_727_);
return v___x_754_;
}
v___jp_739_:
{
size_t v___x_741_; size_t v___x_742_; 
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_add(v_i_725_, v___x_741_);
v_i_725_ = v___x_742_;
v_b_727_ = v_a_740_;
goto _start;
}
v___jp_744_:
{
if (lean_obj_tag(v___y_745_) == 0)
{
lean_object* v_a_746_; 
v_a_746_ = lean_ctor_get(v___y_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___y_745_, 1);
v_a_740_ = v_a_746_;
goto v___jp_739_;
}
else
{
lean_dec_ref(v_f_723_);
return v___y_745_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_723_ = stack[0].m_obj;
lean_object* v_as_724_ = stack[1].m_obj;
size_t v_i_725_ = stack[2].m_num;
size_t v_stop_726_ = stack[3].m_num;
lean_object* v_b_727_ = stack[4].m_obj;
lean_object* v___y_728_ = stack[5].m_obj;
lean_object* v___y_729_ = stack[6].m_obj;
lean_object* v___y_730_ = stack[7].m_obj;
lean_object* v___y_731_ = stack[8].m_obj;
lean_object* v___y_732_ = stack[9].m_obj;
lean_object* v___y_733_ = stack[10].m_obj;
lean_object* v___y_734_ = stack[11].m_obj;
lean_object* v___y_735_ = stack[12].m_obj;
lean_object* v___y_736_ = stack[13].m_obj;
lean_object* v___y_737_ = stack[14].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_723_, v_as_724_, v_i_725_, v_stop_726_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
stack->m_obj
 = v_res_755_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v_es_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_783_; 
v_es_770_ = lean_ctor_get(v_x_757_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_783_ == 0)
{
v___x_772_ = v_x_757_;
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_es_770_);
lean_dec(v_x_757_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_array_get_size(v_es_770_);
v___x_776_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v_es_770_);
lean_dec_ref(v_f_756_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_x_758_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_x_758_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
lean_del_object(v___x_772_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_775_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_756_, v_es_770_, v___x_780_, v___x_781_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v_es_770_);
return v___x_782_;
}
}
}
else
{
lean_object* v_ks_784_; lean_object* v_vs_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_ks_784_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_ks_784_);
v_vs_785_ = lean_ctor_get(v_x_757_, 1);
lean_inc_ref(v_vs_785_);
lean_dec_ref_known(v_x_757_, 2);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_756_, v_ks_784_, v_vs_785_, v___x_786_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v_vs_785_);
lean_dec_ref(v_ks_784_);
return v___x_787_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_756_ = stack[0].m_obj;
lean_object* v_x_757_ = stack[1].m_obj;
lean_object* v_x_758_ = stack[2].m_obj;
lean_object* v___y_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v___y_764_ = stack[8].m_obj;
lean_object* v___y_765_ = stack[9].m_obj;
lean_object* v___y_766_ = stack[10].m_obj;
lean_object* v___y_767_ = stack[11].m_obj;
lean_object* v___y_768_ = stack[12].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_756_, v_x_757_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_789_, v_x_790_, v_x_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec(v___y_792_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_804_, lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
size_t v_i_boxed_820_; size_t v_stop_boxed_821_; lean_object* v_res_822_; 
v_i_boxed_820_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_821_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_804_, v_as_805_, v_i_boxed_820_, v_stop_boxed_821_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v_as_805_);
return v_res_822_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = l_Lean_Expr_isApp(v_c_823_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_c_823_);
v___x_836_ = lean_box(v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v_toGoalState_841_; lean_object* v_split_842_; lean_object* v_resolved_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_838_ = lean_box(v___x_835_);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_839_, 0, v_c_823_);
lean_closure_set(v___f_839_, 1, v___x_838_);
v___x_840_ = lean_st_ref_get(v_a_824_);
v_toGoalState_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_toGoalState_841_);
lean_dec(v___x_840_);
v_split_842_ = lean_ctor_get(v_toGoalState_841_, 14);
lean_inc_ref(v_split_842_);
lean_dec_ref(v_toGoalState_841_);
v_resolved_843_ = lean_ctor_get(v_split_842_, 3);
lean_inc_ref(v_resolved_843_);
lean_dec_ref(v_split_842_);
v___x_844_ = 0;
v___x_845_ = lean_box(v___x_844_);
v___x_846_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_839_, v_resolved_843_, v___x_845_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
return v___x_846_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_823_ = stack[0].m_obj;
lean_object* v_a_824_ = stack[1].m_obj;
lean_object* v_a_825_ = stack[2].m_obj;
lean_object* v_a_826_ = stack[3].m_obj;
lean_object* v_a_827_ = stack[4].m_obj;
lean_object* v_a_828_ = stack[5].m_obj;
lean_object* v_a_829_ = stack[6].m_obj;
lean_object* v_a_830_ = stack[7].m_obj;
lean_object* v_a_831_ = stack[8].m_obj;
lean_object* v_a_832_ = stack[9].m_obj;
lean_object* v_a_833_ = stack[10].m_obj;
lean_object* v_res_847_;
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
return v_res_860_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_861_, lean_object* v_f_862_, lean_object* v_init_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_862_, v_map_861_, v_init_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_861_ = stack[0].m_obj;
lean_object* v_f_862_ = stack[1].m_obj;
lean_object* v_init_863_ = stack[2].m_obj;
lean_object* v___y_864_ = stack[3].m_obj;
lean_object* v___y_865_ = stack[4].m_obj;
lean_object* v___y_866_ = stack[5].m_obj;
lean_object* v___y_867_ = stack[6].m_obj;
lean_object* v___y_868_ = stack[7].m_obj;
lean_object* v___y_869_ = stack[8].m_obj;
lean_object* v___y_870_ = stack[9].m_obj;
lean_object* v___y_871_ = stack[10].m_obj;
lean_object* v___y_872_ = stack[11].m_obj;
lean_object* v___y_873_ = stack[12].m_obj;
lean_object* v_res_876_;
v_res_876_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_861_, v_f_862_, v_init_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_877_, lean_object* v_f_878_, lean_object* v_init_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_877_, v_f_878_, v_init_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
return v_res_891_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_892_, lean_object* v_00_u03b2_893_, lean_object* v_map_894_, lean_object* v_f_895_, lean_object* v_init_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_895_, v_map_894_, v_init_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_894_ = stack[2].m_obj;
lean_object* v_f_895_ = stack[3].m_obj;
lean_object* v_init_896_ = stack[4].m_obj;
lean_object* v___y_897_ = stack[5].m_obj;
lean_object* v___y_898_ = stack[6].m_obj;
lean_object* v___y_899_ = stack[7].m_obj;
lean_object* v___y_900_ = stack[8].m_obj;
lean_object* v___y_901_ = stack[9].m_obj;
lean_object* v___y_902_ = stack[10].m_obj;
lean_object* v___y_903_ = stack[11].m_obj;
lean_object* v___y_904_ = stack[12].m_obj;
lean_object* v___y_905_ = stack[13].m_obj;
lean_object* v___y_906_ = stack[14].m_obj;
lean_object* v_res_909_;
v_res_909_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_box(0), lean_box(0), v_map_894_, v_f_895_, v_init_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_910_, lean_object* v_00_u03b2_911_, lean_object* v_map_912_, lean_object* v_f_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_910_, v_00_u03b2_911_, v_map_912_, v_f_913_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
return v_res_926_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_927_, lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_f_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_930_, v_x_931_, v_x_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_930_ = stack[3].m_obj;
lean_object* v_x_931_ = stack[4].m_obj;
lean_object* v_x_932_ = stack[5].m_obj;
lean_object* v___y_933_ = stack[6].m_obj;
lean_object* v___y_934_ = stack[7].m_obj;
lean_object* v___y_935_ = stack[8].m_obj;
lean_object* v___y_936_ = stack[9].m_obj;
lean_object* v___y_937_ = stack[10].m_obj;
lean_object* v___y_938_ = stack[11].m_obj;
lean_object* v___y_939_ = stack[12].m_obj;
lean_object* v___y_940_ = stack[13].m_obj;
lean_object* v___y_941_ = stack[14].m_obj;
lean_object* v___y_942_ = stack[15].m_obj;
lean_object* v_res_945_;
v_res_945_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_box(0), lean_box(0), lean_box(0), v_f_930_, v_x_931_, v_x_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_946_ = _args[0];
lean_object* v_00_u03b1_947_ = _args[1];
lean_object* v_00_u03b2_948_ = _args[2];
lean_object* v_f_949_ = _args[3];
lean_object* v_x_950_ = _args[4];
lean_object* v_x_951_ = _args[5];
lean_object* v___y_952_ = _args[6];
lean_object* v___y_953_ = _args[7];
lean_object* v___y_954_ = _args[8];
lean_object* v___y_955_ = _args[9];
lean_object* v___y_956_ = _args[10];
lean_object* v___y_957_ = _args[11];
lean_object* v___y_958_ = _args[12];
lean_object* v___y_959_ = _args[13];
lean_object* v___y_960_ = _args[14];
lean_object* v___y_961_ = _args[15];
lean_object* v___y_962_ = _args[16];
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_946_, v_00_u03b1_947_, v_00_u03b2_948_, v_f_949_, v_x_950_, v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
return v_res_963_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_964_, lean_object* v_00_u03b2_965_, lean_object* v_00_u03c3_966_, lean_object* v_f_967_, lean_object* v_as_968_, size_t v_i_969_, size_t v_stop_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_967_, v_as_968_, v_i_969_, v_stop_970_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_967_ = stack[3].m_obj;
lean_object* v_as_968_ = stack[4].m_obj;
size_t v_i_969_ = stack[5].m_num;
size_t v_stop_970_ = stack[6].m_num;
lean_object* v_b_971_ = stack[7].m_obj;
lean_object* v___y_972_ = stack[8].m_obj;
lean_object* v___y_973_ = stack[9].m_obj;
lean_object* v___y_974_ = stack[10].m_obj;
lean_object* v___y_975_ = stack[11].m_obj;
lean_object* v___y_976_ = stack[12].m_obj;
lean_object* v___y_977_ = stack[13].m_obj;
lean_object* v___y_978_ = stack[14].m_obj;
lean_object* v___y_979_ = stack[15].m_obj;
lean_object* v___y_980_ = stack[16].m_obj;
lean_object* v___y_981_ = stack[17].m_obj;
lean_object* v_res_984_;
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_box(0), lean_box(0), lean_box(0), v_f_967_, v_as_968_, v_i_969_, v_stop_970_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
stack->m_obj
 = v_res_984_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_985_ = _args[0];
lean_object* v_00_u03b2_986_ = _args[1];
lean_object* v_00_u03c3_987_ = _args[2];
lean_object* v_f_988_ = _args[3];
lean_object* v_as_989_ = _args[4];
lean_object* v_i_990_ = _args[5];
lean_object* v_stop_991_ = _args[6];
lean_object* v_b_992_ = _args[7];
lean_object* v___y_993_ = _args[8];
lean_object* v___y_994_ = _args[9];
lean_object* v___y_995_ = _args[10];
lean_object* v___y_996_ = _args[11];
lean_object* v___y_997_ = _args[12];
lean_object* v___y_998_ = _args[13];
lean_object* v___y_999_ = _args[14];
lean_object* v___y_1000_ = _args[15];
lean_object* v___y_1001_ = _args[16];
lean_object* v___y_1002_ = _args[17];
lean_object* v___y_1003_ = _args[18];
_start:
{
size_t v_i_boxed_1004_; size_t v_stop_boxed_1005_; lean_object* v_res_1006_; 
v_i_boxed_1004_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_1005_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_985_, v_00_u03b2_986_, v_00_u03c3_987_, v_f_988_, v_as_989_, v_i_boxed_1004_, v_stop_boxed_1005_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v_as_989_);
return v_res_1006_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_1007_, lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_f_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_heq_1013_, lean_object* v_i_1014_, lean_object* v_acc_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_1010_, v_keys_1011_, v_vals_1012_, v_i_1014_, v_acc_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1010_ = stack[3].m_obj;
lean_object* v_keys_1011_ = stack[4].m_obj;
lean_object* v_vals_1012_ = stack[5].m_obj;
lean_object* v_i_1014_ = stack[7].m_obj;
lean_object* v_acc_1015_ = stack[8].m_obj;
lean_object* v___y_1016_ = stack[9].m_obj;
lean_object* v___y_1017_ = stack[10].m_obj;
lean_object* v___y_1018_ = stack[11].m_obj;
lean_object* v___y_1019_ = stack[12].m_obj;
lean_object* v___y_1020_ = stack[13].m_obj;
lean_object* v___y_1021_ = stack[14].m_obj;
lean_object* v___y_1022_ = stack[15].m_obj;
lean_object* v___y_1023_ = stack[16].m_obj;
lean_object* v___y_1024_ = stack[17].m_obj;
lean_object* v___y_1025_ = stack[18].m_obj;
lean_object* v_res_1028_;
v_res_1028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_box(0), lean_box(0), lean_box(0), v_f_1010_, v_keys_1011_, v_vals_1012_, lean_box(0), v_i_1014_, v_acc_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
stack->m_obj
 = v_res_1028_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1029_ = _args[0];
lean_object* v_00_u03b1_1030_ = _args[1];
lean_object* v_00_u03b2_1031_ = _args[2];
lean_object* v_f_1032_ = _args[3];
lean_object* v_keys_1033_ = _args[4];
lean_object* v_vals_1034_ = _args[5];
lean_object* v_heq_1035_ = _args[6];
lean_object* v_i_1036_ = _args[7];
lean_object* v_acc_1037_ = _args[8];
lean_object* v___y_1038_ = _args[9];
lean_object* v___y_1039_ = _args[10];
lean_object* v___y_1040_ = _args[11];
lean_object* v___y_1041_ = _args[12];
lean_object* v___y_1042_ = _args[13];
lean_object* v___y_1043_ = _args[14];
lean_object* v___y_1044_ = _args[15];
lean_object* v___y_1045_ = _args[16];
lean_object* v___y_1046_ = _args[17];
lean_object* v___y_1047_ = _args[18];
lean_object* v___y_1048_ = _args[19];
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1029_, v_00_u03b1_1030_, v_00_u03b2_1031_, v_f_1032_, v_keys_1033_, v_vals_1034_, v_heq_1035_, v_i_1036_, v_acc_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v_vals_1034_);
lean_dec_ref(v_keys_1033_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1053_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
lean_ctor_set(v___x_1056_, 4, v___x_1054_);
lean_ctor_set(v___x_1056_, 5, v___x_1054_);
lean_ctor_set(v___x_1056_, 6, v___x_1054_);
lean_ctor_set(v___x_1056_, 7, v___x_1054_);
lean_ctor_set(v___x_1056_, 8, v___x_1054_);
lean_ctor_set(v___x_1056_, 9, v___x_1054_);
lean_ctor_set(v___x_1056_, 10, v___x_1054_);
lean_ctor_set(v___x_1056_, 11, v___x_1053_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_unsigned_to_nat(32u);
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((size_t)5ULL);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_unsigned_to_nat(32u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1065_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v___x_1061_);
lean_ctor_set(v___x_1065_, 3, v___x_1061_);
lean_ctor_set_usize(v___x_1065_, 4, v___x_1060_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_box(1);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1103_, lean_object* v_declHint_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_env_1109_; uint8_t v___x_1110_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_st_ref_get(v___y_1105_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1110_ = l_Lean_Name_isAnonymous(v_declHint_1104_);
if (v___x_1110_ == 0)
{
uint8_t v_isExporting_1111_; 
v_isExporting_1111_ = lean_ctor_get_uint8(v_env_1109_, sizeof(void*)*13);
if (v_isExporting_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v_env_1109_);
lean_dec(v_declHint_1104_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_msg_1103_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
lean_inc_ref(v_env_1109_);
v___x_1113_ = l_Lean_Environment_setExporting(v_env_1109_, v___x_1110_);
lean_inc(v_declHint_1104_);
lean_inc_ref(v___x_1113_);
v___x_1114_ = l_Lean_Environment_contains(v___x_1113_, v_declHint_1104_, v_isExporting_1111_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_env_1109_);
lean_dec(v_declHint_1104_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_msg_1103_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_c_1121_; lean_object* v___x_1122_; 
v___x_1116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1118_ = l_Lean_Options_empty;
v___x_1119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1113_);
lean_ctor_set(v___x_1119_, 1, v___x_1116_);
lean_ctor_set(v___x_1119_, 2, v___x_1117_);
lean_ctor_set(v___x_1119_, 3, v___x_1118_);
lean_inc(v_declHint_1104_);
v___x_1120_ = l_Lean_MessageData_ofConstName(v_declHint_1104_, v___x_1110_);
v_c_1121_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1121_, 0, v___x_1119_);
lean_ctor_set(v_c_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1109_, v_declHint_1104_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref(v_env_1109_);
lean_dec(v_declHint_1104_);
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_c_1121_);
v___x_1125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_MessageData_note(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_msg_1103_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1186_; 
v_val_1130_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1132_ = v___x_1122_;
v_isShared_1133_ = v_isSharedCheck_1186_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v___x_1122_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1186_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v_modules_1135_; lean_object* v_moduleNames_1136_; lean_object* v_mod_1137_; uint8_t v___y_1139_; uint8_t v___x_1169_; 
v___x_1134_ = l_Lean_Environment_header(v_env_1109_);
lean_dec_ref(v_env_1109_);
v_modules_1135_ = lean_ctor_get(v___x_1134_, 3);
lean_inc_ref(v_modules_1135_);
v_moduleNames_1136_ = lean_ctor_get(v___x_1134_, 4);
lean_inc_ref(v_moduleNames_1136_);
lean_dec_ref(v___x_1134_);
v_mod_1137_ = lean_array_get(v___x_1107_, v_moduleNames_1136_, v_val_1130_);
lean_dec_ref(v_moduleNames_1136_);
v___x_1169_ = l_Lean_isPrivateName(v_declHint_1104_);
lean_dec(v_declHint_1104_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_array_get_size(v_modules_1135_);
v___x_1171_ = lean_nat_dec_lt(v_val_1130_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec_ref(v_modules_1135_);
lean_dec(v_val_1130_);
v___y_1139_ = v___x_1169_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1172_; lean_object* v_toImport_1173_; uint8_t v_isExported_1174_; 
v___x_1172_ = lean_array_fget(v_modules_1135_, v_val_1130_);
lean_dec(v_val_1130_);
lean_dec_ref(v_modules_1135_);
v_toImport_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_ref(v_toImport_1173_);
lean_dec(v___x_1172_);
v_isExported_1174_ = lean_ctor_get_uint8(v_toImport_1173_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1173_);
v___y_1139_ = v_isExported_1174_;
goto v___jp_1138_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_modules_1135_);
lean_del_object(v___x_1132_);
lean_dec(v_val_1130_);
v___x_1175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_c_1121_);
v___x_1177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_MessageData_ofName(v_mod_1137_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_MessageData_note(v___x_1182_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_msg_1103_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
v___jp_1138_:
{
if (v___y_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_c_1121_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_ofName(v_mod_1137_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_note(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_msg_1103_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1149_);
v___x_1151_ = v___x_1132_;
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
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_c_1121_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_ofName(v_mod_1137_);
lean_inc_ref(v___x_1157_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1157_);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_note(v___x_1163_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_msg_1103_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1165_);
v___x_1167_ = v___x_1132_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
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
lean_object* v___x_1187_; 
lean_dec_ref(v_env_1109_);
lean_dec(v_declHint_1104_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_msg_1103_);
return v___x_1187_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1103_ = stack[0].m_obj;
lean_object* v_declHint_1104_ = stack[1].m_obj;
lean_object* v___y_1105_ = stack[2].m_obj;
lean_object* v_res_1188_;
v_res_1188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1103_, v_declHint_1104_, v___y_1105_);
stack->m_obj
 = v_res_1188_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1189_, lean_object* v_declHint_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1189_, v_declHint_1190_, v___y_1191_);
lean_dec(v___y_1191_);
return v_res_1193_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1194_, lean_object* v_declHint_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1217_; 
v___x_1207_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1194_, v_declHint_1195_, v___y_1205_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1212_ = l_Lean_unknownIdentifierMessageTag;
v___x_1213_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v_a_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1194_ = stack[0].m_obj;
lean_object* v_declHint_1195_ = stack[1].m_obj;
lean_object* v___y_1196_ = stack[2].m_obj;
lean_object* v___y_1197_ = stack[3].m_obj;
lean_object* v___y_1198_ = stack[4].m_obj;
lean_object* v___y_1199_ = stack[5].m_obj;
lean_object* v___y_1200_ = stack[6].m_obj;
lean_object* v___y_1201_ = stack[7].m_obj;
lean_object* v___y_1202_ = stack[8].m_obj;
lean_object* v___y_1203_ = stack[9].m_obj;
lean_object* v___y_1204_ = stack[10].m_obj;
lean_object* v___y_1205_ = stack[11].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1194_, v_declHint_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1219_, lean_object* v_declHint_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1219_, v_declHint_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v___y_1221_);
return v_res_1232_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v_env_1240_; uint8_t v___x_1241_; lean_object* v_env_1242_; lean_object* v___x_1243_; lean_object* v_toCold_1244_; lean_object* v_mctx_1245_; lean_object* v_lctx_1246_; lean_object* v_options_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1239_ = lean_st_ref_get(v___y_1237_);
v_env_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_env_1240_);
lean_dec(v___x_1239_);
v___x_1241_ = 0;
v_env_1242_ = l_Lean_Environment_setRecordingDeps(v_env_1240_, v___x_1241_);
v___x_1243_ = lean_st_ref_get(v___y_1235_);
v_toCold_1244_ = lean_ctor_get(v___y_1236_, 0);
v_mctx_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc_ref(v_mctx_1245_);
lean_dec(v___x_1243_);
v_lctx_1246_ = lean_ctor_get(v___y_1234_, 2);
v_options_1247_ = lean_ctor_get(v_toCold_1244_, 2);
lean_inc_ref(v_options_1247_);
lean_inc_ref(v_lctx_1246_);
v___x_1248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1248_, 0, v_env_1242_);
lean_ctor_set(v___x_1248_, 1, v_mctx_1245_);
lean_ctor_set(v___x_1248_, 2, v_lctx_1246_);
lean_ctor_set(v___x_1248_, 3, v_options_1247_);
v___x_1249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v_msgData_1233_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1233_ = stack[0].m_obj;
lean_object* v___y_1234_ = stack[1].m_obj;
lean_object* v___y_1235_ = stack[2].m_obj;
lean_object* v___y_1236_ = stack[3].m_obj;
lean_object* v___y_1237_ = stack[4].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_ref_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
v_ref_1265_ = lean_ctor_get(v___y_1262_, 2);
v___x_1266_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_inc(v_ref_1265_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_ref_1265_);
lean_ctor_set(v___x_1271_, 1, v_a_1267_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1259_ = stack[0].m_obj;
lean_object* v___y_1260_ = stack[1].m_obj;
lean_object* v___y_1261_ = stack[2].m_obj;
lean_object* v___y_1262_ = stack[3].m_obj;
lean_object* v___y_1263_ = stack[4].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1284_, lean_object* v_msg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_toCold_1297_; lean_object* v_currRecDepth_1298_; lean_object* v_ref_1299_; uint16_t v_optionFlags_1300_; uint8_t v_suppressElabErrors_1301_; uint8_t v_isRecordingDeps_1302_; lean_object* v_ref_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_toCold_1297_ = lean_ctor_get(v___y_1294_, 0);
v_currRecDepth_1298_ = lean_ctor_get(v___y_1294_, 1);
v_ref_1299_ = lean_ctor_get(v___y_1294_, 2);
v_optionFlags_1300_ = lean_ctor_get_uint16(v___y_1294_, sizeof(void*)*3);
v_suppressElabErrors_1301_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1302_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*3 + 3);
v_ref_1303_ = l_Lean_replaceRef(v_ref_1284_, v_ref_1299_);
lean_inc(v_currRecDepth_1298_);
lean_inc_ref(v_toCold_1297_);
v___x_1304_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1304_, 0, v_toCold_1297_);
lean_ctor_set(v___x_1304_, 1, v_currRecDepth_1298_);
lean_ctor_set(v___x_1304_, 2, v_ref_1303_);
lean_ctor_set_uint16(v___x_1304_, sizeof(void*)*3, v_optionFlags_1300_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*3 + 2, v_suppressElabErrors_1301_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*3 + 3, v_isRecordingDeps_1302_);
v___x_1305_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1285_, v___y_1292_, v___y_1293_, v___x_1304_, v___y_1295_);
lean_dec_ref_known(v___x_1304_, 3);
return v___x_1305_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1284_ = stack[0].m_obj;
lean_object* v_msg_1285_ = stack[1].m_obj;
lean_object* v___y_1286_ = stack[2].m_obj;
lean_object* v___y_1287_ = stack[3].m_obj;
lean_object* v___y_1288_ = stack[4].m_obj;
lean_object* v___y_1289_ = stack[5].m_obj;
lean_object* v___y_1290_ = stack[6].m_obj;
lean_object* v___y_1291_ = stack[7].m_obj;
lean_object* v___y_1292_ = stack[8].m_obj;
lean_object* v___y_1293_ = stack[9].m_obj;
lean_object* v___y_1294_ = stack[10].m_obj;
lean_object* v___y_1295_ = stack[11].m_obj;
lean_object* v_res_1306_;
v_res_1306_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1284_, v_msg_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
stack->m_obj
 = v_res_1306_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1307_, v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec(v_ref_1307_);
return v_res_1320_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1321_, lean_object* v_msg_1322_, lean_object* v_declHint_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v___x_1337_; 
v___x_1335_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1322_, v_declHint_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1321_, v_a_1336_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1337_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1321_ = stack[0].m_obj;
lean_object* v_msg_1322_ = stack[1].m_obj;
lean_object* v_declHint_1323_ = stack[2].m_obj;
lean_object* v___y_1324_ = stack[3].m_obj;
lean_object* v___y_1325_ = stack[4].m_obj;
lean_object* v___y_1326_ = stack[5].m_obj;
lean_object* v___y_1327_ = stack[6].m_obj;
lean_object* v___y_1328_ = stack[7].m_obj;
lean_object* v___y_1329_ = stack[8].m_obj;
lean_object* v___y_1330_ = stack[9].m_obj;
lean_object* v___y_1331_ = stack[10].m_obj;
lean_object* v___y_1332_ = stack[11].m_obj;
lean_object* v___y_1333_ = stack[12].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1321_, v_msg_1322_, v_declHint_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1339_, lean_object* v_msg_1340_, lean_object* v_declHint_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1339_, v_msg_1340_, v_declHint_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v_ref_1339_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1360_, lean_object* v_constName_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1373_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1374_ = 0;
lean_inc(v_constName_1361_);
v___x_1375_ = l_Lean_MessageData_ofConstName(v_constName_1361_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1360_, v___x_1378_, v_constName_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1379_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1360_ = stack[0].m_obj;
lean_object* v_constName_1361_ = stack[1].m_obj;
lean_object* v___y_1362_ = stack[2].m_obj;
lean_object* v___y_1363_ = stack[3].m_obj;
lean_object* v___y_1364_ = stack[4].m_obj;
lean_object* v___y_1365_ = stack[5].m_obj;
lean_object* v___y_1366_ = stack[6].m_obj;
lean_object* v___y_1367_ = stack[7].m_obj;
lean_object* v___y_1368_ = stack[8].m_obj;
lean_object* v___y_1369_ = stack[9].m_obj;
lean_object* v___y_1370_ = stack[10].m_obj;
lean_object* v___y_1371_ = stack[11].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1360_, v_constName_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1381_, lean_object* v_constName_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1381_, v_constName_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
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
lean_dec(v_ref_1381_);
return v_res_1394_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_ref_1407_; lean_object* v___x_1408_; 
v_ref_1407_ = lean_ctor_get(v___y_1404_, 2);
v___x_1408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1407_, v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1395_ = stack[0].m_obj;
lean_object* v___y_1396_ = stack[1].m_obj;
lean_object* v___y_1397_ = stack[2].m_obj;
lean_object* v___y_1398_ = stack[3].m_obj;
lean_object* v___y_1399_ = stack[4].m_obj;
lean_object* v___y_1400_ = stack[5].m_obj;
lean_object* v___y_1401_ = stack[6].m_obj;
lean_object* v___y_1402_ = stack[7].m_obj;
lean_object* v___y_1403_ = stack[8].m_obj;
lean_object* v___y_1404_ = stack[9].m_obj;
lean_object* v___y_1405_ = stack[10].m_obj;
lean_object* v_res_1409_;
v_res_1409_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec(v___y_1411_);
return v_res_1422_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v_env_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = lean_st_ref_get(v___y_1433_);
v_env_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_ref(v_env_1436_);
lean_dec(v___x_1435_);
v___x_1437_ = 0;
lean_inc(v_constName_1423_);
v___x_1438_ = l_Lean_Environment_find_x3f(v_env_1436_, v_constName_1423_, v___x_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1439_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_constName_1423_);
v_val_1440_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_val_1440_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 0);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_val_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1423_ = stack[0].m_obj;
lean_object* v___y_1424_ = stack[1].m_obj;
lean_object* v___y_1425_ = stack[2].m_obj;
lean_object* v___y_1426_ = stack[3].m_obj;
lean_object* v___y_1427_ = stack[4].m_obj;
lean_object* v___y_1428_ = stack[5].m_obj;
lean_object* v___y_1429_ = stack[6].m_obj;
lean_object* v___y_1430_ = stack[7].m_obj;
lean_object* v___y_1431_ = stack[8].m_obj;
lean_object* v___y_1432_ = stack[9].m_obj;
lean_object* v___y_1433_ = stack[10].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec(v___y_1450_);
return v_res_1461_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1462_; double v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_float_of_nat(v___x_1462_);
return v___x_1463_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_ref_1474_; lean_object* v___x_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1521_; 
v_ref_1474_ = lean_ctor_get(v___y_1471_, 2);
v___x_1475_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v_traceState_1481_; lean_object* v_env_1482_; lean_object* v_nextMacroScope_1483_; lean_object* v_ngen_1484_; lean_object* v_auxDeclNGen_1485_; lean_object* v_cache_1486_; lean_object* v_recordedDeps_1487_; lean_object* v_messages_1488_; lean_object* v_infoState_1489_; lean_object* v_snapshotTasks_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1520_; 
v___x_1480_ = lean_st_ref_take(v___y_1472_);
v_traceState_1481_ = lean_ctor_get(v___x_1480_, 4);
v_env_1482_ = lean_ctor_get(v___x_1480_, 0);
v_nextMacroScope_1483_ = lean_ctor_get(v___x_1480_, 1);
v_ngen_1484_ = lean_ctor_get(v___x_1480_, 2);
v_auxDeclNGen_1485_ = lean_ctor_get(v___x_1480_, 3);
v_cache_1486_ = lean_ctor_get(v___x_1480_, 5);
v_recordedDeps_1487_ = lean_ctor_get(v___x_1480_, 6);
v_messages_1488_ = lean_ctor_get(v___x_1480_, 7);
v_infoState_1489_ = lean_ctor_get(v___x_1480_, 8);
v_snapshotTasks_1490_ = lean_ctor_get(v___x_1480_, 9);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1492_ = v___x_1480_;
v_isShared_1493_ = v_isSharedCheck_1520_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_snapshotTasks_1490_);
lean_inc(v_infoState_1489_);
lean_inc(v_messages_1488_);
lean_inc(v_recordedDeps_1487_);
lean_inc(v_cache_1486_);
lean_inc(v_traceState_1481_);
lean_inc(v_auxDeclNGen_1485_);
lean_inc(v_ngen_1484_);
lean_inc(v_nextMacroScope_1483_);
lean_inc(v_env_1482_);
lean_dec(v___x_1480_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1520_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint64_t v_tid_1494_; lean_object* v_traces_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1519_; 
v_tid_1494_ = lean_ctor_get_uint64(v_traceState_1481_, sizeof(void*)*1);
v_traces_1495_ = lean_ctor_get(v_traceState_1481_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_traceState_1481_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1497_ = v_traceState_1481_;
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_traces_1495_);
lean_dec(v_traceState_1481_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1519_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; double v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1502_ = 0;
v___x_1503_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1504_, 0, v_cls_1467_);
lean_ctor_set(v___x_1504_, 1, v___x_1500_);
lean_ctor_set(v___x_1504_, 2, v___x_1503_);
lean_ctor_set_float(v___x_1504_, sizeof(void*)*3, v___x_1501_);
lean_ctor_set_float(v___x_1504_, sizeof(void*)*3 + 8, v___x_1501_);
lean_ctor_set_uint8(v___x_1504_, sizeof(void*)*3 + 16, v___x_1502_);
v___x_1505_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1506_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v_a_1476_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
lean_inc(v_ref_1474_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_ref_1474_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_PersistentArray_push___redArg(v_traces_1495_, v___x_1507_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1508_);
v___x_1510_ = v___x_1497_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
lean_ctor_set_uint64(v_reuseFailAlloc_1518_, sizeof(void*)*1, v_tid_1494_);
v___x_1510_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v___x_1510_);
v___x_1512_ = v___x_1492_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_env_1482_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_nextMacroScope_1483_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_ngen_1484_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_auxDeclNGen_1485_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 5, v_cache_1486_);
lean_ctor_set(v_reuseFailAlloc_1517_, 6, v_recordedDeps_1487_);
lean_ctor_set(v_reuseFailAlloc_1517_, 7, v_messages_1488_);
lean_ctor_set(v_reuseFailAlloc_1517_, 8, v_infoState_1489_);
lean_ctor_set(v_reuseFailAlloc_1517_, 9, v_snapshotTasks_1490_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_st_ref_put(v___y_1472_, v___x_1512_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1499_);
v___x_1515_ = v___x_1478_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1499_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1467_ = stack[0].m_obj;
lean_object* v_msg_1468_ = stack[1].m_obj;
lean_object* v___y_1469_ = stack[2].m_obj;
lean_object* v___y_1470_ = stack[3].m_obj;
lean_object* v___y_1471_ = stack[4].m_obj;
lean_object* v___y_1472_ = stack[5].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1467_, v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1523_, v_msg_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1549_ = l_Lean_Name_append(v___x_1548_, v___x_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; uint8_t v___y_1700_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___x_1828_; 
lean_inc_ref(v_e_1562_);
v___x_1828_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1562_, v_a_1570_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1857_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1857_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1857_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = l_Lean_Expr_cleanupAnnotations(v_a_1829_);
v___x_1834_ = l_Lean_Expr_isApp(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v___x_1833_);
lean_del_object(v___x_1831_);
v___y_1816_ = v_a_1563_;
v___y_1817_ = v_a_1564_;
v___y_1818_ = v_a_1565_;
v___y_1819_ = v_a_1566_;
v___y_1820_ = v_a_1567_;
v___y_1821_ = v_a_1568_;
v___y_1822_ = v_a_1569_;
v___y_1823_ = v_a_1570_;
v___y_1824_ = v_a_1571_;
v___y_1825_ = v_a_1572_;
goto v___jp_1815_;
}
else
{
lean_object* v_arg_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_arg_1835_ = lean_ctor_get(v___x_1833_, 1);
lean_inc_ref(v_arg_1835_);
v___x_1836_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1833_);
v___x_1837_ = l_Lean_Expr_isApp(v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec_ref(v___x_1836_);
lean_dec_ref(v_arg_1835_);
lean_del_object(v___x_1831_);
v___y_1816_ = v_a_1563_;
v___y_1817_ = v_a_1564_;
v___y_1818_ = v_a_1565_;
v___y_1819_ = v_a_1566_;
v___y_1820_ = v_a_1567_;
v___y_1821_ = v_a_1568_;
v___y_1822_ = v_a_1569_;
v___y_1823_ = v_a_1570_;
v___y_1824_ = v_a_1571_;
v___y_1825_ = v_a_1572_;
goto v___jp_1815_;
}
else
{
lean_object* v_arg_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_arg_1838_ = lean_ctor_get(v___x_1836_, 1);
lean_inc_ref(v_arg_1838_);
v___x_1839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1836_);
v___x_1840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1841_ = l_Lean_Expr_isConstOf(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1843_ = l_Lean_Expr_isConstOf(v___x_1839_, v___x_1842_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Lean_Expr_isApp(v___x_1839_);
if (v___x_1844_ == 0)
{
lean_dec_ref(v___x_1839_);
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_arg_1835_);
lean_del_object(v___x_1831_);
v___y_1816_ = v_a_1563_;
v___y_1817_ = v_a_1564_;
v___y_1818_ = v_a_1565_;
v___y_1819_ = v_a_1566_;
v___y_1820_ = v_a_1567_;
v___y_1821_ = v_a_1568_;
v___y_1822_ = v_a_1569_;
v___y_1823_ = v_a_1570_;
v___y_1824_ = v_a_1571_;
v___y_1825_ = v_a_1572_;
goto v___jp_1815_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1839_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1847_ = l_Lean_Expr_isConstOf(v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1845_);
if (v___x_1847_ == 0)
{
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_arg_1835_);
lean_del_object(v___x_1831_);
v___y_1816_ = v_a_1563_;
v___y_1817_ = v_a_1564_;
v___y_1818_ = v_a_1565_;
v___y_1819_ = v_a_1566_;
v___y_1820_ = v_a_1567_;
v___y_1821_ = v_a_1568_;
v___y_1822_ = v_a_1569_;
v___y_1823_ = v_a_1570_;
v___y_1824_ = v_a_1571_;
v___y_1825_ = v_a_1572_;
goto v___jp_1815_;
}
else
{
uint8_t v___x_1848_; 
lean_inc_ref(v_e_1562_);
v___x_1848_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1562_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec_ref(v_arg_1838_);
lean_dec_ref(v_arg_1835_);
lean_dec_ref(v_e_1562_);
v___x_1849_ = lean_unsigned_to_nat(2u);
v___x_1850_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*1, v___x_1848_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*1 + 1, v___x_1848_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1850_);
v___x_1852_ = v___x_1831_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; 
lean_del_object(v___x_1831_);
v___x_1854_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1562_, v_arg_1838_, v_arg_1835_, v_a_1563_, v_a_1567_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
return v___x_1854_;
}
}
}
}
else
{
lean_object* v___x_1855_; 
lean_dec_ref(v___x_1839_);
lean_del_object(v___x_1831_);
v___x_1855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1562_, v_arg_1838_, v_arg_1835_, v_a_1563_, v_a_1567_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
return v___x_1855_;
}
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1839_);
lean_del_object(v___x_1831_);
v___x_1856_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1562_, v_arg_1838_, v_arg_1835_, v_a_1563_, v_a_1567_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_e_1562_);
v_a_1858_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1828_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1828_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
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
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
v___jp_1583_:
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Expr_isFVar(v_e_1562_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v_e_1562_);
v___x_1596_ = lean_box(1);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; 
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc_ref(v_e_1562_);
v___x_1598_ = lean_infer_type(v_e_1562_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = l_Lean_Meta_whnfD(v_a_1599_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_n(v_a_1601_, 2);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1603_ = l_Lean_MessageData_ofExpr(v_e_1562_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_indentExpr(v_a_1601_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_Expr_getAppFn(v_a_1601_);
lean_dec(v_a_1601_);
if (lean_obj_tag(v___x_1609_) == 4)
{
lean_object* v_declName_1610_; lean_object* v___x_1611_; 
v_declName_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_declName_1610_);
lean_dec_ref_known(v___x_1609_, 2);
v___x_1611_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1610_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1644_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1644_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1644_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
if (lean_obj_tag(v_a_1612_) == 5)
{
lean_object* v_val_1616_; lean_object* v_ctors_1617_; uint8_t v_isRec_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1608_, 2);
v_val_1616_ = lean_ctor_get(v_a_1612_, 0);
lean_inc_ref(v_val_1616_);
lean_dec_ref_known(v_a_1612_, 1);
v_ctors_1617_ = lean_ctor_get(v_val_1616_, 4);
lean_inc(v_ctors_1617_);
v_isRec_1618_ = lean_ctor_get_uint8(v_val_1616_, sizeof(void*)*6);
lean_dec_ref(v_val_1616_);
v___x_1619_ = l_List_lengthTR___redArg(v_ctors_1617_);
lean_dec(v_ctors_1617_);
v___x_1620_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*1, v_isRec_1618_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*1 + 1, v___y_1584_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1620_);
v___x_1622_ = v___x_1614_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v___x_1624_; 
lean_del_object(v___x_1614_);
lean_dec(v_a_1612_);
v___x_1624_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1589_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; uint8_t v_verbose_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_verbose_1626_ = lean_ctor_get_uint8(v_a_1625_, 0);
lean_dec(v_a_1625_);
if (v_verbose_1626_ == 0)
{
lean_dec_ref_known(v___x_1608_, 2);
goto v___jp_1577_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Sym_reportIssue(v___x_1608_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
goto v___jp_1577_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
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
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref_known(v___x_1608_, 2);
v_a_1636_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1624_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1624_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref_known(v___x_1608_, 2);
v_a_1645_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1611_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1611_);
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
else
{
lean_object* v___x_1653_; 
lean_dec_ref(v___x_1609_);
v___x_1653_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1589_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; uint8_t v_verbose_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v_verbose_1655_ = lean_ctor_get_uint8(v_a_1654_, 0);
lean_dec(v_a_1654_);
if (v_verbose_1655_ == 0)
{
lean_dec_ref_known(v___x_1608_, 2);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_Sym_reportIssue(v___x_1608_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
goto v___jp_1580_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
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
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref_known(v___x_1608_, 2);
v_a_1665_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1653_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1653_);
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
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_e_1562_);
v_a_1673_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1600_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1600_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_e_1562_);
v_a_1681_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1598_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1598_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
v___jp_1689_:
{
if (v___y_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1562_, v___y_1692_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_inc_ref(v_e_1562_);
v___x_1704_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1562_, v___y_1692_, v___y_1696_, v___y_1691_, v___y_1699_, v___y_1697_, v___y_1695_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1764_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1764_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1764_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_unbox(v_a_1705_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v_env_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_st_ref_get(v___y_1693_);
v_env_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_env_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1711_, v_e_1562_);
if (lean_obj_tag(v___x_1712_) == 1)
{
lean_object* v_val_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1719_; 
lean_dec_ref(v_e_1562_);
v_val_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1713_);
lean_dec(v_val_1713_);
v___x_1715_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
v___x_1716_ = lean_unbox(v_a_1705_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1, v___x_1716_);
v___x_1717_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1 + 1, v___x_1717_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1715_);
v___x_1719_ = v___x_1707_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1715_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v___x_1721_; 
lean_dec(v___x_1712_);
lean_del_object(v___x_1707_);
v___x_1721_ = l_Lean_Expr_getAppFn(v_e_1562_);
if (lean_obj_tag(v___x_1721_) == 4)
{
lean_object* v_declName_1722_; lean_object* v___x_1723_; 
v_declName_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_declName_1722_);
lean_dec_ref_known(v___x_1721_, 2);
v___x_1723_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1722_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
if (lean_obj_tag(v_a_1724_) == 1)
{
lean_object* v_val_1725_; lean_object* v___x_1726_; 
v_val_1725_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v_a_1724_, 1);
lean_inc_ref(v_e_1562_);
v___x_1726_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1562_, v___y_1692_, v___y_1697_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1741_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
lean_del_object(v___x_1729_);
lean_dec(v_val_1725_);
v___x_1732_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___y_1584_ = v___x_1732_;
v___y_1585_ = v___y_1692_;
v___y_1586_ = v___y_1696_;
v___y_1587_ = v___y_1691_;
v___y_1588_ = v___y_1699_;
v___y_1589_ = v___y_1697_;
v___y_1590_ = v___y_1695_;
v___y_1591_ = v___y_1690_;
v___y_1592_ = v___y_1694_;
v___y_1593_ = v___y_1698_;
v___y_1594_ = v___y_1693_;
goto v___jp_1583_;
}
else
{
lean_object* v_ctors_1733_; uint8_t v_isRec_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1739_; 
lean_dec_ref(v_e_1562_);
v_ctors_1733_ = lean_ctor_get(v_val_1725_, 4);
lean_inc(v_ctors_1733_);
v_isRec_1734_ = lean_ctor_get_uint8(v_val_1725_, sizeof(void*)*6);
lean_dec(v_val_1725_);
v___x_1735_ = l_List_lengthTR___redArg(v_ctors_1733_);
lean_dec(v_ctors_1733_);
v___x_1736_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*1, v_isRec_1734_);
v___x_1737_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*1 + 1, v___x_1737_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1736_);
v___x_1739_ = v___x_1729_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1736_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_val_1725_);
lean_dec(v_a_1705_);
lean_dec_ref(v_e_1562_);
v_a_1742_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1726_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1726_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
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
uint8_t v___x_1750_; 
lean_dec(v_a_1724_);
v___x_1750_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___y_1584_ = v___x_1750_;
v___y_1585_ = v___y_1692_;
v___y_1586_ = v___y_1696_;
v___y_1587_ = v___y_1691_;
v___y_1588_ = v___y_1699_;
v___y_1589_ = v___y_1697_;
v___y_1590_ = v___y_1695_;
v___y_1591_ = v___y_1690_;
v___y_1592_ = v___y_1694_;
v___y_1593_ = v___y_1698_;
v___y_1594_ = v___y_1693_;
goto v___jp_1583_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_a_1705_);
lean_dec_ref(v_e_1562_);
v_a_1751_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1723_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1723_);
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
uint8_t v___x_1759_; 
lean_dec_ref(v___x_1721_);
v___x_1759_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___y_1584_ = v___x_1759_;
v___y_1585_ = v___y_1692_;
v___y_1586_ = v___y_1696_;
v___y_1587_ = v___y_1691_;
v___y_1588_ = v___y_1699_;
v___y_1589_ = v___y_1697_;
v___y_1590_ = v___y_1695_;
v___y_1591_ = v___y_1690_;
v___y_1592_ = v___y_1694_;
v___y_1593_ = v___y_1698_;
v___y_1594_ = v___y_1693_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_dec(v_a_1705_);
lean_dec_ref(v_e_1562_);
v___x_1760_ = lean_box(0);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1760_);
v___x_1762_ = v___x_1707_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_e_1562_);
v_a_1765_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1704_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1704_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_toCold_1773_; lean_object* v_options_1774_; uint8_t v_hasTrace_1775_; 
v_toCold_1773_ = lean_ctor_get(v___y_1698_, 0);
v_options_1774_ = lean_ctor_get(v_toCold_1773_, 2);
v_hasTrace_1775_ = lean_ctor_get_uint8(v_options_1774_, sizeof(void*)*1);
if (v_hasTrace_1775_ == 0)
{
lean_dec_ref(v_e_1562_);
goto v___jp_1574_;
}
else
{
lean_object* v_inheritedTraceOptions_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_inheritedTraceOptions_1776_ = lean_ctor_get(v_toCold_1773_, 11);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1778_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1776_, v_options_1774_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v_e_1562_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Meta_Grind_updateLastTag(v___y_1692_, v___y_1696_, v___y_1691_, v___y_1699_, v___y_1697_, v___y_1695_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec_ref_known(v___x_1780_, 1);
v___x_1781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1782_ = l_Lean_MessageData_ofExpr(v_e_1562_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1777_, v___x_1783_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref_known(v___x_1784_, 1);
goto v___jp_1574_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
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
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_e_1562_);
v_a_1793_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1780_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1780_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_e_1562_);
v_a_1801_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1701_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1701_);
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
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = l_Lean_Expr_getAppNumArgs(v_e_1562_);
v___x_1811_ = lean_nat_sub(v___x_1810_, v___x_1809_);
lean_dec(v___x_1810_);
v___x_1812_ = lean_nat_sub(v___x_1811_, v___x_1809_);
lean_dec(v___x_1811_);
v___x_1813_ = l_Lean_Expr_getRevArg_x21(v_e_1562_, v___x_1812_);
lean_dec_ref(v_e_1562_);
v___x_1814_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1813_, v___y_1692_, v___y_1697_, v___y_1690_, v___y_1694_, v___y_1698_, v___y_1693_);
return v___x_1814_;
}
}
v___jp_1815_:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Grind_isIte(v_e_1562_);
if (v___x_1826_ == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Lean_Meta_Grind_isDIte(v_e_1562_);
v___y_1690_ = v___y_1822_;
v___y_1691_ = v___y_1818_;
v___y_1692_ = v___y_1816_;
v___y_1693_ = v___y_1825_;
v___y_1694_ = v___y_1823_;
v___y_1695_ = v___y_1821_;
v___y_1696_ = v___y_1817_;
v___y_1697_ = v___y_1820_;
v___y_1698_ = v___y_1824_;
v___y_1699_ = v___y_1819_;
v___y_1700_ = v___x_1827_;
goto v___jp_1689_;
}
else
{
v___y_1690_ = v___y_1822_;
v___y_1691_ = v___y_1818_;
v___y_1692_ = v___y_1816_;
v___y_1693_ = v___y_1825_;
v___y_1694_ = v___y_1823_;
v___y_1695_ = v___y_1821_;
v___y_1696_ = v___y_1817_;
v___y_1697_ = v___y_1820_;
v___y_1698_ = v___y_1824_;
v___y_1699_ = v___y_1819_;
v___y_1700_ = v___x_1826_;
goto v___jp_1689_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1562_ = stack[0].m_obj;
lean_object* v_a_1563_ = stack[1].m_obj;
lean_object* v_a_1564_ = stack[2].m_obj;
lean_object* v_a_1565_ = stack[3].m_obj;
lean_object* v_a_1566_ = stack[4].m_obj;
lean_object* v_a_1567_ = stack[5].m_obj;
lean_object* v_a_1568_ = stack[6].m_obj;
lean_object* v_a_1569_ = stack[7].m_obj;
lean_object* v_a_1570_ = stack[8].m_obj;
lean_object* v_a_1571_ = stack[9].m_obj;
lean_object* v_a_1572_ = stack[10].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec(v_a_1868_);
return v_res_1879_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1880_, v_msg_1881_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1880_ = stack[0].m_obj;
lean_object* v_msg_1881_ = stack[1].m_obj;
lean_object* v___y_1882_ = stack[2].m_obj;
lean_object* v___y_1883_ = stack[3].m_obj;
lean_object* v___y_1884_ = stack[4].m_obj;
lean_object* v___y_1885_ = stack[5].m_obj;
lean_object* v___y_1886_ = stack[6].m_obj;
lean_object* v___y_1887_ = stack[7].m_obj;
lean_object* v___y_1888_ = stack[8].m_obj;
lean_object* v___y_1889_ = stack[9].m_obj;
lean_object* v___y_1890_ = stack[10].m_obj;
lean_object* v___y_1891_ = stack[11].m_obj;
lean_object* v_res_1894_;
v_res_1894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1880_, v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
stack->m_obj
 = v_res_1894_;
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
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1909_, lean_object* v_constName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1910_ = stack[1].m_obj;
lean_object* v___y_1911_ = stack[2].m_obj;
lean_object* v___y_1912_ = stack[3].m_obj;
lean_object* v___y_1913_ = stack[4].m_obj;
lean_object* v___y_1914_ = stack[5].m_obj;
lean_object* v___y_1915_ = stack[6].m_obj;
lean_object* v___y_1916_ = stack[7].m_obj;
lean_object* v___y_1917_ = stack[8].m_obj;
lean_object* v___y_1918_ = stack[9].m_obj;
lean_object* v___y_1919_ = stack[10].m_obj;
lean_object* v___y_1920_ = stack[11].m_obj;
lean_object* v_res_1923_;
v_res_1923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_box(0), v_constName_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
stack->m_obj
 = v_res_1923_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_constName_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1924_, v_constName_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
return v_res_1937_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1938_, lean_object* v_ref_1939_, lean_object* v_constName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1939_, v_constName_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1939_ = stack[1].m_obj;
lean_object* v_constName_1940_ = stack[2].m_obj;
lean_object* v___y_1941_ = stack[3].m_obj;
lean_object* v___y_1942_ = stack[4].m_obj;
lean_object* v___y_1943_ = stack[5].m_obj;
lean_object* v___y_1944_ = stack[6].m_obj;
lean_object* v___y_1945_ = stack[7].m_obj;
lean_object* v___y_1946_ = stack[8].m_obj;
lean_object* v___y_1947_ = stack[9].m_obj;
lean_object* v___y_1948_ = stack[10].m_obj;
lean_object* v___y_1949_ = stack[11].m_obj;
lean_object* v___y_1950_ = stack[12].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_box(0), v_ref_1939_, v_constName_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1954_, lean_object* v_ref_1955_, lean_object* v_constName_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1954_, v_ref_1955_, v_constName_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v_ref_1955_);
return v_res_1968_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1969_, lean_object* v_ref_1970_, lean_object* v_msg_1971_, lean_object* v_declHint_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1970_, v_msg_1971_, v_declHint_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1970_ = stack[1].m_obj;
lean_object* v_msg_1971_ = stack[2].m_obj;
lean_object* v_declHint_1972_ = stack[3].m_obj;
lean_object* v___y_1973_ = stack[4].m_obj;
lean_object* v___y_1974_ = stack[5].m_obj;
lean_object* v___y_1975_ = stack[6].m_obj;
lean_object* v___y_1976_ = stack[7].m_obj;
lean_object* v___y_1977_ = stack[8].m_obj;
lean_object* v___y_1978_ = stack[9].m_obj;
lean_object* v___y_1979_ = stack[10].m_obj;
lean_object* v___y_1980_ = stack[11].m_obj;
lean_object* v___y_1981_ = stack[12].m_obj;
lean_object* v___y_1982_ = stack[13].m_obj;
lean_object* v_res_1985_;
v_res_1985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_ref_1970_, v_msg_1971_, v_declHint_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
stack->m_obj
 = v_res_1985_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_ref_1987_, lean_object* v_msg_1988_, lean_object* v_declHint_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1986_, v_ref_1987_, v_msg_1988_, v_declHint_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v_ref_1987_);
return v_res_2001_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_2002_, lean_object* v_declHint_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2002_, v_declHint_2003_, v___y_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2002_ = stack[0].m_obj;
lean_object* v_declHint_2003_ = stack[1].m_obj;
lean_object* v___y_2004_ = stack[2].m_obj;
lean_object* v___y_2005_ = stack[3].m_obj;
lean_object* v___y_2006_ = stack[4].m_obj;
lean_object* v___y_2007_ = stack[5].m_obj;
lean_object* v___y_2008_ = stack[6].m_obj;
lean_object* v___y_2009_ = stack[7].m_obj;
lean_object* v___y_2010_ = stack[8].m_obj;
lean_object* v___y_2011_ = stack[9].m_obj;
lean_object* v___y_2012_ = stack[10].m_obj;
lean_object* v___y_2013_ = stack[11].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2002_, v_declHint_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_2017_, lean_object* v_declHint_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2017_, v_declHint_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec(v___y_2019_);
return v_res_2030_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2031_, lean_object* v_ref_2032_, lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2032_, v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2032_ = stack[1].m_obj;
lean_object* v_msg_2033_ = stack[2].m_obj;
lean_object* v___y_2034_ = stack[3].m_obj;
lean_object* v___y_2035_ = stack[4].m_obj;
lean_object* v___y_2036_ = stack[5].m_obj;
lean_object* v___y_2037_ = stack[6].m_obj;
lean_object* v___y_2038_ = stack[7].m_obj;
lean_object* v___y_2039_ = stack[8].m_obj;
lean_object* v___y_2040_ = stack[9].m_obj;
lean_object* v___y_2041_ = stack[10].m_obj;
lean_object* v___y_2042_ = stack[11].m_obj;
lean_object* v___y_2043_ = stack[12].m_obj;
lean_object* v_res_2046_;
v_res_2046_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_box(0), v_ref_2032_, v_msg_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
stack->m_obj
 = v_res_2046_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_ref_2048_, lean_object* v_msg_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2047_, v_ref_2048_, v_msg_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec(v_ref_2048_);
return v_res_2061_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2062_, lean_object* v_msg_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2063_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2063_ = stack[1].m_obj;
lean_object* v___y_2064_ = stack[2].m_obj;
lean_object* v___y_2065_ = stack[3].m_obj;
lean_object* v___y_2066_ = stack[4].m_obj;
lean_object* v___y_2067_ = stack[5].m_obj;
lean_object* v___y_2068_ = stack[6].m_obj;
lean_object* v___y_2069_ = stack[7].m_obj;
lean_object* v___y_2070_ = stack[8].m_obj;
lean_object* v___y_2071_ = stack[9].m_obj;
lean_object* v___y_2072_ = stack[10].m_obj;
lean_object* v___y_2073_ = stack[11].m_obj;
lean_object* v_res_2076_;
v_res_2076_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_box(0), v_msg_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
stack->m_obj
 = v_res_2076_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_msg_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2077_, v_msg_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec(v___y_2079_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2091_, lean_object* v_x_2092_){
_start:
{
if (lean_obj_tag(v_x_2092_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_box(0);
return v___x_2093_;
}
else
{
lean_object* v_key_2094_; lean_object* v_value_2095_; lean_object* v_tail_2096_; uint8_t v___y_2098_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v_fst_2103_; lean_object* v_snd_2104_; uint8_t v___x_2105_; 
v_key_2094_ = lean_ctor_get(v_x_2092_, 0);
v_value_2095_ = lean_ctor_get(v_x_2092_, 1);
v_tail_2096_ = lean_ctor_get(v_x_2092_, 2);
v_fst_2101_ = lean_ctor_get(v_key_2094_, 0);
v_snd_2102_ = lean_ctor_get(v_key_2094_, 1);
v_fst_2103_ = lean_ctor_get(v_a_2091_, 0);
v_snd_2104_ = lean_ctor_get(v_a_2091_, 1);
v___x_2105_ = lean_expr_eqv(v_fst_2101_, v_fst_2103_);
if (v___x_2105_ == 0)
{
v___y_2098_ = v___x_2105_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_expr_eqv(v_snd_2102_, v_snd_2104_);
v___y_2098_ = v___x_2106_;
goto v___jp_2097_;
}
v___jp_2097_:
{
if (v___y_2098_ == 0)
{
v_x_2092_ = v_tail_2096_;
goto _start;
}
else
{
lean_object* v___x_2100_; 
lean_inc(v_value_2095_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_value_2095_);
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2107_, v_x_2108_);
lean_dec(v_x_2108_);
lean_dec_ref(v_a_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_buckets_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; uint64_t v___x_2116_; uint64_t v___x_2117_; uint64_t v___x_2118_; uint64_t v___x_2119_; uint64_t v___x_2120_; uint64_t v_fold_2121_; uint64_t v___x_2122_; uint64_t v___x_2123_; uint64_t v___x_2124_; size_t v___x_2125_; size_t v___x_2126_; size_t v___x_2127_; size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_buckets_2112_ = lean_ctor_get(v_m_2110_, 1);
v_fst_2113_ = lean_ctor_get(v_a_2111_, 0);
v_snd_2114_ = lean_ctor_get(v_a_2111_, 1);
v___x_2115_ = lean_array_get_size(v_buckets_2112_);
v___x_2116_ = l_Lean_Expr_hash(v_fst_2113_);
v___x_2117_ = l_Lean_Expr_hash(v_snd_2114_);
v___x_2118_ = lean_uint64_mix_hash(v___x_2116_, v___x_2117_);
v___x_2119_ = 32ULL;
v___x_2120_ = lean_uint64_shift_right(v___x_2118_, v___x_2119_);
v_fold_2121_ = lean_uint64_xor(v___x_2118_, v___x_2120_);
v___x_2122_ = 16ULL;
v___x_2123_ = lean_uint64_shift_right(v_fold_2121_, v___x_2122_);
v___x_2124_ = lean_uint64_xor(v_fold_2121_, v___x_2123_);
v___x_2125_ = lean_uint64_to_usize(v___x_2124_);
v___x_2126_ = lean_usize_of_nat(v___x_2115_);
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_sub(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_usize_land(v___x_2125_, v___x_2128_);
v___x_2130_ = lean_array_uget_borrowed(v_buckets_2112_, v___x_2129_);
v___x_2131_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2111_, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2132_, v_a_2133_);
lean_dec_ref(v_a_2133_);
lean_dec_ref(v_m_2132_);
return v_res_2134_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2135_, uint8_t v___x_2136_, lean_object* v_fst_2137_, lean_object* v_snd_2138_, lean_object* v___x_2139_, lean_object* v_____r_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2152_ = lean_unsigned_to_nat(2u);
v___x_2153_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1, v_a_2135_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*1 + 1, v___x_2136_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_fst_2137_);
lean_ctor_set(v___x_2155_, 1, v_snd_2138_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2139_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2135_ = stack[0].m_num;
uint8_t v___x_2136_ = stack[1].m_num;
lean_object* v_fst_2137_ = stack[2].m_obj;
lean_object* v_snd_2138_ = stack[3].m_obj;
lean_object* v___x_2139_ = stack[4].m_obj;
lean_object* v_____r_2140_ = stack[5].m_obj;
lean_object* v___y_2141_ = stack[6].m_obj;
lean_object* v___y_2142_ = stack[7].m_obj;
lean_object* v___y_2143_ = stack[8].m_obj;
lean_object* v___y_2144_ = stack[9].m_obj;
lean_object* v___y_2145_ = stack[10].m_obj;
lean_object* v___y_2146_ = stack[11].m_obj;
lean_object* v___y_2147_ = stack[12].m_obj;
lean_object* v___y_2148_ = stack[13].m_obj;
lean_object* v___y_2149_ = stack[14].m_obj;
lean_object* v___y_2150_ = stack[15].m_obj;
lean_object* v_res_2160_;
v_res_2160_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_2135_, v___x_2136_, v_fst_2137_, v_snd_2138_, v___x_2139_, v_____r_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
stack->m_obj
 = v_res_2160_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2161_ = _args[0];
lean_object* v___x_2162_ = _args[1];
lean_object* v_fst_2163_ = _args[2];
lean_object* v_snd_2164_ = _args[3];
lean_object* v___x_2165_ = _args[4];
lean_object* v_____r_2166_ = _args[5];
lean_object* v___y_2167_ = _args[6];
lean_object* v___y_2168_ = _args[7];
lean_object* v___y_2169_ = _args[8];
lean_object* v___y_2170_ = _args[9];
lean_object* v___y_2171_ = _args[10];
lean_object* v___y_2172_ = _args[11];
lean_object* v___y_2173_ = _args[12];
lean_object* v___y_2174_ = _args[13];
lean_object* v___y_2175_ = _args[14];
lean_object* v___y_2176_ = _args[15];
lean_object* v___y_2177_ = _args[16];
_start:
{
uint8_t v_a_33800__boxed_2178_; uint8_t v___x_33801__boxed_2179_; lean_object* v_res_2180_; 
v_a_33800__boxed_2178_ = lean_unbox(v_a_2161_);
v___x_33801__boxed_2179_ = lean_unbox(v___x_2162_);
v_res_2180_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_33800__boxed_2178_, v___x_33801__boxed_2179_, v_fst_2163_, v_snd_2164_, v___x_2165_, v_____r_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
return v_res_2180_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2181_, lean_object* v_snd_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v_____r_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2197_ = l_Lean_Expr_appFn_x21(v_fst_2181_);
v___x_2198_ = l_Lean_Expr_appFn_x21(v_snd_2182_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2183_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2184_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2181_ = stack[0].m_obj;
lean_object* v_snd_2182_ = stack[1].m_obj;
lean_object* v___x_2183_ = stack[2].m_obj;
lean_object* v___x_2184_ = stack[3].m_obj;
lean_object* v_____r_2185_ = stack[4].m_obj;
lean_object* v___y_2186_ = stack[5].m_obj;
lean_object* v___y_2187_ = stack[6].m_obj;
lean_object* v___y_2188_ = stack[7].m_obj;
lean_object* v___y_2189_ = stack[8].m_obj;
lean_object* v___y_2190_ = stack[9].m_obj;
lean_object* v___y_2191_ = stack[10].m_obj;
lean_object* v___y_2192_ = stack[11].m_obj;
lean_object* v___y_2193_ = stack[12].m_obj;
lean_object* v___y_2194_ = stack[13].m_obj;
lean_object* v___y_2195_ = stack[14].m_obj;
lean_object* v_res_2204_;
v_res_2204_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2181_, v_snd_2182_, v___x_2183_, v___x_2184_, v_____r_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
stack->m_obj
 = v_res_2204_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2205_, lean_object* v_snd_2206_, lean_object* v___x_2207_, lean_object* v___x_2208_, lean_object* v_____r_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2205_, v_snd_2206_, v___x_2207_, v___x_2208_, v_____r_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec(v_snd_2206_);
lean_dec(v_fst_2205_);
return v_res_2221_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___f_2223_; 
v___x_2222_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2223_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2223_, 0, v___x_2222_);
return v___f_2223_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2229_ = l_Lean_Name_append(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2248_, lean_object* v___y_2249_, lean_object* v_eq_2250_, lean_object* v_a_2251_, lean_object* v_b_2252_, lean_object* v_a_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___y_2266_; lean_object* v_snd_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2409_; 
v_snd_2286_ = lean_ctor_get(v_a_2253_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_a_2253_, 0);
lean_dec(v_unused_2410_);
v___x_2288_ = v_a_2253_;
v_isShared_2289_ = v_isSharedCheck_2409_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_snd_2286_);
lean_dec(v_a_2253_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2409_;
goto v_resetjp_2287_;
}
v___jp_2265_:
{
if (lean_obj_tag(v___y_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2277_; 
v_a_2267_ = lean_ctor_get(v___y_2266_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___y_2266_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2269_ = v___y_2266_;
v_isShared_2270_ = v_isSharedCheck_2277_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___y_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2277_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
if (lean_obj_tag(v_a_2267_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; 
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2271_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_a_2267_, 1);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v_a_2271_);
v___x_2273_ = v___x_2269_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
else
{
lean_object* v_a_2275_; 
lean_del_object(v___x_2269_);
v_a_2275_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v_a_2267_, 1);
v_a_2253_ = v_a_2275_;
goto _start;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2278_ = lean_ctor_get(v___y_2266_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___y_2266_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___y_2266_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___y_2266_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v_resetjp_2287_:
{
lean_object* v_snd_2290_; lean_object* v_fst_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2408_; 
v_snd_2290_ = lean_ctor_get(v_snd_2286_, 1);
v_fst_2291_ = lean_ctor_get(v_snd_2286_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_snd_2286_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2293_ = v_snd_2286_;
v_isShared_2294_ = v_isSharedCheck_2408_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snd_2290_);
lean_inc(v_fst_2291_);
lean_dec(v_snd_2286_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2408_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_fst_2295_; lean_object* v_snd_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2407_; 
v_fst_2295_ = lean_ctor_get(v_snd_2290_, 0);
v_snd_2296_ = lean_ctor_get(v_snd_2290_, 1);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_snd_2290_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2298_ = v_snd_2290_;
v_isShared_2299_ = v_isSharedCheck_2407_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_snd_2296_);
lean_inc(v_fst_2295_);
lean_dec(v_snd_2290_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2407_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
uint8_t v___y_2301_; uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Expr_isApp(v_fst_2295_);
if (v___x_2315_ == 0)
{
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v___y_2301_ = v_a_2248_;
goto v___jp_2300_;
}
else
{
uint8_t v___x_2316_; 
v___x_2316_ = l_Lean_Expr_isApp(v_snd_2296_);
if (v___x_2316_ == 0)
{
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v___y_2301_ = v___x_2316_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___f_2323_; uint8_t v___x_2324_; 
lean_del_object(v___x_2298_);
lean_del_object(v___x_2293_);
lean_del_object(v___x_2288_);
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_sub(v_fst_2291_, v___x_2318_);
lean_dec(v_fst_2291_);
v___f_2323_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2249_);
lean_inc(v___x_2319_);
v___x_2324_ = l_List_elem___redArg(v___f_2323_, v___x_2319_, v___y_2249_);
if (v___x_2324_ == 0)
{
if (v___x_2316_ == 0)
{
goto v___jp_2320_;
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = l_Lean_Expr_appArg_x21(v_fst_2295_);
v___x_2326_ = l_Lean_Expr_appArg_x21(v_snd_2296_);
v___x_2327_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2325_, v___x_2326_, v___y_2254_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_unbox(v_a_2328_);
if (v___x_2329_ == 0)
{
lean_object* v_toCold_2330_; lean_object* v_options_2331_; lean_object* v_inheritedTraceOptions_2332_; uint8_t v_hasTrace_2333_; 
v_toCold_2330_ = lean_ctor_get(v___y_2262_, 0);
v_options_2331_ = lean_ctor_get(v_toCold_2330_, 2);
v_inheritedTraceOptions_2332_ = lean_ctor_get(v_toCold_2330_, 11);
v_hasTrace_2333_ = lean_ctor_get_uint8(v_options_2331_, sizeof(void*)*1);
if (v_hasTrace_2333_ == 0)
{
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
goto v___jp_2334_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2338_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2339_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2332_, v_options_2331_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
goto v___jp_2334_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Meta_Grind_updateLastTag(v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; 
lean_dec_ref_known(v___x_2341_, 1);
v___x_2342_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2250_, v___y_2254_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2251_);
v___x_2345_ = l_Lean_MessageData_ofExpr(v_a_2251_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
lean_inc_ref(v_b_2252_);
v___x_2349_ = l_Lean_MessageData_ofExpr(v_b_2252_);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
lean_inc_ref(v_eq_2250_);
v___x_2353_ = l_Lean_MessageData_ofExpr(v_eq_2250_);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = l_Lean_MessageData_ofExpr(v___x_2325_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_MessageData_ofExpr(v___x_2326_);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2360_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
v___x_2363_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = l_Nat_reprFast(v_a_2343_);
v___x_2366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = l_Lean_MessageData_ofFormat(v___x_2366_);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2364_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2338_, v___x_2368_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
v___x_2372_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2371_, v___x_2316_, v_fst_2295_, v_snd_2296_, v___x_2319_, v_a_2370_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
v___y_2266_ = v___x_2372_;
goto v___jp_2265_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2328_);
lean_dec(v___x_2319_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2373_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2369_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2369_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
lean_dec(v___x_2319_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2381_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2342_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2342_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
lean_dec(v___x_2319_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2389_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2341_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2341_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
v___jp_2334_:
{
lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
v___x_2337_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2336_, v___x_2316_, v_fst_2295_, v_snd_2296_, v___x_2319_, v___x_2335_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
v___y_2266_ = v___x_2337_;
goto v___jp_2265_;
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
v___x_2397_ = lean_box(0);
v___x_2398_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2295_, v_snd_2296_, v___x_2319_, v___x_2317_, v___x_2397_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
v___y_2266_ = v___x_2398_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2325_);
lean_dec(v___x_2319_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
lean_dec_ref(v_b_2252_);
lean_dec_ref(v_a_2251_);
lean_dec_ref(v_eq_2250_);
lean_dec(v___y_2249_);
v_a_2399_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2327_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2327_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
else
{
goto v___jp_2320_;
}
v___jp_2320_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_box(0);
v___x_2322_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2295_, v_snd_2296_, v___x_2319_, v___x_2317_, v___x_2321_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
v___y_2266_ = v___x_2322_;
goto v___jp_2265_;
}
}
}
v___jp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2302_ = lean_unsigned_to_nat(2u);
v___x_2303_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*1, v___y_2301_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*1 + 1, v___y_2301_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
if (v_isShared_2299_ == 0)
{
v___x_2306_ = v___x_2298_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_snd_2296_);
v___x_2306_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2306_);
v___x_2308_ = v___x_2293_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2308_);
lean_ctor_set(v___x_2288_, 0, v___x_2304_);
v___x_2310_ = v___x_2288_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2248_ = stack[0].m_num;
lean_object* v___y_2249_ = stack[1].m_obj;
lean_object* v_eq_2250_ = stack[2].m_obj;
lean_object* v_a_2251_ = stack[3].m_obj;
lean_object* v_b_2252_ = stack[4].m_obj;
lean_object* v_a_2253_ = stack[5].m_obj;
lean_object* v___y_2254_ = stack[6].m_obj;
lean_object* v___y_2255_ = stack[7].m_obj;
lean_object* v___y_2256_ = stack[8].m_obj;
lean_object* v___y_2257_ = stack[9].m_obj;
lean_object* v___y_2258_ = stack[10].m_obj;
lean_object* v___y_2259_ = stack[11].m_obj;
lean_object* v___y_2260_ = stack[12].m_obj;
lean_object* v___y_2261_ = stack[13].m_obj;
lean_object* v___y_2262_ = stack[14].m_obj;
lean_object* v___y_2263_ = stack[15].m_obj;
lean_object* v_res_2411_;
v_res_2411_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2248_, v___y_2249_, v_eq_2250_, v_a_2251_, v_b_2252_, v_a_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_a_2412_ = _args[0];
lean_object* v___y_2413_ = _args[1];
lean_object* v_eq_2414_ = _args[2];
lean_object* v_a_2415_ = _args[3];
lean_object* v_b_2416_ = _args[4];
lean_object* v_a_2417_ = _args[5];
lean_object* v___y_2418_ = _args[6];
lean_object* v___y_2419_ = _args[7];
lean_object* v___y_2420_ = _args[8];
lean_object* v___y_2421_ = _args[9];
lean_object* v___y_2422_ = _args[10];
lean_object* v___y_2423_ = _args[11];
lean_object* v___y_2424_ = _args[12];
lean_object* v___y_2425_ = _args[13];
lean_object* v___y_2426_ = _args[14];
lean_object* v___y_2427_ = _args[15];
lean_object* v___y_2428_ = _args[16];
_start:
{
uint8_t v_a_34047__boxed_2429_; lean_object* v_res_2430_; 
v_a_34047__boxed_2429_ = lean_unbox(v_a_2412_);
v_res_2430_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34047__boxed_2429_, v___y_2413_, v_eq_2414_, v_a_2415_, v_b_2416_, v_a_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
return v_res_2430_;
}
}
lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2431_, lean_object* v_b_2432_, lean_object* v_eq_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
uint8_t v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2478_; lean_object* v___x_2514_; 
lean_inc_ref(v_eq_2433_);
v___x_2514_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2433_, v_a_2434_, v_a_2438_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint8_t v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v___x_2516_ = lean_unbox(v_a_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref_known(v___x_2514_, 1);
lean_inc_ref(v_eq_2433_);
v___x_2517_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2433_, v_a_2434_, v_a_2438_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
v___y_2478_ = v___x_2517_;
goto v___jp_2477_;
}
else
{
v___y_2478_ = v___x_2514_;
goto v___jp_2477_;
}
}
else
{
v___y_2478_ = v___x_2514_;
goto v___jp_2477_;
}
v___jp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2448_ = l_Lean_Expr_getAppNumArgs(v_a_2431_);
v___x_2449_ = lean_box(0);
lean_inc_ref(v_b_2432_);
lean_inc_ref(v_a_2431_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_a_2431_);
lean_ctor_set(v___x_2450_, 1, v_b_2432_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2448_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2449_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2446_, v___y_2447_, v_eq_2433_, v_a_2431_, v_b_2432_, v___x_2452_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2468_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2468_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2468_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_fst_2458_; 
v_fst_2458_ = lean_ctor_get(v_a_2454_, 0);
lean_inc(v_fst_2458_);
lean_dec(v_a_2454_);
if (lean_obj_tag(v_fst_2458_) == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2459_ = lean_unsigned_to_nat(2u);
v___x_2460_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*1, v___y_2446_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*1 + 1, v___y_2446_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2460_);
v___x_2462_ = v___x_2456_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
else
{
lean_object* v_val_2464_; lean_object* v___x_2466_; 
v_val_2464_ = lean_ctor_get(v_fst_2458_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v_fst_2458_, 1);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_val_2464_);
v___x_2466_ = v___x_2456_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_val_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2453_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2453_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
v___jp_2477_:
{
if (lean_obj_tag(v___y_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2505_; 
v_a_2479_ = lean_ctor_get(v___y_2478_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___y_2478_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2481_ = v___y_2478_;
v_isShared_2482_ = v_isSharedCheck_2505_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___y_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2505_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_unbox(v_a_2479_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v_toGoalState_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2499_; 
lean_del_object(v___x_2481_);
v___x_2484_ = lean_st_ref_get(v_a_2434_);
v_toGoalState_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2484_, 1);
lean_dec(v_unused_2500_);
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_toGoalState_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_split_2489_; lean_object* v_argPosMap_2490_; lean_object* v___x_2492_; 
v_split_2489_ = lean_ctor_get(v_toGoalState_2485_, 14);
lean_inc_ref(v_split_2489_);
lean_dec_ref(v_toGoalState_2485_);
v_argPosMap_2490_ = lean_ctor_get(v_split_2489_, 6);
lean_inc_ref(v_argPosMap_2490_);
lean_dec_ref(v_split_2489_);
lean_inc_ref(v_b_2432_);
lean_inc_ref(v_a_2431_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v_b_2432_);
lean_ctor_set(v___x_2487_, 0, v_a_2431_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2431_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_b_2432_);
v___x_2492_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2490_, v___x_2492_);
lean_dec_ref(v___x_2492_);
lean_dec_ref(v_argPosMap_2490_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_unbox(v_a_2479_);
lean_dec(v_a_2479_);
v___y_2446_ = v___x_2495_;
v___y_2447_ = v___x_2494_;
goto v___jp_2445_;
}
else
{
lean_object* v_val_2496_; uint8_t v___x_2497_; 
v_val_2496_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2497_ = lean_unbox(v_a_2479_);
lean_dec(v_a_2479_);
v___y_2446_ = v___x_2497_;
v___y_2447_ = v_val_2496_;
goto v___jp_2445_;
}
}
}
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_dec(v_a_2479_);
lean_dec_ref(v_eq_2433_);
lean_dec_ref(v_b_2432_);
lean_dec_ref(v_a_2431_);
v___x_2501_ = lean_box(0);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2501_);
v___x_2503_ = v___x_2481_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_eq_2433_);
lean_dec_ref(v_b_2432_);
lean_dec_ref(v_a_2431_);
v_a_2506_ = lean_ctor_get(v___y_2478_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___y_2478_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___y_2478_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___y_2478_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_checkSplitInfoArgStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2431_ = stack[0].m_obj;
lean_object* v_b_2432_ = stack[1].m_obj;
lean_object* v_eq_2433_ = stack[2].m_obj;
lean_object* v_a_2434_ = stack[3].m_obj;
lean_object* v_a_2435_ = stack[4].m_obj;
lean_object* v_a_2436_ = stack[5].m_obj;
lean_object* v_a_2437_ = stack[6].m_obj;
lean_object* v_a_2438_ = stack[7].m_obj;
lean_object* v_a_2439_ = stack[8].m_obj;
lean_object* v_a_2440_ = stack[9].m_obj;
lean_object* v_a_2441_ = stack[10].m_obj;
lean_object* v_a_2442_ = stack[11].m_obj;
lean_object* v_a_2443_ = stack[12].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2431_, v_b_2432_, v_eq_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2519_, lean_object* v_b_2520_, lean_object* v_eq_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2519_, v_b_2520_, v_eq_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec(v_a_2522_);
return v_res_2533_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2534_, lean_object* v___y_2535_, lean_object* v_eq_2536_, lean_object* v_a_2537_, lean_object* v_b_2538_, lean_object* v_inst_2539_, lean_object* v_a_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2534_, v___y_2535_, v_eq_2536_, v_a_2537_, v_b_2538_, v_a_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2534_ = stack[0].m_num;
lean_object* v___y_2535_ = stack[1].m_obj;
lean_object* v_eq_2536_ = stack[2].m_obj;
lean_object* v_a_2537_ = stack[3].m_obj;
lean_object* v_b_2538_ = stack[4].m_obj;
lean_object* v_a_2540_ = stack[6].m_obj;
lean_object* v___y_2541_ = stack[7].m_obj;
lean_object* v___y_2542_ = stack[8].m_obj;
lean_object* v___y_2543_ = stack[9].m_obj;
lean_object* v___y_2544_ = stack[10].m_obj;
lean_object* v___y_2545_ = stack[11].m_obj;
lean_object* v___y_2546_ = stack[12].m_obj;
lean_object* v___y_2547_ = stack[13].m_obj;
lean_object* v___y_2548_ = stack[14].m_obj;
lean_object* v___y_2549_ = stack[15].m_obj;
lean_object* v___y_2550_ = stack[16].m_obj;
lean_object* v_res_2553_;
v_res_2553_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_2534_, v___y_2535_, v_eq_2536_, v_a_2537_, v_b_2538_, lean_box(0), v_a_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2554_ = _args[0];
lean_object* v___y_2555_ = _args[1];
lean_object* v_eq_2556_ = _args[2];
lean_object* v_a_2557_ = _args[3];
lean_object* v_b_2558_ = _args[4];
lean_object* v_inst_2559_ = _args[5];
lean_object* v_a_2560_ = _args[6];
lean_object* v___y_2561_ = _args[7];
lean_object* v___y_2562_ = _args[8];
lean_object* v___y_2563_ = _args[9];
lean_object* v___y_2564_ = _args[10];
lean_object* v___y_2565_ = _args[11];
lean_object* v___y_2566_ = _args[12];
lean_object* v___y_2567_ = _args[13];
lean_object* v___y_2568_ = _args[14];
lean_object* v___y_2569_ = _args[15];
lean_object* v___y_2570_ = _args[16];
lean_object* v___y_2571_ = _args[17];
_start:
{
uint8_t v_a_34789__boxed_2572_; lean_object* v_res_2573_; 
v_a_34789__boxed_2572_ = lean_unbox(v_a_2554_);
v_res_2573_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34789__boxed_2572_, v___y_2555_, v_eq_2556_, v_a_2557_, v_b_2558_, v_inst_2559_, v_a_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec(v___y_2561_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2574_, lean_object* v_m_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2575_, v_a_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2578_, lean_object* v_m_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2578_, v_m_2579_, v_a_2580_);
lean_dec_ref(v_a_2580_);
lean_dec_ref(v_m_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2582_, lean_object* v_a_2583_, lean_object* v_x_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2583_, v_x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2586_, lean_object* v_a_2587_, lean_object* v_x_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2586_, v_a_2587_, v_x_2588_);
lean_dec(v_x_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2589_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v___y_2599_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___x_2624_; 
lean_inc_ref(v_imp_2590_);
v___x_2624_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; uint8_t v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = lean_unbox(v_a_2625_);
lean_dec(v_a_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2641_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_unbox(v_a_2628_);
lean_dec(v_a_2628_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_box(1);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_box(0);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2637_);
v___x_2639_ = v___x_2630_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
v_a_2642_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2627_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2627_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_binderType_2650_; lean_object* v_body_2651_; lean_object* v___y_2653_; lean_object* v___x_2681_; 
v_binderType_2650_ = lean_ctor_get(v_imp_2590_, 1);
lean_inc_ref_n(v_binderType_2650_, 2);
v_body_2651_ = lean_ctor_get(v_imp_2590_, 2);
lean_inc_ref(v_body_2651_);
lean_dec_ref(v_imp_2590_);
v___x_2681_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2650_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; uint8_t v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v___x_2683_ = lean_unbox(v_a_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref_known(v___x_2681_, 1);
v___x_2684_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2650_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
v___y_2653_ = v___x_2684_;
goto v___jp_2652_;
}
else
{
lean_dec_ref(v_binderType_2650_);
v___y_2653_ = v___x_2681_;
goto v___jp_2652_;
}
}
else
{
lean_dec_ref(v_binderType_2650_);
v___y_2653_ = v___x_2681_;
goto v___jp_2652_;
}
v___jp_2652_:
{
if (lean_obj_tag(v___y_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2672_; 
v_a_2654_ = lean_ctor_get(v___y_2653_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___y_2653_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2656_ = v___y_2653_;
v_isShared_2657_ = v_isSharedCheck_2672_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___y_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2672_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
uint8_t v___x_2658_; 
v___x_2658_ = lean_unbox(v_a_2654_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
lean_del_object(v___x_2656_);
v___x_2659_ = l_Lean_Expr_hasLooseBVars(v_body_2651_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_inc_ref(v_body_2651_);
v___x_2660_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2651_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; uint8_t v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v___x_2662_ = lean_unbox(v_a_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
lean_dec_ref_known(v___x_2660_, 1);
v___x_2663_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2651_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
v___x_2664_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
v___y_2604_ = v___x_2664_;
v___y_2605_ = v___x_2663_;
goto v___jp_2603_;
}
else
{
uint8_t v___x_2665_; 
lean_dec_ref(v_body_2651_);
v___x_2665_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
v___y_2604_ = v___x_2665_;
v___y_2605_ = v___x_2660_;
goto v___jp_2603_;
}
}
else
{
uint8_t v___x_2666_; 
lean_dec_ref(v_body_2651_);
v___x_2666_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
v___y_2604_ = v___x_2666_;
v___y_2605_ = v___x_2660_;
goto v___jp_2603_;
}
}
else
{
uint8_t v___x_2667_; 
lean_dec_ref(v_body_2651_);
v___x_2667_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
v___y_2599_ = v___x_2667_;
goto v___jp_2598_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_a_2654_);
lean_dec_ref(v_body_2651_);
v___x_2668_ = lean_box(0);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2668_);
v___x_2670_ = v___x_2656_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
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
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_body_2651_);
v_a_2673_ = lean_ctor_get(v___y_2653_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___y_2653_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___y_2653_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___y_2653_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v_imp_2590_);
v_a_2685_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2624_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2624_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_unsigned_to_nat(2u);
v___x_2601_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*1, v___y_2599_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*1 + 1, v___y_2599_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
v___jp_2603_:
{
if (lean_obj_tag(v___y_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2615_; 
v_a_2606_ = lean_ctor_get(v___y_2605_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___y_2605_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2608_ = v___y_2605_;
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___y_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2615_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2610_ == 0)
{
lean_del_object(v___x_2608_);
v___y_2599_ = v___y_2604_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(0);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2611_);
v___x_2613_ = v___x_2608_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
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
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v_a_2616_ = lean_ctor_get(v___y_2605_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___y_2605_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___y_2605_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___y_2605_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_imp_2590_ = stack[0].m_obj;
lean_object* v_a_2591_ = stack[1].m_obj;
lean_object* v_a_2592_ = stack[2].m_obj;
lean_object* v_a_2593_ = stack[3].m_obj;
lean_object* v_a_2594_ = stack[4].m_obj;
lean_object* v_a_2595_ = stack[5].m_obj;
lean_object* v_a_2596_ = stack[6].m_obj;
lean_object* v_res_2693_;
v_res_2693_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
return v_res_2702_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2703_, lean_object* v_h_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2703_, v_a_2705_, v_a_2709_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_imp_2703_ = stack[0].m_obj;
lean_object* v_a_2705_ = stack[2].m_obj;
lean_object* v_a_2706_ = stack[3].m_obj;
lean_object* v_a_2707_ = stack[4].m_obj;
lean_object* v_a_2708_ = stack[5].m_obj;
lean_object* v_a_2709_ = stack[6].m_obj;
lean_object* v_a_2710_ = stack[7].m_obj;
lean_object* v_a_2711_ = stack[8].m_obj;
lean_object* v_a_2712_ = stack[9].m_obj;
lean_object* v_a_2713_ = stack[10].m_obj;
lean_object* v_a_2714_ = stack[11].m_obj;
lean_object* v_res_2717_;
v_res_2717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2703_, lean_box(0), v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
stack->m_obj
 = v_res_2717_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2718_, lean_object* v_h_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2718_, v_h_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec(v_a_2720_);
return v_res_2731_;
}
}
lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
switch(lean_obj_tag(v_s_2732_))
{
case 0:
{
lean_object* v_e_2744_; lean_object* v___x_2745_; 
v_e_2744_ = lean_ctor_get(v_s_2732_, 0);
lean_inc_ref(v_e_2744_);
lean_dec_ref_known(v_s_2732_, 2);
v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2744_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2745_;
}
case 1:
{
lean_object* v_e_2746_; lean_object* v___x_2747_; 
v_e_2746_ = lean_ctor_get(v_s_2732_, 0);
lean_inc_ref(v_e_2746_);
lean_dec_ref_known(v_s_2732_, 2);
v___x_2747_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2746_, v_a_2733_, v_a_2737_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2747_;
}
default: 
{
lean_object* v_a_2748_; lean_object* v_b_2749_; lean_object* v_eq_2750_; lean_object* v___x_2751_; 
v_a_2748_ = lean_ctor_get(v_s_2732_, 0);
lean_inc_ref(v_a_2748_);
v_b_2749_ = lean_ctor_get(v_s_2732_, 1);
lean_inc_ref(v_b_2749_);
v_eq_2750_ = lean_ctor_get(v_s_2732_, 3);
lean_inc_ref(v_eq_2750_);
lean_dec_ref_known(v_s_2732_, 5);
v___x_2751_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2748_, v_b_2749_, v_eq_2750_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2751_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_checkSplitStatus_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2732_ = stack[0].m_obj;
lean_object* v_a_2733_ = stack[1].m_obj;
lean_object* v_a_2734_ = stack[2].m_obj;
lean_object* v_a_2735_ = stack[3].m_obj;
lean_object* v_a_2736_ = stack[4].m_obj;
lean_object* v_a_2737_ = stack[5].m_obj;
lean_object* v_a_2738_ = stack[6].m_obj;
lean_object* v_a_2739_ = stack[7].m_obj;
lean_object* v_a_2740_ = stack[8].m_obj;
lean_object* v_a_2741_ = stack[9].m_obj;
lean_object* v_a_2742_ = stack[10].m_obj;
lean_object* v_res_2752_;
v_res_2752_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec(v_a_2754_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_obj_tag_nat(v_x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2768_);
lean_dec(v_x_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2770_, lean_object* v_k_2771_){
_start:
{
if (lean_obj_tag(v_t_2770_) == 0)
{
return v_k_2771_;
}
else
{
lean_object* v_c_2772_; lean_object* v_numCases_2773_; uint8_t v_isRec_2774_; uint8_t v_tryPostpone_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_c_2772_ = lean_ctor_get(v_t_2770_, 0);
lean_inc_ref(v_c_2772_);
v_numCases_2773_ = lean_ctor_get(v_t_2770_, 1);
lean_inc(v_numCases_2773_);
v_isRec_2774_ = lean_ctor_get_uint8(v_t_2770_, sizeof(void*)*2);
v_tryPostpone_2775_ = lean_ctor_get_uint8(v_t_2770_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2770_, 2);
v___x_2776_ = lean_box(v_isRec_2774_);
v___x_2777_ = lean_box(v_tryPostpone_2775_);
v___x_2778_ = lean_apply_4(v_k_2771_, v_c_2772_, v_numCases_2773_, v___x_2776_, v___x_2777_);
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2779_, lean_object* v_ctorIdx_2780_, lean_object* v_t_2781_, lean_object* v_h_2782_, lean_object* v_k_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2781_, v_k_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2785_, lean_object* v_ctorIdx_2786_, lean_object* v_t_2787_, lean_object* v_h_2788_, lean_object* v_k_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2785_, v_ctorIdx_2786_, v_t_2787_, v_h_2788_, v_k_2789_);
lean_dec(v_ctorIdx_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2791_, lean_object* v_none_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2791_, v_none_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2794_, lean_object* v_t_2795_, lean_object* v_h_2796_, lean_object* v_none_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2795_, v_none_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2799_, lean_object* v_some_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2799_, v_some_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2802_, lean_object* v_t_2803_, lean_object* v_h_2804_, lean_object* v_some_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2803_, v_some_2805_);
return v___x_2806_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2807_, lean_object* v_as_2808_, size_t v_i_2809_, size_t v_stop_2810_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = lean_usize_dec_eq(v_i_2809_, v_stop_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_array_uget_borrowed(v_as_2808_, v_i_2809_);
v___x_2813_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2812_, v_a_2807_);
if (v___x_2813_ == 0)
{
size_t v___x_2814_; size_t v___x_2815_; 
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2809_, v___x_2814_);
v_i_2809_ = v___x_2815_;
goto _start;
}
else
{
return v___x_2813_;
}
}
else
{
uint8_t v___x_2817_; 
v___x_2817_ = 0;
return v___x_2817_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_2807_ = stack[0].m_num;
lean_object* v_as_2808_ = stack[1].m_obj;
size_t v_i_2809_ = stack[2].m_num;
size_t v_stop_2810_ = stack[3].m_num;
uint8_t v_res_2818_;
v_res_2818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2807_, v_as_2808_, v_i_2809_, v_stop_2810_);
stack->m_num = v_res_2818_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2819_, lean_object* v_as_2820_, lean_object* v_i_2821_, lean_object* v_stop_2822_){
_start:
{
uint64_t v_a_2507__boxed_2823_; size_t v_i_boxed_2824_; size_t v_stop_boxed_2825_; uint8_t v_res_2826_; lean_object* v_r_2827_; 
v_a_2507__boxed_2823_ = lean_unbox_uint64(v_a_2819_);
lean_dec_ref(v_a_2819_);
v_i_boxed_2824_ = lean_unbox_usize(v_i_2821_);
lean_dec(v_i_2821_);
v_stop_boxed_2825_ = lean_unbox_usize(v_stop_2822_);
lean_dec(v_stop_2822_);
v_res_2826_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2823_, v_as_2820_, v_i_boxed_2824_, v_stop_boxed_2825_);
lean_dec_ref(v_as_2820_);
v_r_2827_ = lean_box(v_res_2826_);
return v_r_2827_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2830_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2883_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2883_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2883_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (lean_obj_tag(v_a_2840_) == 1)
{
lean_object* v_val_2844_; lean_object* v___x_2845_; 
lean_del_object(v___x_2842_);
v_val_2844_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v_a_2840_, 1);
v___x_2845_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2869_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2869_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2869_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v_val_2844_);
v___x_2852_ = lean_nat_dec_lt(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec(v_a_2846_);
lean_dec(v_val_2844_);
v___x_2853_ = lean_box(v___x_2852_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2853_);
v___x_2855_ = v___x_2848_;
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
else
{
if (v___x_2852_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec(v_a_2846_);
lean_dec(v_val_2844_);
v___x_2857_ = lean_box(v___x_2852_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2857_);
v___x_2859_ = v___x_2848_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
size_t v___x_2861_; size_t v___x_2862_; uint64_t v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = lean_usize_of_nat(v___x_2851_);
v___x_2863_ = lean_unbox_uint64(v_a_2846_);
lean_dec(v_a_2846_);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2863_, v_val_2844_, v___x_2861_, v___x_2862_);
lean_dec(v_val_2844_);
v___x_2865_ = lean_box(v___x_2864_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2865_);
v___x_2867_ = v___x_2848_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_val_2844_);
v_a_2870_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2845_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2845_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_dec(v_a_2840_);
v___x_2878_ = 1;
v___x_2879_ = lean_box(v___x_2878_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2879_);
v___x_2881_ = v___x_2842_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_a_2884_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2839_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2839_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2828_ = stack[0].m_obj;
lean_object* v_a_2829_ = stack[1].m_obj;
lean_object* v_a_2830_ = stack[2].m_obj;
lean_object* v_a_2831_ = stack[3].m_obj;
lean_object* v_a_2832_ = stack[4].m_obj;
lean_object* v_a_2833_ = stack[5].m_obj;
lean_object* v_a_2834_ = stack[6].m_obj;
lean_object* v_a_2835_ = stack[7].m_obj;
lean_object* v_a_2836_ = stack[8].m_obj;
lean_object* v_a_2837_ = stack[9].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_c_2893_);
return v_res_2904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2907_ = l_Lean_stringToMessageData(v___x_2906_);
return v___x_2907_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2908_, lean_object* v_c_x3f_2909_, lean_object* v_cs_x27_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
if (lean_obj_tag(v_cs_2908_) == 0)
{
lean_object* v___x_2922_; lean_object* v_toGoalState_2923_; lean_object* v_split_2924_; lean_object* v_mvarId_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_3033_; 
v___x_2922_ = lean_st_ref_take(v_a_2911_);
v_toGoalState_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_ref(v_toGoalState_2923_);
v_split_2924_ = lean_ctor_get(v_toGoalState_2923_, 14);
lean_inc_ref(v_split_2924_);
v_mvarId_2925_ = lean_ctor_get(v___x_2922_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; 
v_unused_3034_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_3034_);
v___x_2927_ = v___x_2922_;
v_isShared_2928_ = v_isSharedCheck_3033_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_mvarId_2925_);
lean_dec(v___x_2922_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_3033_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v_nextDeclIdx_2929_; lean_object* v_enodeMap_2930_; lean_object* v_exprs_2931_; lean_object* v_parents_2932_; lean_object* v_congrTable_2933_; lean_object* v_appMap_2934_; lean_object* v_indicesFound_2935_; lean_object* v_toProcess_2936_; uint8_t v_inconsistent_2937_; lean_object* v_nextIdx_2938_; lean_object* v_newRawFacts_2939_; lean_object* v_facts_2940_; lean_object* v_extThms_2941_; lean_object* v_ematch_2942_; lean_object* v_inj_2943_; lean_object* v_clean_2944_; lean_object* v_sstates_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3031_; 
v_nextDeclIdx_2929_ = lean_ctor_get(v_toGoalState_2923_, 0);
v_enodeMap_2930_ = lean_ctor_get(v_toGoalState_2923_, 1);
v_exprs_2931_ = lean_ctor_get(v_toGoalState_2923_, 2);
v_parents_2932_ = lean_ctor_get(v_toGoalState_2923_, 3);
v_congrTable_2933_ = lean_ctor_get(v_toGoalState_2923_, 4);
v_appMap_2934_ = lean_ctor_get(v_toGoalState_2923_, 5);
v_indicesFound_2935_ = lean_ctor_get(v_toGoalState_2923_, 6);
v_toProcess_2936_ = lean_ctor_get(v_toGoalState_2923_, 7);
v_inconsistent_2937_ = lean_ctor_get_uint8(v_toGoalState_2923_, sizeof(void*)*17);
v_nextIdx_2938_ = lean_ctor_get(v_toGoalState_2923_, 8);
v_newRawFacts_2939_ = lean_ctor_get(v_toGoalState_2923_, 9);
v_facts_2940_ = lean_ctor_get(v_toGoalState_2923_, 10);
v_extThms_2941_ = lean_ctor_get(v_toGoalState_2923_, 11);
v_ematch_2942_ = lean_ctor_get(v_toGoalState_2923_, 12);
v_inj_2943_ = lean_ctor_get(v_toGoalState_2923_, 13);
v_clean_2944_ = lean_ctor_get(v_toGoalState_2923_, 15);
v_sstates_2945_ = lean_ctor_get(v_toGoalState_2923_, 16);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_toGoalState_2923_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v_toGoalState_2923_, 14);
lean_dec(v_unused_3032_);
v___x_2947_ = v_toGoalState_2923_;
v_isShared_2948_ = v_isSharedCheck_3031_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_sstates_2945_);
lean_inc(v_clean_2944_);
lean_inc(v_inj_2943_);
lean_inc(v_ematch_2942_);
lean_inc(v_extThms_2941_);
lean_inc(v_facts_2940_);
lean_inc(v_newRawFacts_2939_);
lean_inc(v_nextIdx_2938_);
lean_inc(v_toProcess_2936_);
lean_inc(v_indicesFound_2935_);
lean_inc(v_appMap_2934_);
lean_inc(v_congrTable_2933_);
lean_inc(v_parents_2932_);
lean_inc(v_exprs_2931_);
lean_inc(v_enodeMap_2930_);
lean_inc(v_nextDeclIdx_2929_);
lean_dec(v_toGoalState_2923_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3031_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_num_2949_; lean_object* v_added_2950_; lean_object* v_resolved_2951_; lean_object* v_trace_2952_; lean_object* v_lookaheads_2953_; lean_object* v_argPosMap_2954_; lean_object* v_argsAt_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3029_; 
v_num_2949_ = lean_ctor_get(v_split_2924_, 0);
v_added_2950_ = lean_ctor_get(v_split_2924_, 2);
v_resolved_2951_ = lean_ctor_get(v_split_2924_, 3);
v_trace_2952_ = lean_ctor_get(v_split_2924_, 4);
v_lookaheads_2953_ = lean_ctor_get(v_split_2924_, 5);
v_argPosMap_2954_ = lean_ctor_get(v_split_2924_, 6);
v_argsAt_2955_ = lean_ctor_get(v_split_2924_, 7);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_split_2924_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v_split_2924_, 1);
lean_dec(v_unused_3030_);
v___x_2957_ = v_split_2924_;
v_isShared_2958_ = v_isSharedCheck_3029_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_argsAt_2955_);
lean_inc(v_argPosMap_2954_);
lean_inc(v_lookaheads_2953_);
lean_inc(v_trace_2952_);
lean_inc(v_resolved_2951_);
lean_inc(v_added_2950_);
lean_inc(v_num_2949_);
lean_dec(v_split_2924_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3029_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = l_List_reverse___redArg(v_cs_x27_2910_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2959_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_num_2949_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_added_2950_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_resolved_2951_);
lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_trace_2952_);
lean_ctor_set(v_reuseFailAlloc_3028_, 5, v_lookaheads_2953_);
lean_ctor_set(v_reuseFailAlloc_3028_, 6, v_argPosMap_2954_);
lean_ctor_set(v_reuseFailAlloc_3028_, 7, v_argsAt_2955_);
v___x_2961_ = v_reuseFailAlloc_3028_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2963_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 14, v___x_2961_);
v___x_2963_ = v___x_2947_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_nextDeclIdx_2929_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_enodeMap_2930_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_exprs_2931_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_parents_2932_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v_congrTable_2933_);
lean_ctor_set(v_reuseFailAlloc_3027_, 5, v_appMap_2934_);
lean_ctor_set(v_reuseFailAlloc_3027_, 6, v_indicesFound_2935_);
lean_ctor_set(v_reuseFailAlloc_3027_, 7, v_toProcess_2936_);
lean_ctor_set(v_reuseFailAlloc_3027_, 8, v_nextIdx_2938_);
lean_ctor_set(v_reuseFailAlloc_3027_, 9, v_newRawFacts_2939_);
lean_ctor_set(v_reuseFailAlloc_3027_, 10, v_facts_2940_);
lean_ctor_set(v_reuseFailAlloc_3027_, 11, v_extThms_2941_);
lean_ctor_set(v_reuseFailAlloc_3027_, 12, v_ematch_2942_);
lean_ctor_set(v_reuseFailAlloc_3027_, 13, v_inj_2943_);
lean_ctor_set(v_reuseFailAlloc_3027_, 14, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_3027_, 15, v_clean_2944_);
lean_ctor_set(v_reuseFailAlloc_3027_, 16, v_sstates_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*17, v_inconsistent_2937_);
v___x_2963_ = v_reuseFailAlloc_3027_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2963_);
v___x_2965_ = v___x_2927_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_mvarId_2925_);
v___x_2965_ = v_reuseFailAlloc_3026_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_st_ref_put(v_a_2911_, v___x_2965_);
if (lean_obj_tag(v_c_x3f_2909_) == 1)
{
lean_object* v___x_2967_; lean_object* v_toGoalState_2968_; lean_object* v_ematch_2969_; lean_object* v_mvarId_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3023_; 
v___x_2967_ = lean_st_ref_take(v_a_2911_);
v_toGoalState_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_ref(v_toGoalState_2968_);
v_ematch_2969_ = lean_ctor_get(v_toGoalState_2968_, 12);
lean_inc_ref(v_ematch_2969_);
v_mvarId_2970_ = lean_ctor_get(v___x_2967_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v___x_2967_, 0);
lean_dec(v_unused_3024_);
v___x_2972_ = v___x_2967_;
v_isShared_2973_ = v_isSharedCheck_3023_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_mvarId_2970_);
lean_dec(v___x_2967_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3023_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_nextDeclIdx_2974_; lean_object* v_enodeMap_2975_; lean_object* v_exprs_2976_; lean_object* v_parents_2977_; lean_object* v_congrTable_2978_; lean_object* v_appMap_2979_; lean_object* v_indicesFound_2980_; lean_object* v_toProcess_2981_; uint8_t v_inconsistent_2982_; lean_object* v_nextIdx_2983_; lean_object* v_newRawFacts_2984_; lean_object* v_facts_2985_; lean_object* v_extThms_2986_; lean_object* v_inj_2987_; lean_object* v_split_2988_; lean_object* v_clean_2989_; lean_object* v_sstates_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3021_; 
v_nextDeclIdx_2974_ = lean_ctor_get(v_toGoalState_2968_, 0);
v_enodeMap_2975_ = lean_ctor_get(v_toGoalState_2968_, 1);
v_exprs_2976_ = lean_ctor_get(v_toGoalState_2968_, 2);
v_parents_2977_ = lean_ctor_get(v_toGoalState_2968_, 3);
v_congrTable_2978_ = lean_ctor_get(v_toGoalState_2968_, 4);
v_appMap_2979_ = lean_ctor_get(v_toGoalState_2968_, 5);
v_indicesFound_2980_ = lean_ctor_get(v_toGoalState_2968_, 6);
v_toProcess_2981_ = lean_ctor_get(v_toGoalState_2968_, 7);
v_inconsistent_2982_ = lean_ctor_get_uint8(v_toGoalState_2968_, sizeof(void*)*17);
v_nextIdx_2983_ = lean_ctor_get(v_toGoalState_2968_, 8);
v_newRawFacts_2984_ = lean_ctor_get(v_toGoalState_2968_, 9);
v_facts_2985_ = lean_ctor_get(v_toGoalState_2968_, 10);
v_extThms_2986_ = lean_ctor_get(v_toGoalState_2968_, 11);
v_inj_2987_ = lean_ctor_get(v_toGoalState_2968_, 13);
v_split_2988_ = lean_ctor_get(v_toGoalState_2968_, 14);
v_clean_2989_ = lean_ctor_get(v_toGoalState_2968_, 15);
v_sstates_2990_ = lean_ctor_get(v_toGoalState_2968_, 16);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_toGoalState_2968_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v_toGoalState_2968_, 12);
lean_dec(v_unused_3022_);
v___x_2992_ = v_toGoalState_2968_;
v_isShared_2993_ = v_isSharedCheck_3021_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_sstates_2990_);
lean_inc(v_clean_2989_);
lean_inc(v_split_2988_);
lean_inc(v_inj_2987_);
lean_inc(v_extThms_2986_);
lean_inc(v_facts_2985_);
lean_inc(v_newRawFacts_2984_);
lean_inc(v_nextIdx_2983_);
lean_inc(v_toProcess_2981_);
lean_inc(v_indicesFound_2980_);
lean_inc(v_appMap_2979_);
lean_inc(v_congrTable_2978_);
lean_inc(v_parents_2977_);
lean_inc(v_exprs_2976_);
lean_inc(v_enodeMap_2975_);
lean_inc(v_nextDeclIdx_2974_);
lean_dec(v_toGoalState_2968_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3021_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_thmMap_2994_; lean_object* v_gmt_2995_; lean_object* v_thms_2996_; lean_object* v_newThms_2997_; lean_object* v_numInstances_2998_; lean_object* v_numDelayedInstances_2999_; lean_object* v_preInstances_3000_; lean_object* v_nextThmIdx_3001_; lean_object* v_matchEqNames_3002_; lean_object* v_delayedThmInsts_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3019_; 
v_thmMap_2994_ = lean_ctor_get(v_ematch_2969_, 0);
v_gmt_2995_ = lean_ctor_get(v_ematch_2969_, 1);
v_thms_2996_ = lean_ctor_get(v_ematch_2969_, 2);
v_newThms_2997_ = lean_ctor_get(v_ematch_2969_, 3);
v_numInstances_2998_ = lean_ctor_get(v_ematch_2969_, 4);
v_numDelayedInstances_2999_ = lean_ctor_get(v_ematch_2969_, 5);
v_preInstances_3000_ = lean_ctor_get(v_ematch_2969_, 7);
v_nextThmIdx_3001_ = lean_ctor_get(v_ematch_2969_, 8);
v_matchEqNames_3002_ = lean_ctor_get(v_ematch_2969_, 9);
v_delayedThmInsts_3003_ = lean_ctor_get(v_ematch_2969_, 10);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_ematch_2969_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_ematch_2969_, 6);
lean_dec(v_unused_3020_);
v___x_3005_ = v_ematch_2969_;
v_isShared_3006_ = v_isSharedCheck_3019_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_delayedThmInsts_3003_);
lean_inc(v_matchEqNames_3002_);
lean_inc(v_nextThmIdx_3001_);
lean_inc(v_preInstances_3000_);
lean_inc(v_numDelayedInstances_2999_);
lean_inc(v_numInstances_2998_);
lean_inc(v_newThms_2997_);
lean_inc(v_thms_2996_);
lean_inc(v_gmt_2995_);
lean_inc(v_thmMap_2994_);
lean_dec(v_ematch_2969_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3019_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_unsigned_to_nat(0u);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 6, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_thmMap_2994_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_gmt_2995_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_thms_2996_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_newThms_2997_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_numInstances_2998_);
lean_ctor_set(v_reuseFailAlloc_3018_, 5, v_numDelayedInstances_2999_);
lean_ctor_set(v_reuseFailAlloc_3018_, 6, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3018_, 7, v_preInstances_3000_);
lean_ctor_set(v_reuseFailAlloc_3018_, 8, v_nextThmIdx_3001_);
lean_ctor_set(v_reuseFailAlloc_3018_, 9, v_matchEqNames_3002_);
lean_ctor_set(v_reuseFailAlloc_3018_, 10, v_delayedThmInsts_3003_);
v___x_3009_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3011_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 12, v___x_3009_);
v___x_3011_ = v___x_2992_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_nextDeclIdx_2974_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_enodeMap_2975_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_exprs_2976_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_parents_2977_);
lean_ctor_set(v_reuseFailAlloc_3017_, 4, v_congrTable_2978_);
lean_ctor_set(v_reuseFailAlloc_3017_, 5, v_appMap_2979_);
lean_ctor_set(v_reuseFailAlloc_3017_, 6, v_indicesFound_2980_);
lean_ctor_set(v_reuseFailAlloc_3017_, 7, v_toProcess_2981_);
lean_ctor_set(v_reuseFailAlloc_3017_, 8, v_nextIdx_2983_);
lean_ctor_set(v_reuseFailAlloc_3017_, 9, v_newRawFacts_2984_);
lean_ctor_set(v_reuseFailAlloc_3017_, 10, v_facts_2985_);
lean_ctor_set(v_reuseFailAlloc_3017_, 11, v_extThms_2986_);
lean_ctor_set(v_reuseFailAlloc_3017_, 12, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3017_, 13, v_inj_2987_);
lean_ctor_set(v_reuseFailAlloc_3017_, 14, v_split_2988_);
lean_ctor_set(v_reuseFailAlloc_3017_, 15, v_clean_2989_);
lean_ctor_set(v_reuseFailAlloc_3017_, 16, v_sstates_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3017_, sizeof(void*)*17, v_inconsistent_2982_);
v___x_3011_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_3011_);
v___x_3013_ = v___x_2972_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_mvarId_2970_);
v___x_3013_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_st_ref_put(v_a_2911_, v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_c_x3f_2909_);
return v___x_3015_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_c_x3f_2909_);
return v___x_3025_;
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
lean_object* v_head_3035_; lean_object* v_tail_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3256_; 
v_head_3035_ = lean_ctor_get(v_cs_2908_, 0);
v_tail_3036_ = lean_ctor_get(v_cs_2908_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_cs_2908_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3038_ = v_cs_2908_;
v_isShared_3039_ = v_isSharedCheck_3256_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_tail_3036_);
lean_inc(v_head_3035_);
lean_dec(v_cs_2908_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3256_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; uint8_t v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; uint8_t v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; uint8_t v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; uint8_t v___y_3143_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v___x_3148_; 
v___x_3148_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_3035_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; uint8_t v___x_3150_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = lean_unbox(v_a_3149_);
lean_dec(v_a_3149_);
if (v___x_3150_ == 0)
{
lean_del_object(v___x_3038_);
lean_dec(v_head_3035_);
v_cs_2908_ = v_tail_3036_;
goto _start;
}
else
{
lean_object* v_toCold_3152_; lean_object* v_options_3153_; lean_object* v_inheritedTraceOptions_3154_; uint8_t v_hasTrace_3155_; uint8_t v___x_3156_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; uint8_t v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3170_; uint8_t v___y_3171_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; 
v_toCold_3152_ = lean_ctor_get(v_a_2919_, 0);
v_options_3153_ = lean_ctor_get(v_toCold_3152_, 2);
v_inheritedTraceOptions_3154_ = lean_ctor_get(v_toCold_3152_, 11);
v_hasTrace_3155_ = lean_ctor_get_uint8(v_options_3153_, sizeof(void*)*1);
v___x_3156_ = 0;
if (v_hasTrace_3155_ == 0)
{
v___y_3182_ = v_a_2911_;
v___y_3183_ = v_a_2912_;
v___y_3184_ = v_a_2913_;
v___y_3185_ = v_a_2914_;
v___y_3186_ = v_a_2915_;
v___y_3187_ = v_a_2916_;
v___y_3188_ = v_a_2917_;
v___y_3189_ = v_a_2918_;
v___y_3190_ = v_a_2919_;
v___y_3191_ = v_a_2920_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3154_, v_options_3153_, v___x_3224_);
if (v___x_3225_ == 0)
{
v___y_3182_ = v_a_2911_;
v___y_3183_ = v_a_2912_;
v___y_3184_ = v_a_2913_;
v___y_3185_ = v_a_2914_;
v___y_3186_ = v_a_2915_;
v___y_3187_ = v_a_2916_;
v___y_3188_ = v_a_2917_;
v___y_3189_ = v_a_2918_;
v___y_3190_ = v_a_2919_;
v___y_3191_ = v_a_2920_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Meta_Grind_updateLastTag(v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec_ref_known(v___x_3226_, 1);
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3228_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_3035_);
v___x_3229_ = l_Lean_MessageData_ofExpr(v___x_3228_);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3223_, v___x_3230_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec_ref_known(v___x_3231_, 1);
v___y_3182_ = v_a_2911_;
v___y_3183_ = v_a_2912_;
v___y_3184_ = v_a_2913_;
v___y_3185_ = v_a_2914_;
v___y_3186_ = v_a_2915_;
v___y_3187_ = v_a_2916_;
v___y_3188_ = v_a_2917_;
v___y_3189_ = v_a_2918_;
v___y_3190_ = v_a_2919_;
v___y_3191_ = v_a_2920_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3240_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3226_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3226_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
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
}
v___jp_3157_:
{
if (lean_obj_tag(v_c_x3f_2909_) == 0)
{
lean_object* v___x_3172_; 
lean_del_object(v___x_3038_);
v___x_3172_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3172_, 0, v_head_3035_);
lean_ctor_set(v___x_3172_, 1, v___y_3170_);
lean_ctor_set_uint8(v___x_3172_, sizeof(void*)*2, v___y_3169_);
lean_ctor_set_uint8(v___x_3172_, sizeof(void*)*2 + 1, v___y_3162_);
v_cs_2908_ = v_tail_3036_;
v_c_x3f_2909_ = v___x_3172_;
v_a_2911_ = v___y_3166_;
v_a_2912_ = v___y_3161_;
v_a_2913_ = v___y_3164_;
v_a_2914_ = v___y_3168_;
v_a_2915_ = v___y_3158_;
v_a_2916_ = v___y_3167_;
v_a_2917_ = v___y_3159_;
v_a_2918_ = v___y_3163_;
v_a_2919_ = v___y_3160_;
v_a_2920_ = v___y_3165_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3174_; 
v_tryPostpone_3174_ = lean_ctor_get_uint8(v_c_x3f_2909_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3174_ == 0)
{
if (v___y_3162_ == 0)
{
lean_object* v_c_3175_; lean_object* v_numCases_3176_; 
v_c_3175_ = lean_ctor_get(v_c_x3f_2909_, 0);
v_numCases_3176_ = lean_ctor_get(v_c_x3f_2909_, 1);
lean_inc_ref(v_c_3175_);
lean_inc(v_numCases_3176_);
v___y_3130_ = v___y_3158_;
v___y_3131_ = v___y_3159_;
v___y_3132_ = v___y_3160_;
v___y_3133_ = v___y_3161_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v_numCases_3176_;
v___y_3136_ = v___y_3163_;
v___y_3137_ = v___y_3164_;
v___y_3138_ = v___y_3165_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3167_;
v___y_3141_ = v___y_3168_;
v___y_3142_ = v_c_3175_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___x_3156_;
goto v___jp_3129_;
}
else
{
lean_dec(v___y_3170_);
v___y_3041_ = v___y_3167_;
v___y_3042_ = v___y_3158_;
v___y_3043_ = v___y_3159_;
v___y_3044_ = v___y_3160_;
v___y_3045_ = v___y_3161_;
v___y_3046_ = v___y_3168_;
v___y_3047_ = v___y_3163_;
v___y_3048_ = v___y_3165_;
v___y_3049_ = v___y_3164_;
v___y_3050_ = v___y_3166_;
goto v___jp_3040_;
}
}
else
{
if (v___y_3162_ == 0)
{
lean_object* v_c_3177_; 
lean_del_object(v___x_3038_);
v_c_3177_ = lean_ctor_get(v_c_x3f_2909_, 0);
lean_inc_ref(v_c_3177_);
lean_dec_ref_known(v_c_x3f_2909_, 2);
v___y_3056_ = v___y_3158_;
v___y_3057_ = v___y_3159_;
v___y_3058_ = v___y_3160_;
v___y_3059_ = v___y_3161_;
v___y_3060_ = v___y_3162_;
v___y_3061_ = v___y_3163_;
v___y_3062_ = v___y_3165_;
v___y_3063_ = v___y_3164_;
v___y_3064_ = v___y_3166_;
v___y_3065_ = v___y_3167_;
v___y_3066_ = v___y_3168_;
v___y_3067_ = v_c_3177_;
v___y_3068_ = v___y_3169_;
v___y_3069_ = v___y_3170_;
goto v___jp_3055_;
}
else
{
if (v___y_3171_ == 0)
{
lean_object* v_c_3178_; lean_object* v_numCases_3179_; 
v_c_3178_ = lean_ctor_get(v_c_x3f_2909_, 0);
v_numCases_3179_ = lean_ctor_get(v_c_x3f_2909_, 1);
lean_inc_ref(v_c_3178_);
lean_inc(v_numCases_3179_);
v___y_3130_ = v___y_3158_;
v___y_3131_ = v___y_3159_;
v___y_3132_ = v___y_3160_;
v___y_3133_ = v___y_3161_;
v___y_3134_ = v___y_3162_;
v___y_3135_ = v_numCases_3179_;
v___y_3136_ = v___y_3163_;
v___y_3137_ = v___y_3164_;
v___y_3138_ = v___y_3165_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3167_;
v___y_3141_ = v___y_3168_;
v___y_3142_ = v_c_3178_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___y_3171_;
goto v___jp_3129_;
}
else
{
lean_object* v_c_3180_; 
lean_del_object(v___x_3038_);
v_c_3180_ = lean_ctor_get(v_c_x3f_2909_, 0);
lean_inc_ref(v_c_3180_);
lean_dec_ref_known(v_c_x3f_2909_, 2);
v___y_3056_ = v___y_3158_;
v___y_3057_ = v___y_3159_;
v___y_3058_ = v___y_3160_;
v___y_3059_ = v___y_3161_;
v___y_3060_ = v___y_3162_;
v___y_3061_ = v___y_3163_;
v___y_3062_ = v___y_3165_;
v___y_3063_ = v___y_3164_;
v___y_3064_ = v___y_3166_;
v___y_3065_ = v___y_3167_;
v___y_3066_ = v___y_3168_;
v___y_3067_ = v_c_3180_;
v___y_3068_ = v___y_3169_;
v___y_3069_ = v___y_3170_;
goto v___jp_3055_;
}
}
}
}
}
v___jp_3181_:
{
lean_object* v___x_3192_; 
lean_inc(v_head_3035_);
v___x_3192_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_3035_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
switch(lean_obj_tag(v_a_3193_))
{
case 0:
{
lean_del_object(v___x_3038_);
lean_dec(v_head_3035_);
v_cs_2908_ = v_tail_3036_;
v_a_2911_ = v___y_3182_;
v_a_2912_ = v___y_3183_;
v_a_2913_ = v___y_3184_;
v_a_2914_ = v___y_3185_;
v_a_2915_ = v___y_3186_;
v_a_2916_ = v___y_3187_;
v_a_2917_ = v___y_3188_;
v_a_2918_ = v___y_3189_;
v_a_2919_ = v___y_3190_;
v_a_2920_ = v___y_3191_;
goto _start;
}
case 1:
{
lean_object* v___x_3195_; 
lean_del_object(v___x_3038_);
v___x_3195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_head_3035_);
lean_ctor_set(v___x_3195_, 1, v_cs_x27_2910_);
v_cs_2908_ = v_tail_3036_;
v_cs_x27_2910_ = v___x_3195_;
v_a_2911_ = v___y_3182_;
v_a_2912_ = v___y_3183_;
v_a_2913_ = v___y_3184_;
v_a_2914_ = v___y_3185_;
v_a_2915_ = v___y_3186_;
v_a_2916_ = v___y_3187_;
v_a_2917_ = v___y_3188_;
v_a_2918_ = v___y_3189_;
v_a_2919_ = v___y_3190_;
v_a_2920_ = v___y_3191_;
goto _start;
}
default: 
{
lean_object* v_numCases_3197_; uint8_t v_isRec_3198_; uint8_t v_tryPostpone_3199_; lean_object* v___x_3200_; 
v_numCases_3197_ = lean_ctor_get(v_a_3193_, 0);
lean_inc(v_numCases_3197_);
v_isRec_3198_ = lean_ctor_get_uint8(v_a_3193_, sizeof(void*)*1);
v_tryPostpone_3199_ = lean_ctor_get_uint8(v_a_3193_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3193_, 1);
v___x_3200_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3184_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; uint8_t v___x_3202_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = lean_unbox(v_a_3201_);
lean_dec(v_a_3201_);
if (v___x_3202_ == 0)
{
v___y_3158_ = v___y_3186_;
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3190_;
v___y_3161_ = v___y_3183_;
v___y_3162_ = v_tryPostpone_3199_;
v___y_3163_ = v___y_3189_;
v___y_3164_ = v___y_3184_;
v___y_3165_ = v___y_3191_;
v___y_3166_ = v___y_3182_;
v___y_3167_ = v___y_3187_;
v___y_3168_ = v___y_3185_;
v___y_3169_ = v_isRec_3198_;
v___y_3170_ = v_numCases_3197_;
v___y_3171_ = v___x_3156_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3203_ = lean_unsigned_to_nat(1u);
v___x_3204_ = lean_nat_dec_lt(v___x_3203_, v_numCases_3197_);
if (v___x_3204_ == 0)
{
v___y_3158_ = v___y_3186_;
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3190_;
v___y_3161_ = v___y_3183_;
v___y_3162_ = v_tryPostpone_3199_;
v___y_3163_ = v___y_3189_;
v___y_3164_ = v___y_3184_;
v___y_3165_ = v___y_3191_;
v___y_3166_ = v___y_3182_;
v___y_3167_ = v___y_3187_;
v___y_3168_ = v___y_3185_;
v___y_3169_ = v_isRec_3198_;
v___y_3170_ = v_numCases_3197_;
v___y_3171_ = v___x_3204_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3205_; 
lean_dec(v_numCases_3197_);
lean_del_object(v___x_3038_);
v___x_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3205_, 0, v_head_3035_);
lean_ctor_set(v___x_3205_, 1, v_cs_x27_2910_);
v_cs_2908_ = v_tail_3036_;
v_cs_x27_2910_ = v___x_3205_;
v_a_2911_ = v___y_3182_;
v_a_2912_ = v___y_3183_;
v_a_2913_ = v___y_3184_;
v_a_2914_ = v___y_3185_;
v_a_2915_ = v___y_3186_;
v_a_2916_ = v___y_3187_;
v_a_2917_ = v___y_3188_;
v_a_2918_ = v___y_3189_;
v_a_2919_ = v___y_3190_;
v_a_2920_ = v___y_3191_;
goto _start;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_numCases_3197_);
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3207_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3200_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3200_);
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
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3215_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3192_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3192_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3248_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3148_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3148_);
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
v___jp_3040_:
{
lean_object* v___x_3052_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v_cs_x27_2910_);
v___x_3052_ = v___x_3038_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_head_3035_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_cs_x27_2910_);
v___x_3052_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
v_cs_2908_ = v_tail_3036_;
v_cs_x27_2910_ = v___x_3052_;
v_a_2911_ = v___y_3050_;
v_a_2912_ = v___y_3045_;
v_a_2913_ = v___y_3049_;
v_a_2914_ = v___y_3046_;
v_a_2915_ = v___y_3042_;
v_a_2916_ = v___y_3041_;
v_a_2917_ = v___y_3043_;
v_a_2918_ = v___y_3047_;
v_a_2919_ = v___y_3044_;
v_a_2920_ = v___y_3048_;
goto _start;
}
}
v___jp_3055_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3070_, 0, v_head_3035_);
lean_ctor_set(v___x_3070_, 1, v___y_3069_);
lean_ctor_set_uint8(v___x_3070_, sizeof(void*)*2, v___y_3068_);
lean_ctor_set_uint8(v___x_3070_, sizeof(void*)*2 + 1, v___y_3060_);
v___x_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3067_);
lean_ctor_set(v___x_3071_, 1, v_cs_x27_2910_);
v_cs_2908_ = v_tail_3036_;
v_c_x3f_2909_ = v___x_3070_;
v_cs_x27_2910_ = v___x_3071_;
v_a_2911_ = v___y_3064_;
v_a_2912_ = v___y_3059_;
v_a_2913_ = v___y_3063_;
v_a_2914_ = v___y_3066_;
v_a_2915_ = v___y_3056_;
v_a_2916_ = v___y_3065_;
v_a_2917_ = v___y_3057_;
v_a_2918_ = v___y_3061_;
v_a_2919_ = v___y_3058_;
v_a_2920_ = v___y_3062_;
goto _start;
}
v___jp_3073_:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_3035_, v___y_3083_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3091_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3091_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3086_, v___y_3083_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; uint8_t v___x_3093_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = lean_nat_dec_lt(v_a_3090_, v_a_3092_);
lean_dec(v_a_3092_);
lean_dec(v_a_3090_);
if (v___x_3093_ == 0)
{
uint8_t v___x_3094_; 
v___x_3094_ = lean_nat_dec_lt(v___y_3088_, v___y_3079_);
lean_dec(v___y_3079_);
if (v___x_3094_ == 0)
{
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3086_);
v___y_3041_ = v___y_3084_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3085_;
v___y_3047_ = v___y_3080_;
v___y_3048_ = v___y_3082_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3083_;
goto v___jp_3040_;
}
else
{
lean_del_object(v___x_3038_);
lean_dec(v_c_x3f_2909_);
v___y_3056_ = v___y_3074_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3077_;
v___y_3060_ = v___y_3078_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3082_;
v___y_3063_ = v___y_3081_;
v___y_3064_ = v___y_3083_;
v___y_3065_ = v___y_3084_;
v___y_3066_ = v___y_3085_;
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3087_;
v___y_3069_ = v___y_3088_;
goto v___jp_3055_;
}
}
else
{
lean_dec(v___y_3079_);
lean_del_object(v___x_3038_);
lean_dec(v_c_x3f_2909_);
v___y_3056_ = v___y_3074_;
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3076_;
v___y_3059_ = v___y_3077_;
v___y_3060_ = v___y_3078_;
v___y_3061_ = v___y_3080_;
v___y_3062_ = v___y_3082_;
v___y_3063_ = v___y_3081_;
v___y_3064_ = v___y_3083_;
v___y_3065_ = v___y_3084_;
v___y_3066_ = v___y_3085_;
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3087_;
v___y_3069_ = v___y_3088_;
goto v___jp_3055_;
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_a_3090_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3079_);
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3095_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3091_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3091_);
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
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3079_);
lean_del_object(v___x_3038_);
lean_dec(v_tail_3036_);
lean_dec(v_head_3035_);
lean_dec(v_cs_x27_2910_);
lean_dec(v_c_x3f_2909_);
v_a_3103_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3089_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3089_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
v___jp_3111_:
{
lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3127_ = lean_unsigned_to_nat(1u);
v___x_3128_ = lean_nat_dec_lt(v___x_3127_, v___y_3117_);
if (v___x_3128_ == 0)
{
v___y_3074_ = v___y_3112_;
v___y_3075_ = v___y_3113_;
v___y_3076_ = v___y_3114_;
v___y_3077_ = v___y_3115_;
v___y_3078_ = v___y_3116_;
v___y_3079_ = v___y_3117_;
v___y_3080_ = v___y_3118_;
v___y_3081_ = v___y_3119_;
v___y_3082_ = v___y_3120_;
v___y_3083_ = v___y_3121_;
v___y_3084_ = v___y_3122_;
v___y_3085_ = v___y_3123_;
v___y_3086_ = v___y_3124_;
v___y_3087_ = v___y_3125_;
v___y_3088_ = v___y_3126_;
goto v___jp_3073_;
}
else
{
lean_dec(v___y_3117_);
lean_del_object(v___x_3038_);
lean_dec(v_c_x3f_2909_);
v___y_3056_ = v___y_3112_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3116_;
v___y_3061_ = v___y_3118_;
v___y_3062_ = v___y_3120_;
v___y_3063_ = v___y_3119_;
v___y_3064_ = v___y_3121_;
v___y_3065_ = v___y_3122_;
v___y_3066_ = v___y_3123_;
v___y_3067_ = v___y_3124_;
v___y_3068_ = v___y_3125_;
v___y_3069_ = v___y_3126_;
goto v___jp_3055_;
}
}
v___jp_3129_:
{
lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = lean_nat_dec_eq(v___y_3144_, v___x_3146_);
if (v___x_3147_ == 0)
{
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
v___y_3085_ = v___y_3141_;
v___y_3086_ = v___y_3142_;
v___y_3087_ = v___y_3143_;
v___y_3088_ = v___y_3144_;
goto v___jp_3073_;
}
else
{
if (v___y_3143_ == 0)
{
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3131_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3139_;
v___y_3122_ = v___y_3140_;
v___y_3123_ = v___y_3141_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3143_;
v___y_3126_ = v___y_3144_;
goto v___jp_3111_;
}
else
{
if (v___y_3145_ == 0)
{
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
v___y_3085_ = v___y_3141_;
v___y_3086_ = v___y_3142_;
v___y_3087_ = v___y_3143_;
v___y_3088_ = v___y_3144_;
goto v___jp_3073_;
}
else
{
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3131_;
v___y_3114_ = v___y_3132_;
v___y_3115_ = v___y_3133_;
v___y_3116_ = v___y_3134_;
v___y_3117_ = v___y_3135_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3139_;
v___y_3122_ = v___y_3140_;
v___y_3123_ = v___y_3141_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3143_;
v___y_3126_ = v___y_3144_;
goto v___jp_3111_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_cs_2908_ = stack[0].m_obj;
lean_object* v_c_x3f_2909_ = stack[1].m_obj;
lean_object* v_cs_x27_2910_ = stack[2].m_obj;
lean_object* v_a_2911_ = stack[3].m_obj;
lean_object* v_a_2912_ = stack[4].m_obj;
lean_object* v_a_2913_ = stack[5].m_obj;
lean_object* v_a_2914_ = stack[6].m_obj;
lean_object* v_a_2915_ = stack[7].m_obj;
lean_object* v_a_2916_ = stack[8].m_obj;
lean_object* v_a_2917_ = stack[9].m_obj;
lean_object* v_a_2918_ = stack[10].m_obj;
lean_object* v_a_2919_ = stack[11].m_obj;
lean_object* v_a_2920_ = stack[12].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_2908_, v_c_x3f_2909_, v_cs_x27_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3258_, lean_object* v_c_x3f_3259_, lean_object* v_cs_x27_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3258_, v_c_x3f_3259_, v_cs_x27_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec(v_a_3261_);
return v_res_3272_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3273_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3320_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3320_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3320_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
uint8_t v___x_3289_; 
v___x_3289_ = lean_unbox(v_a_3285_);
lean_dec(v_a_3285_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
lean_del_object(v___x_3287_);
v___x_3290_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3273_, v_a_3275_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3307_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3307_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3307_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
uint8_t v___x_3295_; 
v___x_3295_ = lean_unbox(v_a_3291_);
lean_dec(v_a_3291_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v_toGoalState_3297_; lean_object* v_split_3298_; lean_object* v_candidates_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_del_object(v___x_3293_);
v___x_3296_ = lean_st_ref_get(v_a_3273_);
v_toGoalState_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc_ref(v_toGoalState_3297_);
lean_dec(v___x_3296_);
v_split_3298_ = lean_ctor_get(v_toGoalState_3297_, 14);
lean_inc_ref(v_split_3298_);
lean_dec_ref(v_toGoalState_3297_);
v_candidates_3299_ = lean_ctor_get(v_split_3298_, 1);
lean_inc(v_candidates_3299_);
lean_dec_ref(v_split_3298_);
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_box(0);
v___x_3302_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3299_, v___x_3300_, v___x_3301_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_box(0);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3303_);
v___x_3305_ = v___x_3293_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_a_3308_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3290_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3290_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
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
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3316_);
v___x_3318_ = v___x_3287_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3321_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3284_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3284_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3273_ = stack[0].m_obj;
lean_object* v_a_3274_ = stack[1].m_obj;
lean_object* v_a_3275_ = stack[2].m_obj;
lean_object* v_a_3276_ = stack[3].m_obj;
lean_object* v_a_3277_ = stack[4].m_obj;
lean_object* v_a_3278_ = stack[5].m_obj;
lean_object* v_a_3279_ = stack[6].m_obj;
lean_object* v_a_3280_ = stack[7].m_obj;
lean_object* v_a_3281_ = stack[8].m_obj;
lean_object* v_a_3282_ = stack[9].m_obj;
lean_object* v_res_3329_;
v_res_3329_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
stack->m_obj
 = v_res_3329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec(v_a_3330_);
return v_res_3341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_box(0);
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3351_ = l_Lean_mkConst(v___x_3350_, v___x_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3352_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3354_ = l_Lean_Expr_app___override(v___x_3353_, v_c_3352_);
return v___x_3354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3365_ = l_Lean_mkConst(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = lean_box(0);
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3373_ = l_Lean_mkConst(v___x_3372_, v___x_3371_);
return v___x_3373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_box(0);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3381_ = l_Lean_mkConst(v___x_3380_, v___x_3379_);
return v___x_3381_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; uint8_t v___y_3405_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___x_3454_; 
lean_inc_ref(v_c_3382_);
v___x_3454_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3382_, v_a_3390_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3527_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3527_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3527_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; uint8_t v___x_3460_; 
v___x_3459_ = l_Lean_Expr_cleanupAnnotations(v_a_3455_);
v___x_3460_ = l_Lean_Expr_isApp(v___x_3459_);
if (v___x_3460_ == 0)
{
lean_dec_ref(v___x_3459_);
lean_del_object(v___x_3457_);
v___y_3442_ = v_a_3383_;
v___y_3443_ = v_a_3384_;
v___y_3444_ = v_a_3385_;
v___y_3445_ = v_a_3386_;
v___y_3446_ = v_a_3387_;
v___y_3447_ = v_a_3388_;
v___y_3448_ = v_a_3389_;
v___y_3449_ = v_a_3390_;
v___y_3450_ = v_a_3391_;
v___y_3451_ = v_a_3392_;
goto v___jp_3441_;
}
else
{
lean_object* v_arg_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_arg_3461_ = lean_ctor_get(v___x_3459_, 1);
lean_inc_ref(v_arg_3461_);
v___x_3462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3459_);
v___x_3463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3464_ = l_Lean_Expr_isConstOf(v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
uint8_t v___x_3465_; 
v___x_3465_ = l_Lean_Expr_isApp(v___x_3462_);
if (v___x_3465_ == 0)
{
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_arg_3461_);
lean_del_object(v___x_3457_);
v___y_3442_ = v_a_3383_;
v___y_3443_ = v_a_3384_;
v___y_3444_ = v_a_3385_;
v___y_3445_ = v_a_3386_;
v___y_3446_ = v_a_3387_;
v___y_3447_ = v_a_3388_;
v___y_3448_ = v_a_3389_;
v___y_3449_ = v_a_3390_;
v___y_3450_ = v_a_3391_;
v___y_3451_ = v_a_3392_;
goto v___jp_3441_;
}
else
{
lean_object* v_arg_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v_arg_3466_ = lean_ctor_get(v___x_3462_, 1);
lean_inc_ref(v_arg_3466_);
v___x_3467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3462_);
v___x_3468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3469_ = l_Lean_Expr_isConstOf(v___x_3467_, v___x_3468_);
if (v___x_3469_ == 0)
{
uint8_t v___x_3470_; 
v___x_3470_ = l_Lean_Expr_isApp(v___x_3467_);
if (v___x_3470_ == 0)
{
lean_dec_ref(v___x_3467_);
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
lean_del_object(v___x_3457_);
v___y_3442_ = v_a_3383_;
v___y_3443_ = v_a_3384_;
v___y_3444_ = v_a_3385_;
v___y_3445_ = v_a_3386_;
v___y_3446_ = v_a_3387_;
v___y_3447_ = v_a_3388_;
v___y_3448_ = v_a_3389_;
v___y_3449_ = v_a_3390_;
v___y_3450_ = v_a_3391_;
v___y_3451_ = v_a_3392_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3467_);
v___x_3472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3473_ = l_Lean_Expr_isConstOf(v___x_3471_, v___x_3472_);
lean_dec_ref(v___x_3471_);
if (v___x_3473_ == 0)
{
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
lean_del_object(v___x_3457_);
v___y_3442_ = v_a_3383_;
v___y_3443_ = v_a_3384_;
v___y_3444_ = v_a_3385_;
v___y_3445_ = v_a_3386_;
v___y_3446_ = v_a_3387_;
v___y_3447_ = v_a_3388_;
v___y_3448_ = v_a_3389_;
v___y_3449_ = v_a_3390_;
v___y_3450_ = v_a_3391_;
v___y_3451_ = v_a_3392_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3474_; 
lean_inc_ref(v_c_3382_);
v___x_3474_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3382_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
v___x_3475_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3382_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3475_);
v___x_3477_ = v___x_3457_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
else
{
lean_object* v___x_3479_; 
lean_del_object(v___x_3457_);
lean_inc_ref(v_c_3382_);
v___x_3479_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3382_, v_a_3383_, v_a_3387_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; uint8_t v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = lean_unbox(v_a_3480_);
lean_dec(v_a_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3492_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3488_ = l_Lean_mkApp3(v___x_3487_, v_arg_3466_, v_arg_3461_, v_a_3483_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3488_);
v___x_3490_ = v___x_3485_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
else
{
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
return v___x_3482_;
}
}
else
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3503_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3499_ = l_Lean_mkApp3(v___x_3498_, v_arg_3466_, v_arg_3461_, v_a_3494_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3499_);
v___x_3501_ = v___x_3496_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
return v___x_3493_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
lean_dec_ref(v_c_3382_);
v_a_3504_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3479_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3479_);
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
}
}
else
{
lean_object* v___x_3512_; 
lean_dec_ref(v___x_3467_);
lean_del_object(v___x_3457_);
v___x_3512_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3522_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3522_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3518_ = l_Lean_mkApp3(v___x_3517_, v_arg_3466_, v_arg_3461_, v_a_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3518_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
else
{
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_arg_3461_);
return v___x_3512_;
}
}
}
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_c_3382_);
v___x_3523_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3461_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3523_);
v___x_3525_ = v___x_3457_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3382_);
return v___x_3454_;
}
v___jp_3394_:
{
if (v___y_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_inc_ref(v_c_3382_);
v___x_3406_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3382_, v___y_3397_, v___y_3401_, v___y_3404_, v___y_3396_, v___y_3400_, v___y_3403_);
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
lean_ctor_set(v___x_3409_, 0, v_c_3382_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_c_3382_);
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
lean_inc_ref(v_c_3382_);
v___x_3415_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3382_, v___y_3397_, v___y_3402_, v___y_3399_, v___y_3395_, v___y_3401_, v___y_3398_, v___y_3404_, v___y_3396_, v___y_3400_, v___y_3403_);
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
v___x_3420_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3382_, v_a_3416_);
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
lean_dec_ref(v_c_3382_);
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_c_3382_);
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
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = l_Lean_Expr_getAppNumArgs(v_c_3382_);
v___x_3436_ = lean_nat_sub(v___x_3435_, v___x_3434_);
lean_dec(v___x_3435_);
v___x_3437_ = lean_nat_sub(v___x_3436_, v___x_3434_);
lean_dec(v___x_3436_);
v___x_3438_ = l_Lean_Expr_getRevArg_x21(v_c_3382_, v___x_3437_);
lean_dec_ref(v_c_3382_);
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3438_);
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
return v___x_3440_;
}
}
v___jp_3441_:
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Meta_Grind_isIte(v_c_3382_);
if (v___x_3452_ == 0)
{
uint8_t v___x_3453_; 
v___x_3453_ = l_Lean_Meta_Grind_isDIte(v_c_3382_);
v___y_3395_ = v___y_3445_;
v___y_3396_ = v___y_3449_;
v___y_3397_ = v___y_3442_;
v___y_3398_ = v___y_3447_;
v___y_3399_ = v___y_3444_;
v___y_3400_ = v___y_3450_;
v___y_3401_ = v___y_3446_;
v___y_3402_ = v___y_3443_;
v___y_3403_ = v___y_3451_;
v___y_3404_ = v___y_3448_;
v___y_3405_ = v___x_3453_;
goto v___jp_3394_;
}
else
{
v___y_3395_ = v___y_3445_;
v___y_3396_ = v___y_3449_;
v___y_3397_ = v___y_3442_;
v___y_3398_ = v___y_3447_;
v___y_3399_ = v___y_3444_;
v___y_3400_ = v___y_3450_;
v___y_3401_ = v___y_3446_;
v___y_3402_ = v___y_3443_;
v___y_3403_ = v___y_3451_;
v___y_3404_ = v___y_3448_;
v___y_3405_ = v___x_3452_;
goto v___jp_3394_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3382_ = stack[0].m_obj;
lean_object* v_a_3383_ = stack[1].m_obj;
lean_object* v_a_3384_ = stack[2].m_obj;
lean_object* v_a_3385_ = stack[3].m_obj;
lean_object* v_a_3386_ = stack[4].m_obj;
lean_object* v_a_3387_ = stack[5].m_obj;
lean_object* v_a_3388_ = stack[6].m_obj;
lean_object* v_a_3389_ = stack[7].m_obj;
lean_object* v_a_3390_ = stack[8].m_obj;
lean_object* v_a_3391_ = stack[9].m_obj;
lean_object* v_a_3392_ = stack[10].m_obj;
lean_object* v_res_3528_;
v_res_3528_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
stack->m_obj
 = v_res_3528_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec(v_a_3530_);
return v_res_3541_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3542_, lean_object* v_major_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3544_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; uint8_t v_trace_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_trace_3553_ = lean_ctor_get_uint8(v_a_3552_, sizeof(void*)*14);
lean_dec(v_a_3552_);
if (v_trace_3553_ == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Meta_Grind_cases(v_mvarId_3542_, v_major_3543_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; 
lean_inc(v_a_3549_);
lean_inc_ref(v_a_3548_);
lean_inc(v_a_3547_);
lean_inc_ref(v_a_3546_);
lean_inc_ref(v_major_3543_);
v___x_3555_ = lean_infer_type(v_major_3543_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = l_Lean_Meta_whnfD(v_a_3556_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Expr_getAppFn(v_a_3558_);
lean_dec(v_a_3558_);
if (lean_obj_tag(v___x_3559_) == 4)
{
lean_object* v_declName_3560_; lean_object* v___x_3561_; 
v_declName_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_declName_3560_);
lean_dec_ref_known(v___x_3559_, 2);
v___x_3561_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3560_, v_a_3545_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref_known(v___x_3561_, 1);
v___x_3562_ = l_Lean_Meta_Grind_cases(v_mvarId_3542_, v_major_3543_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3562_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_major_3543_);
lean_dec(v_mvarId_3542_);
v_a_3563_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3561_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3561_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3571_; 
lean_dec_ref(v___x_3559_);
v___x_3571_ = l_Lean_Meta_Grind_cases(v_mvarId_3542_, v_major_3543_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3571_;
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec_ref(v_major_3543_);
lean_dec(v_mvarId_3542_);
v_a_3572_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3557_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3557_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_major_3543_);
lean_dec(v_mvarId_3542_);
v_a_3580_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3555_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3555_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_major_3543_);
lean_dec(v_mvarId_3542_);
v_a_3588_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3551_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3551_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3542_ = stack[0].m_obj;
lean_object* v_major_3543_ = stack[1].m_obj;
lean_object* v_a_3544_ = stack[2].m_obj;
lean_object* v_a_3545_ = stack[3].m_obj;
lean_object* v_a_3546_ = stack[4].m_obj;
lean_object* v_a_3547_ = stack[5].m_obj;
lean_object* v_a_3548_ = stack[6].m_obj;
lean_object* v_a_3549_ = stack[7].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3542_, v_major_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3597_, lean_object* v_major_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3597_, v_major_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3606_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3607_, lean_object* v_major_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3607_, v_major_3608_, v_a_3611_, v_a_3612_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3607_ = stack[0].m_obj;
lean_object* v_major_3608_ = stack[1].m_obj;
lean_object* v_a_3609_ = stack[2].m_obj;
lean_object* v_a_3610_ = stack[3].m_obj;
lean_object* v_a_3611_ = stack[4].m_obj;
lean_object* v_a_3612_ = stack[5].m_obj;
lean_object* v_a_3613_ = stack[6].m_obj;
lean_object* v_a_3614_ = stack[7].m_obj;
lean_object* v_a_3615_ = stack[8].m_obj;
lean_object* v_a_3616_ = stack[9].m_obj;
lean_object* v_a_3617_ = stack[10].m_obj;
lean_object* v_a_3618_ = stack[11].m_obj;
lean_object* v_res_3621_;
v_res_3621_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3607_, v_major_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
stack->m_obj
 = v_res_3621_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3622_, lean_object* v_major_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3622_, v_major_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec(v_a_3624_);
return v_res_3635_;
}
}
uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3636_){
_start:
{
uint64_t v_anchor_3637_; 
v_anchor_3637_ = lean_ctor_get_uint64(v_e_3636_, sizeof(void*)*3);
return v_anchor_3637_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3636_ = stack[0].m_obj;
uint64_t v_res_3638_;
v_res_3638_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3636_);
stack->m_num = v_res_3638_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3639_){
_start:
{
uint64_t v_res_3640_; lean_object* v_r_3641_; 
v_res_3640_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3639_);
lean_dec_ref(v_e_3639_);
v_r_3641_ = lean_box_uint64(v_res_3640_);
return v_r_3641_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3644_, lean_object* v_x_3645_){
_start:
{
if (lean_obj_tag(v_x_3645_) == 0)
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_box(0);
return v___x_3646_;
}
else
{
lean_object* v_key_3647_; lean_object* v_value_3648_; lean_object* v_tail_3649_; uint64_t v___x_3650_; uint8_t v___x_3651_; 
v_key_3647_ = lean_ctor_get(v_x_3645_, 0);
v_value_3648_ = lean_ctor_get(v_x_3645_, 1);
v_tail_3649_ = lean_ctor_get(v_x_3645_, 2);
v___x_3650_ = lean_unbox_uint64(v_key_3647_);
v___x_3651_ = lean_uint64_dec_eq(v___x_3650_, v_a_3644_);
if (v___x_3651_ == 0)
{
v_x_3645_ = v_tail_3649_;
goto _start;
}
else
{
lean_object* v___x_3653_; 
lean_inc(v_value_3648_);
v___x_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_value_3648_);
return v___x_3653_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_3644_ = stack[0].m_num;
lean_object* v_x_3645_ = stack[1].m_obj;
lean_object* v_res_3654_;
v_res_3654_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3644_, v_x_3645_);
stack->m_obj
 = v_res_3654_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3655_, lean_object* v_x_3656_){
_start:
{
uint64_t v_a_boxed_3657_; lean_object* v_res_3658_; 
v_a_boxed_3657_ = lean_unbox_uint64(v_a_3655_);
lean_dec_ref(v_a_3655_);
v_res_3658_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3657_, v_x_3656_);
lean_dec(v_x_3656_);
return v_res_3658_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3659_, uint64_t v_a_3660_){
_start:
{
lean_object* v_buckets_3661_; lean_object* v___x_3662_; uint64_t v___x_3663_; uint64_t v___x_3664_; uint64_t v_fold_3665_; uint64_t v___x_3666_; uint64_t v___x_3667_; uint64_t v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_buckets_3661_ = lean_ctor_get(v_m_3659_, 1);
v___x_3662_ = lean_array_get_size(v_buckets_3661_);
v___x_3663_ = 32ULL;
v___x_3664_ = lean_uint64_shift_right(v_a_3660_, v___x_3663_);
v_fold_3665_ = lean_uint64_xor(v_a_3660_, v___x_3664_);
v___x_3666_ = 16ULL;
v___x_3667_ = lean_uint64_shift_right(v_fold_3665_, v___x_3666_);
v___x_3668_ = lean_uint64_xor(v_fold_3665_, v___x_3667_);
v___x_3669_ = lean_uint64_to_usize(v___x_3668_);
v___x_3670_ = lean_usize_of_nat(v___x_3662_);
v___x_3671_ = ((size_t)1ULL);
v___x_3672_ = lean_usize_sub(v___x_3670_, v___x_3671_);
v___x_3673_ = lean_usize_land(v___x_3669_, v___x_3672_);
v___x_3674_ = lean_array_uget_borrowed(v_buckets_3661_, v___x_3673_);
v___x_3675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3660_, v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3659_ = stack[0].m_obj;
uint64_t v_a_3660_ = stack[1].m_num;
lean_object* v_res_3676_;
v_res_3676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3659_, v_a_3660_);
stack->m_obj
 = v_res_3676_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3677_, lean_object* v_a_3678_){
_start:
{
uint64_t v_a_boxed_3679_; lean_object* v_res_3680_; 
v_a_boxed_3679_ = lean_unbox_uint64(v_a_3678_);
lean_dec_ref(v_a_3678_);
v_res_3680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3677_, v_a_boxed_3679_);
lean_dec_ref(v_m_3677_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3681_, lean_object* v_x_3682_){
_start:
{
if (lean_obj_tag(v_x_3682_) == 0)
{
return v_x_3681_;
}
else
{
lean_object* v_key_3683_; lean_object* v_value_3684_; lean_object* v_tail_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3709_; 
v_key_3683_ = lean_ctor_get(v_x_3682_, 0);
v_value_3684_ = lean_ctor_get(v_x_3682_, 1);
v_tail_3685_ = lean_ctor_get(v_x_3682_, 2);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_x_3682_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3687_ = v_x_3682_;
v_isShared_3688_ = v_isSharedCheck_3709_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_tail_3685_);
lean_inc(v_value_3684_);
lean_inc(v_key_3683_);
lean_dec(v_x_3682_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3709_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; uint64_t v___x_3690_; uint64_t v___x_3691_; uint64_t v___x_3692_; uint64_t v___x_3693_; uint64_t v_fold_3694_; uint64_t v___x_3695_; uint64_t v___x_3696_; uint64_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3689_ = lean_array_get_size(v_x_3681_);
v___x_3690_ = 32ULL;
v___x_3691_ = lean_unbox_uint64(v_key_3683_);
v___x_3692_ = lean_uint64_shift_right(v___x_3691_, v___x_3690_);
v___x_3693_ = lean_unbox_uint64(v_key_3683_);
v_fold_3694_ = lean_uint64_xor(v___x_3693_, v___x_3692_);
v___x_3695_ = 16ULL;
v___x_3696_ = lean_uint64_shift_right(v_fold_3694_, v___x_3695_);
v___x_3697_ = lean_uint64_xor(v_fold_3694_, v___x_3696_);
v___x_3698_ = lean_uint64_to_usize(v___x_3697_);
v___x_3699_ = lean_usize_of_nat(v___x_3689_);
v___x_3700_ = ((size_t)1ULL);
v___x_3701_ = lean_usize_sub(v___x_3699_, v___x_3700_);
v___x_3702_ = lean_usize_land(v___x_3698_, v___x_3701_);
v___x_3703_ = lean_array_uget_borrowed(v_x_3681_, v___x_3702_);
lean_inc(v___x_3703_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 2, v___x_3703_);
v___x_3705_ = v___x_3687_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_key_3683_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_value_3684_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_array_uset(v_x_3681_, v___x_3702_, v___x_3705_);
v_x_3681_ = v___x_3706_;
v_x_3682_ = v_tail_3685_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3710_, lean_object* v_source_3711_, lean_object* v_target_3712_){
_start:
{
lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3713_ = lean_array_get_size(v_source_3711_);
v___x_3714_ = lean_nat_dec_lt(v_i_3710_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_dec_ref(v_source_3711_);
lean_dec(v_i_3710_);
return v_target_3712_;
}
else
{
lean_object* v_es_3715_; lean_object* v___x_3716_; lean_object* v_source_3717_; lean_object* v_target_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_es_3715_ = lean_array_fget(v_source_3711_, v_i_3710_);
v___x_3716_ = lean_box(0);
v_source_3717_ = lean_array_fset(v_source_3711_, v_i_3710_, v___x_3716_);
v_target_3718_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3712_, v_es_3715_);
v___x_3719_ = lean_unsigned_to_nat(1u);
v___x_3720_ = lean_nat_add(v_i_3710_, v___x_3719_);
lean_dec(v_i_3710_);
v_i_3710_ = v___x_3720_;
v_source_3711_ = v_source_3717_;
v_target_3712_ = v_target_3718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3722_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v_nbuckets_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3723_ = lean_array_get_size(v_data_3722_);
v___x_3724_ = lean_unsigned_to_nat(2u);
v_nbuckets_3725_ = lean_nat_mul(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_box(0);
v___x_3728_ = lean_mk_array(v_nbuckets_3725_, v___x_3727_);
v___x_3729_ = lean_array_propagate_mark(v_data_3722_, v___x_3728_);
v___x_3730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3726_, v_data_3722_, v___x_3729_);
return v___x_3730_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3731_, lean_object* v_b_3732_, lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 0)
{
lean_dec(v_b_3732_);
return v_x_3733_;
}
else
{
lean_object* v_key_3734_; lean_object* v_value_3735_; lean_object* v_tail_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3750_; 
v_key_3734_ = lean_ctor_get(v_x_3733_, 0);
v_value_3735_ = lean_ctor_get(v_x_3733_, 1);
v_tail_3736_ = lean_ctor_get(v_x_3733_, 2);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_x_3733_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3738_ = v_x_3733_;
v_isShared_3739_ = v_isSharedCheck_3750_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_tail_3736_);
lean_inc(v_value_3735_);
lean_inc(v_key_3734_);
lean_dec(v_x_3733_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3750_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
uint64_t v___x_3740_; uint8_t v___x_3741_; 
v___x_3740_ = lean_unbox_uint64(v_key_3734_);
v___x_3741_ = lean_uint64_dec_eq(v___x_3740_, v_a_3731_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3742_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3731_, v_b_3732_, v_tail_3736_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 2, v___x_3742_);
v___x_3744_ = v___x_3738_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_key_3734_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_value_3735_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v___x_3742_);
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
lean_object* v___x_3746_; lean_object* v___x_3748_; 
lean_dec(v_value_3735_);
lean_dec(v_key_3734_);
v___x_3746_ = lean_box_uint64(v_a_3731_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 1, v_b_3732_);
lean_ctor_set(v___x_3738_, 0, v___x_3746_);
v___x_3748_ = v___x_3738_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_b_3732_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_tail_3736_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_3731_ = stack[0].m_num;
lean_object* v_b_3732_ = stack[1].m_obj;
lean_object* v_x_3733_ = stack[2].m_obj;
lean_object* v_res_3751_;
v_res_3751_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3731_, v_b_3732_, v_x_3733_);
stack->m_obj
 = v_res_3751_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3752_, lean_object* v_b_3753_, lean_object* v_x_3754_){
_start:
{
uint64_t v_a_boxed_3755_; lean_object* v_res_3756_; 
v_a_boxed_3755_ = lean_unbox_uint64(v_a_3752_);
lean_dec_ref(v_a_3752_);
v_res_3756_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3755_, v_b_3753_, v_x_3754_);
return v_res_3756_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3757_, lean_object* v_x_3758_){
_start:
{
if (lean_obj_tag(v_x_3758_) == 0)
{
uint8_t v___x_3759_; 
v___x_3759_ = 0;
return v___x_3759_;
}
else
{
lean_object* v_key_3760_; lean_object* v_tail_3761_; uint64_t v___x_3762_; uint8_t v___x_3763_; 
v_key_3760_ = lean_ctor_get(v_x_3758_, 0);
v_tail_3761_ = lean_ctor_get(v_x_3758_, 2);
v___x_3762_ = lean_unbox_uint64(v_key_3760_);
v___x_3763_ = lean_uint64_dec_eq(v___x_3762_, v_a_3757_);
if (v___x_3763_ == 0)
{
v_x_3758_ = v_tail_3761_;
goto _start;
}
else
{
return v___x_3763_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_3757_ = stack[0].m_num;
lean_object* v_x_3758_ = stack[1].m_obj;
uint8_t v_res_3765_;
v_res_3765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3757_, v_x_3758_);
stack->m_num = v_res_3765_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3766_, lean_object* v_x_3767_){
_start:
{
uint64_t v_a_boxed_3768_; uint8_t v_res_3769_; lean_object* v_r_3770_; 
v_a_boxed_3768_ = lean_unbox_uint64(v_a_3766_);
lean_dec_ref(v_a_3766_);
v_res_3769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3768_, v_x_3767_);
lean_dec(v_x_3767_);
v_r_3770_ = lean_box(v_res_3769_);
return v_r_3770_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3771_, uint64_t v_a_3772_, lean_object* v_b_3773_){
_start:
{
lean_object* v_size_3774_; lean_object* v_buckets_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3818_; 
v_size_3774_ = lean_ctor_get(v_m_3771_, 0);
v_buckets_3775_ = lean_ctor_get(v_m_3771_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_m_3771_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3777_ = v_m_3771_;
v_isShared_3778_ = v_isSharedCheck_3818_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_buckets_3775_);
lean_inc(v_size_3774_);
lean_dec(v_m_3771_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3818_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3779_; uint64_t v___x_3780_; uint64_t v___x_3781_; uint64_t v_fold_3782_; uint64_t v___x_3783_; uint64_t v___x_3784_; uint64_t v___x_3785_; size_t v___x_3786_; size_t v___x_3787_; size_t v___x_3788_; size_t v___x_3789_; size_t v___x_3790_; lean_object* v_bkt_3791_; uint8_t v___x_3792_; 
v___x_3779_ = lean_array_get_size(v_buckets_3775_);
v___x_3780_ = 32ULL;
v___x_3781_ = lean_uint64_shift_right(v_a_3772_, v___x_3780_);
v_fold_3782_ = lean_uint64_xor(v_a_3772_, v___x_3781_);
v___x_3783_ = 16ULL;
v___x_3784_ = lean_uint64_shift_right(v_fold_3782_, v___x_3783_);
v___x_3785_ = lean_uint64_xor(v_fold_3782_, v___x_3784_);
v___x_3786_ = lean_uint64_to_usize(v___x_3785_);
v___x_3787_ = lean_usize_of_nat(v___x_3779_);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_sub(v___x_3787_, v___x_3788_);
v___x_3790_ = lean_usize_land(v___x_3786_, v___x_3789_);
v_bkt_3791_ = lean_array_uget_borrowed(v_buckets_3775_, v___x_3790_);
v___x_3792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3772_, v_bkt_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v_size_x27_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v_buckets_x27_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3793_ = lean_unsigned_to_nat(1u);
v_size_x27_3794_ = lean_nat_add(v_size_3774_, v___x_3793_);
lean_dec(v_size_3774_);
v___x_3795_ = lean_box_uint64(v_a_3772_);
lean_inc(v_bkt_3791_);
v___x_3796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v_b_3773_);
lean_ctor_set(v___x_3796_, 2, v_bkt_3791_);
v_buckets_x27_3797_ = lean_array_uset(v_buckets_3775_, v___x_3790_, v___x_3796_);
v___x_3798_ = lean_unsigned_to_nat(4u);
v___x_3799_ = lean_nat_mul(v_size_x27_3794_, v___x_3798_);
v___x_3800_ = lean_unsigned_to_nat(3u);
v___x_3801_ = lean_nat_div(v___x_3799_, v___x_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_array_get_size(v_buckets_x27_3797_);
v___x_3803_ = lean_nat_dec_le(v___x_3801_, v___x_3802_);
lean_dec(v___x_3801_);
if (v___x_3803_ == 0)
{
lean_object* v_val_3804_; lean_object* v___x_3806_; 
v_val_3804_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3797_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 1, v_val_3804_);
lean_ctor_set(v___x_3777_, 0, v_size_x27_3794_);
v___x_3806_ = v___x_3777_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_size_x27_3794_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_val_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
else
{
lean_object* v___x_3809_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 1, v_buckets_x27_3797_);
lean_ctor_set(v___x_3777_, 0, v_size_x27_3794_);
v___x_3809_ = v___x_3777_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_size_x27_3794_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_buckets_x27_3797_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v_buckets_x27_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_inc(v_bkt_3791_);
v___x_3811_ = lean_box(0);
v_buckets_x27_3812_ = lean_array_uset(v_buckets_3775_, v___x_3790_, v___x_3811_);
v___x_3813_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3772_, v_b_3773_, v_bkt_3791_);
v___x_3814_ = lean_array_uset(v_buckets_x27_3812_, v___x_3790_, v___x_3813_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 1, v___x_3814_);
v___x_3816_ = v___x_3777_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_size_3774_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3771_ = stack[0].m_obj;
uint64_t v_a_3772_ = stack[1].m_num;
lean_object* v_b_3773_ = stack[2].m_obj;
lean_object* v_res_3819_;
v_res_3819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3771_, v_a_3772_, v_b_3773_);
stack->m_obj
 = v_res_3819_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3820_, lean_object* v_a_3821_, lean_object* v_b_3822_){
_start:
{
uint64_t v_a_boxed_3823_; lean_object* v_res_3824_; 
v_a_boxed_3823_ = lean_unbox_uint64(v_a_3821_);
lean_dec_ref(v_a_3821_);
v_res_3824_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3820_, v_a_boxed_3823_, v_b_3822_);
return v_res_3824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_unsigned_to_nat(16u);
v___x_3827_ = lean_mk_array(v___x_3826_, v___x_3825_);
return v___x_3827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v_found_3830_; 
v___x_3828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3829_ = lean_unsigned_to_nat(0u);
v_found_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3830_, 0, v___x_3829_);
lean_ctor_set(v_found_3830_, 1, v___x_3828_);
return v_found_3830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v_found_3831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3832_ = lean_box(0);
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v_found_3831_);
return v___x_3833_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3834_, lean_object* v_numDigits_3835_, lean_object* v_es_3836_, lean_object* v_as_3837_, size_t v_sz_3838_, size_t v_i_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v_a_3842_; uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3839_, v_sz_3838_);
if (v___x_3846_ == 0)
{
return v_b_3840_;
}
else
{
lean_object* v_snd_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3881_; 
v_snd_3847_ = lean_ctor_get(v_b_3840_, 1);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_b_3840_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v_b_3840_, 0);
lean_dec(v_unused_3882_);
v___x_3849_ = v_b_3840_;
v_isShared_3850_ = v_isSharedCheck_3881_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_snd_3847_);
lean_dec(v_b_3840_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3881_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v_a_3851_; uint64_t v_anchor_3852_; lean_object* v___x_3853_; uint64_t v___x_3854_; uint64_t v___x_3855_; lean_object* v___x_3856_; 
v_a_3851_ = lean_array_uget_borrowed(v_as_3837_, v_i_3839_);
v_anchor_3852_ = lean_ctor_get_uint64(v_a_3851_, sizeof(void*)*3);
v___x_3853_ = lean_box(0);
v___x_3854_ = lean_uint64_of_nat(v_shift_3834_);
v___x_3855_ = lean_uint64_shift_right(v_anchor_3852_, v___x_3854_);
v___x_3856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3847_, v___x_3855_);
if (lean_obj_tag(v___x_3856_) == 1)
{
lean_object* v_val_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3875_; 
v_val_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3875_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_val_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3875_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
uint64_t v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = lean_unbox_uint64(v_val_3857_);
lean_dec(v_val_3857_);
v___x_3862_ = lean_uint64_dec_eq(v___x_3861_, v_anchor_3852_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3863_ = lean_unsigned_to_nat(1u);
v___x_3864_ = lean_nat_add(v_numDigits_3835_, v___x_3863_);
v___x_3865_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3836_, v___x_3864_);
lean_dec(v___x_3864_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3865_);
v___x_3867_ = v___x_3859_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3869_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3867_);
v___x_3869_ = v___x_3849_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_snd_3847_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
else
{
lean_object* v___x_3873_; 
lean_del_object(v___x_3859_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3853_);
v___x_3873_ = v___x_3849_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_snd_3847_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
v_a_3842_ = v___x_3873_;
goto v___jp_3841_;
}
}
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_dec(v___x_3856_);
v___x_3876_ = lean_box_uint64(v_anchor_3852_);
v___x_3877_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3847_, v___x_3855_, v___x_3876_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 1, v___x_3877_);
lean_ctor_set(v___x_3849_, 0, v___x_3853_);
v___x_3879_ = v___x_3849_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
v_a_3842_ = v___x_3879_;
goto v___jp_3841_;
}
}
}
}
v___jp_3841_:
{
size_t v___x_3843_; size_t v___x_3844_; 
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3839_, v___x_3843_);
v_i_3839_ = v___x_3844_;
v_b_3840_ = v_a_3842_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_shift_3834_ = stack[0].m_obj;
lean_object* v_numDigits_3835_ = stack[1].m_obj;
lean_object* v_es_3836_ = stack[2].m_obj;
lean_object* v_as_3837_ = stack[3].m_obj;
size_t v_sz_3838_ = stack[4].m_num;
size_t v_i_3839_ = stack[5].m_num;
lean_object* v_b_3840_ = stack[6].m_obj;
lean_object* v_res_3883_;
v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3834_, v_numDigits_3835_, v_es_3836_, v_as_3837_, v_sz_3838_, v_i_3839_, v_b_3840_);
stack->m_obj
 = v_res_3883_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3884_, lean_object* v_numDigits_3885_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3886_ = lean_unsigned_to_nat(4u);
v___x_3887_ = lean_nat_mul(v___x_3886_, v_numDigits_3885_);
v___x_3888_ = lean_unsigned_to_nat(64u);
v___x_3889_ = lean_nat_dec_lt(v___x_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_dec(v___x_3887_);
lean_inc(v_numDigits_3885_);
return v_numDigits_3885_;
}
else
{
lean_object* v_shift_3890_; lean_object* v___x_3891_; size_t v_sz_3892_; size_t v___x_3893_; lean_object* v___x_3894_; lean_object* v_fst_3895_; 
v_shift_3890_ = lean_nat_sub(v___x_3888_, v___x_3887_);
lean_dec(v___x_3887_);
v___x_3891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3892_ = lean_array_size(v_es_3884_);
v___x_3893_ = ((size_t)0ULL);
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3890_, v_numDigits_3885_, v_es_3884_, v_es_3884_, v_sz_3892_, v___x_3893_, v___x_3891_);
lean_dec(v_shift_3890_);
v_fst_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_fst_3895_);
lean_dec_ref(v___x_3894_);
if (lean_obj_tag(v_fst_3895_) == 0)
{
lean_inc(v_numDigits_3885_);
return v_numDigits_3885_;
}
else
{
lean_object* v_val_3896_; 
v_val_3896_ = lean_ctor_get(v_fst_3895_, 0);
lean_inc(v_val_3896_);
lean_dec_ref_known(v_fst_3895_, 1);
return v_val_3896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3897_, lean_object* v_numDigits_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3897_, v_numDigits_3898_);
lean_dec(v_numDigits_3898_);
lean_dec_ref(v_es_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3900_, lean_object* v_numDigits_3901_, lean_object* v_es_3902_, lean_object* v_as_3903_, lean_object* v_sz_3904_, lean_object* v_i_3905_, lean_object* v_b_3906_){
_start:
{
size_t v_sz_boxed_3907_; size_t v_i_boxed_3908_; lean_object* v_res_3909_; 
v_sz_boxed_3907_ = lean_unbox_usize(v_sz_3904_);
lean_dec(v_sz_3904_);
v_i_boxed_3908_ = lean_unbox_usize(v_i_3905_);
lean_dec(v_i_3905_);
v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3900_, v_numDigits_3901_, v_es_3902_, v_as_3903_, v_sz_boxed_3907_, v_i_boxed_3908_, v_b_3906_);
lean_dec_ref(v_as_3903_);
lean_dec_ref(v_es_3902_);
lean_dec(v_numDigits_3901_);
lean_dec(v_shift_3900_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3910_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_unsigned_to_nat(4u);
v___x_3912_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3910_, v___x_3911_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3913_);
lean_dec_ref(v_es_3913_);
return v_res_3914_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3915_, lean_object* v_as_3916_, size_t v_i_3917_, size_t v_stop_3918_, lean_object* v_b_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_a_3932_; uint8_t v___x_3936_; 
v___x_3936_ = lean_usize_dec_eq(v_i_3917_, v_stop_3918_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v_e_3938_; lean_object* v___x_3939_; 
v___x_3937_ = lean_array_uget_borrowed(v_as_3916_, v_i_3917_);
v_e_3938_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3937_);
v___x_3939_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3937_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
lean_inc(v___x_3937_);
v___x_3941_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3937_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
if (lean_obj_tag(v_a_3942_) == 2)
{
lean_object* v_numCases_3943_; uint8_t v_isRec_3944_; lean_object* v___x_3945_; 
v_numCases_3943_ = lean_ctor_get(v_a_3942_, 0);
lean_inc(v_numCases_3943_);
v_isRec_3944_ = lean_ctor_get_uint8(v_a_3942_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3942_, 1);
lean_inc_ref(v_filter_3915_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc_ref(v___y_3926_);
lean_inc(v___y_3925_);
lean_inc_ref(v___y_3924_);
lean_inc(v___y_3923_);
lean_inc_ref(v___y_3922_);
lean_inc(v___y_3921_);
lean_inc(v___y_3920_);
lean_inc_ref(v_e_3938_);
v___x_3945_ = lean_apply_12(v_filter_3915_, v_e_3938_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, lean_box(0));
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; uint8_t v___x_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
if (v___x_3947_ == 0)
{
lean_dec(v_numCases_3943_);
lean_dec(v_a_3940_);
lean_dec_ref(v_e_3938_);
v_a_3932_ = v_b_3919_;
goto v___jp_3931_;
}
else
{
lean_object* v___x_3948_; uint64_t v___x_3949_; lean_object* v___x_3950_; 
lean_inc(v___x_3937_);
v___x_3948_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3948_, 0, v___x_3937_);
lean_ctor_set(v___x_3948_, 1, v_numCases_3943_);
lean_ctor_set(v___x_3948_, 2, v_e_3938_);
lean_ctor_set_uint8(v___x_3948_, sizeof(void*)*3 + 8, v_isRec_3944_);
v___x_3949_ = lean_unbox_uint64(v_a_3940_);
lean_dec(v_a_3940_);
lean_ctor_set_uint64(v___x_3948_, sizeof(void*)*3, v___x_3949_);
v___x_3950_ = lean_array_push(v_b_3919_, v___x_3948_);
v_a_3932_ = v___x_3950_;
goto v___jp_3931_;
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v_numCases_3943_);
lean_dec(v_a_3940_);
lean_dec_ref(v_e_3938_);
lean_dec_ref(v_b_3919_);
lean_dec_ref(v_filter_3915_);
v_a_3951_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3945_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3945_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_dec(v_a_3942_);
lean_dec(v_a_3940_);
lean_dec_ref(v_e_3938_);
v_a_3932_ = v_b_3919_;
goto v___jp_3931_;
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_a_3940_);
lean_dec_ref(v_e_3938_);
lean_dec_ref(v_b_3919_);
lean_dec_ref(v_filter_3915_);
v_a_3959_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3941_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3941_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v_e_3938_);
lean_dec_ref(v_b_3919_);
lean_dec_ref(v_filter_3915_);
v_a_3967_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3939_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3939_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v___x_3975_; 
lean_dec_ref(v_filter_3915_);
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_b_3919_);
return v___x_3975_;
}
v___jp_3931_:
{
size_t v___x_3933_; size_t v___x_3934_; 
v___x_3933_ = ((size_t)1ULL);
v___x_3934_ = lean_usize_add(v_i_3917_, v___x_3933_);
v_i_3917_ = v___x_3934_;
v_b_3919_ = v_a_3932_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_3915_ = stack[0].m_obj;
lean_object* v_as_3916_ = stack[1].m_obj;
size_t v_i_3917_ = stack[2].m_num;
size_t v_stop_3918_ = stack[3].m_num;
lean_object* v_b_3919_ = stack[4].m_obj;
lean_object* v___y_3920_ = stack[5].m_obj;
lean_object* v___y_3921_ = stack[6].m_obj;
lean_object* v___y_3922_ = stack[7].m_obj;
lean_object* v___y_3923_ = stack[8].m_obj;
lean_object* v___y_3924_ = stack[9].m_obj;
lean_object* v___y_3925_ = stack[10].m_obj;
lean_object* v___y_3926_ = stack[11].m_obj;
lean_object* v___y_3927_ = stack[12].m_obj;
lean_object* v___y_3928_ = stack[13].m_obj;
lean_object* v___y_3929_ = stack[14].m_obj;
lean_object* v_res_3976_;
v_res_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3915_, v_as_3916_, v_i_3917_, v_stop_3918_, v_b_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
stack->m_obj
 = v_res_3976_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3977_, lean_object* v_as_3978_, lean_object* v_i_3979_, lean_object* v_stop_3980_, lean_object* v_b_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_i_boxed_3993_; size_t v_stop_boxed_3994_; lean_object* v_res_3995_; 
v_i_boxed_3993_ = lean_unbox_usize(v_i_3979_);
lean_dec(v_i_3979_);
v_stop_boxed_3994_ = lean_unbox_usize(v_stop_3980_);
lean_dec(v_stop_3980_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3977_, v_as_3978_, v_i_boxed_3993_, v_stop_boxed_3994_, v_b_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v_as_3978_);
return v_res_3995_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3998_, lean_object* v_as_3999_, lean_object* v_start_4000_, lean_object* v_stop_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4013_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_4014_ = lean_nat_dec_lt(v_start_4000_, v_stop_4001_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec_ref(v_filter_3998_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4016_ = lean_array_get_size(v_as_3999_);
v___x_4017_ = lean_nat_dec_le(v_stop_4001_, v___x_4016_);
if (v___x_4017_ == 0)
{
uint8_t v___x_4018_; 
v___x_4018_ = lean_nat_dec_lt(v_start_4000_, v___x_4016_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
lean_dec_ref(v_filter_3998_);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4013_);
return v___x_4019_;
}
else
{
size_t v___x_4020_; size_t v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = lean_usize_of_nat(v_start_4000_);
v___x_4021_ = lean_usize_of_nat(v___x_4016_);
v___x_4022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3998_, v_as_3999_, v___x_4020_, v___x_4021_, v___x_4013_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4022_;
}
}
else
{
size_t v___x_4023_; size_t v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = lean_usize_of_nat(v_start_4000_);
v___x_4024_ = lean_usize_of_nat(v_stop_4001_);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3998_, v_as_3999_, v___x_4023_, v___x_4024_, v___x_4013_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4025_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_3998_ = stack[0].m_obj;
lean_object* v_as_3999_ = stack[1].m_obj;
lean_object* v_start_4000_ = stack[2].m_obj;
lean_object* v_stop_4001_ = stack[3].m_obj;
lean_object* v___y_4002_ = stack[4].m_obj;
lean_object* v___y_4003_ = stack[5].m_obj;
lean_object* v___y_4004_ = stack[6].m_obj;
lean_object* v___y_4005_ = stack[7].m_obj;
lean_object* v___y_4006_ = stack[8].m_obj;
lean_object* v___y_4007_ = stack[9].m_obj;
lean_object* v___y_4008_ = stack[10].m_obj;
lean_object* v___y_4009_ = stack[11].m_obj;
lean_object* v___y_4010_ = stack[12].m_obj;
lean_object* v___y_4011_ = stack[13].m_obj;
lean_object* v_res_4026_;
v_res_4026_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3998_, v_as_3999_, v_start_4000_, v_stop_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
stack->m_obj
 = v_res_4026_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_4027_, lean_object* v_as_4028_, lean_object* v_start_4029_, lean_object* v_stop_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_4027_, v_as_4028_, v_start_4029_, v_stop_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v_stop_4030_);
lean_dec(v_start_4029_);
lean_dec_ref(v_as_4028_);
return v_res_4042_;
}
}
lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_4043_, lean_object* v_candidates_x3f_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_candidates_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; 
if (lean_obj_tag(v_candidates_x3f_4044_) == 0)
{
lean_object* v___x_4090_; lean_object* v_toGoalState_4091_; lean_object* v_split_4092_; lean_object* v_candidates_4093_; 
v___x_4090_ = lean_st_ref_get(v_a_4045_);
v_toGoalState_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc_ref(v_toGoalState_4091_);
lean_dec(v___x_4090_);
v_split_4092_ = lean_ctor_get(v_toGoalState_4091_, 14);
lean_inc_ref(v_split_4092_);
lean_dec_ref(v_toGoalState_4091_);
v_candidates_4093_ = lean_ctor_get(v_split_4092_, 1);
lean_inc(v_candidates_4093_);
lean_dec_ref(v_split_4092_);
v_candidates_4057_ = v_candidates_4093_;
v___y_4058_ = v_a_4045_;
v___y_4059_ = v_a_4046_;
v___y_4060_ = v_a_4047_;
v___y_4061_ = v_a_4048_;
v___y_4062_ = v_a_4049_;
v___y_4063_ = v_a_4050_;
v___y_4064_ = v_a_4051_;
v___y_4065_ = v_a_4052_;
v___y_4066_ = v_a_4053_;
v___y_4067_ = v_a_4054_;
goto v___jp_4056_;
}
else
{
lean_object* v_val_4094_; 
v_val_4094_ = lean_ctor_get(v_candidates_x3f_4044_, 0);
lean_inc(v_val_4094_);
lean_dec_ref_known(v_candidates_x3f_4044_, 1);
v_candidates_4057_ = v_val_4094_;
v___y_4058_ = v_a_4045_;
v___y_4059_ = v_a_4046_;
v___y_4060_ = v_a_4047_;
v___y_4061_ = v_a_4048_;
v___y_4062_ = v_a_4049_;
v___y_4063_ = v_a_4050_;
v___y_4064_ = v_a_4051_;
v___y_4065_ = v_a_4052_;
v___y_4066_ = v_a_4053_;
v___y_4067_ = v_a_4054_;
goto v___jp_4056_;
}
v___jp_4056_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4068_ = lean_array_mk(v_candidates_4057_);
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_array_get_size(v___x_4068_);
v___x_4071_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_4043_, v___x_4068_, v___x_4069_, v___x_4070_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec_ref(v___x_4068_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4081_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4081_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4076_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4072_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4072_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4077_);
v___x_4079_ = v___x_4074_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_a_4082_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4071_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4071_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getSplitCandidateAnchors_0interp(lean_interpreter_value* stack)
{
lean_object* v_filter_4043_ = stack[0].m_obj;
lean_object* v_candidates_x3f_4044_ = stack[1].m_obj;
lean_object* v_a_4045_ = stack[2].m_obj;
lean_object* v_a_4046_ = stack[3].m_obj;
lean_object* v_a_4047_ = stack[4].m_obj;
lean_object* v_a_4048_ = stack[5].m_obj;
lean_object* v_a_4049_ = stack[6].m_obj;
lean_object* v_a_4050_ = stack[7].m_obj;
lean_object* v_a_4051_ = stack[8].m_obj;
lean_object* v_a_4052_ = stack[9].m_obj;
lean_object* v_a_4053_ = stack[10].m_obj;
lean_object* v_a_4054_ = stack[11].m_obj;
lean_object* v_res_4095_;
v_res_4095_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4043_, v_candidates_x3f_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
stack->m_obj
 = v_res_4095_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4096_, lean_object* v_candidates_x3f_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4096_, v_candidates_x3f_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
lean_dec(v_a_4098_);
return v_res_4109_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4110_, lean_object* v_m_4111_, uint64_t v_a_4112_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4111_, v_a_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4111_ = stack[1].m_obj;
uint64_t v_a_4112_ = stack[2].m_num;
lean_object* v_res_4114_;
v_res_4114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_box(0), v_m_4111_, v_a_4112_);
stack->m_obj
 = v_res_4114_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4115_, lean_object* v_m_4116_, lean_object* v_a_4117_){
_start:
{
uint64_t v_a_boxed_4118_; lean_object* v_res_4119_; 
v_a_boxed_4118_ = lean_unbox_uint64(v_a_4117_);
lean_dec_ref(v_a_4117_);
v_res_4119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4115_, v_m_4116_, v_a_boxed_4118_);
lean_dec_ref(v_m_4116_);
return v_res_4119_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4120_, lean_object* v_m_4121_, uint64_t v_a_4122_, lean_object* v_b_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4121_, v_a_4122_, v_b_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4121_ = stack[1].m_obj;
uint64_t v_a_4122_ = stack[2].m_num;
lean_object* v_b_4123_ = stack[3].m_obj;
lean_object* v_res_4125_;
v_res_4125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_box(0), v_m_4121_, v_a_4122_, v_b_4123_);
stack->m_obj
 = v_res_4125_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4126_, lean_object* v_m_4127_, lean_object* v_a_4128_, lean_object* v_b_4129_){
_start:
{
uint64_t v_a_boxed_4130_; lean_object* v_res_4131_; 
v_a_boxed_4130_ = lean_unbox_uint64(v_a_4128_);
lean_dec_ref(v_a_4128_);
v_res_4131_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4126_, v_m_4127_, v_a_boxed_4130_, v_b_4129_);
return v_res_4131_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4132_, uint64_t v_a_4133_, lean_object* v_x_4134_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4133_, v_x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_4133_ = stack[1].m_num;
lean_object* v_x_4134_ = stack[2].m_obj;
lean_object* v_res_4136_;
v_res_4136_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_box(0), v_a_4133_, v_x_4134_);
stack->m_obj
 = v_res_4136_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4137_, lean_object* v_a_4138_, lean_object* v_x_4139_){
_start:
{
uint64_t v_a_boxed_4140_; lean_object* v_res_4141_; 
v_a_boxed_4140_ = lean_unbox_uint64(v_a_4138_);
lean_dec_ref(v_a_4138_);
v_res_4141_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4137_, v_a_boxed_4140_, v_x_4139_);
lean_dec(v_x_4139_);
return v_res_4141_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4142_, uint64_t v_a_4143_, lean_object* v_x_4144_){
_start:
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4143_, v_x_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_4143_ = stack[1].m_num;
lean_object* v_x_4144_ = stack[2].m_obj;
uint8_t v_res_4146_;
v_res_4146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_box(0), v_a_4143_, v_x_4144_);
stack->m_num = v_res_4146_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4147_, lean_object* v_a_4148_, lean_object* v_x_4149_){
_start:
{
uint64_t v_a_boxed_4150_; uint8_t v_res_4151_; lean_object* v_r_4152_; 
v_a_boxed_4150_ = lean_unbox_uint64(v_a_4148_);
lean_dec_ref(v_a_4148_);
v_res_4151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4147_, v_a_boxed_4150_, v_x_4149_);
lean_dec(v_x_4149_);
v_r_4152_ = lean_box(v_res_4151_);
return v_r_4152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4153_, lean_object* v_data_4154_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4154_);
return v___x_4155_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4156_, uint64_t v_a_4157_, lean_object* v_b_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4157_, v_b_4158_, v_x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_4157_ = stack[1].m_num;
lean_object* v_b_4158_ = stack[2].m_obj;
lean_object* v_x_4159_ = stack[3].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_box(0), v_a_4157_, v_b_4158_, v_x_4159_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4162_, lean_object* v_a_4163_, lean_object* v_b_4164_, lean_object* v_x_4165_){
_start:
{
uint64_t v_a_boxed_4166_; lean_object* v_res_4167_; 
v_a_boxed_4166_ = lean_unbox_uint64(v_a_4163_);
lean_dec_ref(v_a_4163_);
v_res_4167_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4162_, v_a_boxed_4166_, v_b_4164_, v_x_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4168_, lean_object* v_i_4169_, lean_object* v_source_4170_, lean_object* v_target_4171_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4169_, v_source_4170_, v_target_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4173_, lean_object* v_x_4174_, lean_object* v_x_4175_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4174_, v_x_4175_);
return v___x_4176_;
}
}
lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = 1;
v___x_4190_ = lean_box(v___x_4189_);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4177_ = stack[0].m_obj;
lean_object* v___y_4178_ = stack[1].m_obj;
lean_object* v___y_4179_ = stack[2].m_obj;
lean_object* v___y_4180_ = stack[3].m_obj;
lean_object* v___y_4181_ = stack[4].m_obj;
lean_object* v___y_4182_ = stack[5].m_obj;
lean_object* v___y_4183_ = stack[6].m_obj;
lean_object* v___y_4184_ = stack[7].m_obj;
lean_object* v___y_4185_ = stack[8].m_obj;
lean_object* v___y_4186_ = stack[9].m_obj;
lean_object* v___y_4187_ = stack[10].m_obj;
lean_object* v_res_4192_;
v_res_4192_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
stack->m_obj
 = v_res_4192_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v_x_4193_);
return v_res_4205_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4206_, uint64_t v_a_4207_, lean_object* v_c_4208_, lean_object* v_numDigits_4209_, lean_object* v_as_4210_, size_t v_sz_4211_, size_t v_i_4212_, lean_object* v_b_4213_){
_start:
{
lean_object* v_a_4216_; uint8_t v___x_4220_; 
v___x_4220_ = lean_usize_dec_lt(v_i_4212_, v_sz_4211_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
lean_dec(v_numDigits_4209_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_b_4213_);
return v___x_4221_;
}
else
{
lean_object* v_snd_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4248_; 
v_snd_4222_ = lean_ctor_get(v_b_4213_, 1);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_b_4213_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; 
v_unused_4249_ = lean_ctor_get(v_b_4213_, 0);
lean_dec(v_unused_4249_);
v___x_4224_ = v_b_4213_;
v_isShared_4225_ = v_isSharedCheck_4248_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_snd_4222_);
lean_dec(v_b_4213_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4248_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_a_4226_; lean_object* v_c_4227_; uint64_t v_anchor_4228_; lean_object* v___x_4229_; uint64_t v___x_4230_; uint64_t v___x_4231_; uint8_t v___x_4232_; 
v_a_4226_ = lean_array_uget_borrowed(v_as_4210_, v_i_4212_);
v_c_4227_ = lean_ctor_get(v_a_4226_, 0);
v_anchor_4228_ = lean_ctor_get_uint64(v_a_4226_, sizeof(void*)*3);
v___x_4229_ = lean_box(0);
v___x_4230_ = lean_uint64_shift_right(v_anchor_4228_, v___x_4206_);
v___x_4231_ = lean_uint64_shift_right(v_a_4207_, v___x_4206_);
v___x_4232_ = lean_uint64_dec_eq(v___x_4230_, v___x_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4234_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4229_);
v___x_4234_ = v___x_4224_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_snd_4222_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
v_a_4216_ = v___x_4234_;
goto v___jp_4215_;
}
}
else
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4227_, v_c_4208_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4237_ = lean_unsigned_to_nat(1u);
v___x_4238_ = lean_nat_add(v_snd_4222_, v___x_4237_);
lean_dec(v_snd_4222_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 1, v___x_4238_);
lean_ctor_set(v___x_4224_, 0, v___x_4229_);
v___x_4240_ = v___x_4224_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
v_a_4216_ = v___x_4240_;
goto v___jp_4215_;
}
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
lean_inc(v_snd_4222_);
v___x_4242_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4242_, 0, v_numDigits_4209_);
lean_ctor_set(v___x_4242_, 1, v_snd_4222_);
lean_ctor_set_uint64(v___x_4242_, sizeof(void*)*2, v_a_4207_);
v___x_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4243_);
v___x_4245_ = v___x_4224_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v_snd_4222_);
v___x_4245_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
}
}
}
v___jp_4215_:
{
size_t v___x_4217_; size_t v___x_4218_; 
v___x_4217_ = ((size_t)1ULL);
v___x_4218_ = lean_usize_add(v_i_4212_, v___x_4217_);
v_i_4212_ = v___x_4218_;
v_b_4213_ = v_a_4216_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_4206_ = stack[0].m_num;
uint64_t v_a_4207_ = stack[1].m_num;
lean_object* v_c_4208_ = stack[2].m_obj;
lean_object* v_numDigits_4209_ = stack[3].m_obj;
lean_object* v_as_4210_ = stack[4].m_obj;
size_t v_sz_4211_ = stack[5].m_num;
size_t v_i_4212_ = stack[6].m_num;
lean_object* v_b_4213_ = stack[7].m_obj;
lean_object* v_res_4250_;
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4206_, v_a_4207_, v_c_4208_, v_numDigits_4209_, v_as_4210_, v_sz_4211_, v_i_4212_, v_b_4213_);
stack->m_obj
 = v_res_4250_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4251_, lean_object* v_a_4252_, lean_object* v_c_4253_, lean_object* v_numDigits_4254_, lean_object* v_as_4255_, lean_object* v_sz_4256_, lean_object* v_i_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_){
_start:
{
uint64_t v___x_7708__boxed_4260_; uint64_t v_a_7709__boxed_4261_; size_t v_sz_boxed_4262_; size_t v_i_boxed_4263_; lean_object* v_res_4264_; 
v___x_7708__boxed_4260_ = lean_unbox_uint64(v___x_4251_);
lean_dec_ref(v___x_4251_);
v_a_7709__boxed_4261_ = lean_unbox_uint64(v_a_4252_);
lean_dec_ref(v_a_4252_);
v_sz_boxed_4262_ = lean_unbox_usize(v_sz_4256_);
lean_dec(v_sz_4256_);
v_i_boxed_4263_ = lean_unbox_usize(v_i_4257_);
lean_dec(v_i_4257_);
v_res_4264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7708__boxed_4260_, v_a_7709__boxed_4261_, v_c_4253_, v_numDigits_4254_, v_as_4255_, v_sz_boxed_4262_, v_i_boxed_4263_, v_b_4258_);
lean_dec_ref(v_as_4255_);
lean_dec_ref(v_c_4253_);
return v_res_4264_;
}
}
lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4269_, lean_object* v_candidates_x3f_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___f_4282_; lean_object* v___x_4283_; 
v___f_4282_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4283_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4282_, v_candidates_x3f_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v_candidates_4285_; lean_object* v_numDigits_4286_; lean_object* v___x_4287_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v_candidates_4285_ = lean_ctor_get(v_a_4284_, 0);
lean_inc_ref(v_candidates_4285_);
v_numDigits_4286_ = lean_ctor_get(v_a_4284_, 1);
lean_inc(v_numDigits_4286_);
lean_dec(v_a_4284_);
v___x_4287_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4269_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; uint64_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; size_t v_sz_4296_; size_t v___x_4297_; uint64_t v___x_4298_; lean_object* v___x_4299_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = lean_unsigned_to_nat(64u);
v___x_4290_ = lean_unsigned_to_nat(4u);
v___x_4291_ = lean_nat_mul(v___x_4290_, v_numDigits_4286_);
v___x_4292_ = lean_nat_sub(v___x_4289_, v___x_4291_);
lean_dec(v___x_4291_);
v___x_4293_ = lean_uint64_of_nat(v___x_4292_);
lean_dec(v___x_4292_);
v___x_4294_ = lean_unsigned_to_nat(0u);
v___x_4295_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4296_ = lean_array_size(v_candidates_4285_);
v___x_4297_ = ((size_t)0ULL);
v___x_4298_ = lean_unbox_uint64(v_a_4288_);
lean_inc(v_numDigits_4286_);
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4293_, v___x_4298_, v_c_4269_, v_numDigits_4286_, v_candidates_4285_, v_sz_4296_, v___x_4297_, v___x_4295_);
lean_dec_ref(v_candidates_4285_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4314_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4314_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4314_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_fst_4304_; 
v_fst_4304_ = lean_ctor_get(v_a_4300_, 0);
lean_inc(v_fst_4304_);
lean_dec(v_a_4300_);
if (lean_obj_tag(v_fst_4304_) == 0)
{
lean_object* v___x_4305_; uint64_t v___x_4306_; lean_object* v___x_4308_; 
v___x_4305_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4305_, 0, v_numDigits_4286_);
lean_ctor_set(v___x_4305_, 1, v___x_4294_);
v___x_4306_ = lean_unbox_uint64(v_a_4288_);
lean_dec(v_a_4288_);
lean_ctor_set_uint64(v___x_4305_, sizeof(void*)*2, v___x_4306_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4305_);
v___x_4308_ = v___x_4302_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4305_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
else
{
lean_object* v_val_4310_; lean_object* v___x_4312_; 
lean_dec(v_a_4288_);
lean_dec(v_numDigits_4286_);
v_val_4310_ = lean_ctor_get(v_fst_4304_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v_fst_4304_, 1);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v_val_4310_);
v___x_4312_ = v___x_4302_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_val_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_a_4288_);
lean_dec(v_numDigits_4286_);
v_a_4315_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4299_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4299_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_numDigits_4286_);
lean_dec_ref(v_candidates_4285_);
v_a_4323_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4287_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4287_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
v_a_4331_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4283_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4283_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkSplitAnchorRefInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4269_ = stack[0].m_obj;
lean_object* v_candidates_x3f_4270_ = stack[1].m_obj;
lean_object* v_a_4271_ = stack[2].m_obj;
lean_object* v_a_4272_ = stack[3].m_obj;
lean_object* v_a_4273_ = stack[4].m_obj;
lean_object* v_a_4274_ = stack[5].m_obj;
lean_object* v_a_4275_ = stack[6].m_obj;
lean_object* v_a_4276_ = stack[7].m_obj;
lean_object* v_a_4277_ = stack[8].m_obj;
lean_object* v_a_4278_ = stack[9].m_obj;
lean_object* v_a_4279_ = stack[10].m_obj;
lean_object* v_a_4280_ = stack[11].m_obj;
lean_object* v_res_4339_;
v_res_4339_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4269_, v_candidates_x3f_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
stack->m_obj
 = v_res_4339_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4340_, lean_object* v_candidates_x3f_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4340_, v_candidates_x3f_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_c_4340_);
return v_res_4353_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4354_, uint64_t v_a_4355_, lean_object* v_c_4356_, lean_object* v_numDigits_4357_, lean_object* v_as_4358_, size_t v_sz_4359_, size_t v_i_4360_, lean_object* v_b_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4354_, v_a_4355_, v_c_4356_, v_numDigits_4357_, v_as_4358_, v_sz_4359_, v_i_4360_, v_b_4361_);
return v___x_4373_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0_0interp(lean_interpreter_value* stack)
{
uint64_t v___x_4354_ = stack[0].m_num;
uint64_t v_a_4355_ = stack[1].m_num;
lean_object* v_c_4356_ = stack[2].m_obj;
lean_object* v_numDigits_4357_ = stack[3].m_obj;
lean_object* v_as_4358_ = stack[4].m_obj;
size_t v_sz_4359_ = stack[5].m_num;
size_t v_i_4360_ = stack[6].m_num;
lean_object* v_b_4361_ = stack[7].m_obj;
lean_object* v___y_4362_ = stack[8].m_obj;
lean_object* v___y_4363_ = stack[9].m_obj;
lean_object* v___y_4364_ = stack[10].m_obj;
lean_object* v___y_4365_ = stack[11].m_obj;
lean_object* v___y_4366_ = stack[12].m_obj;
lean_object* v___y_4367_ = stack[13].m_obj;
lean_object* v___y_4368_ = stack[14].m_obj;
lean_object* v___y_4369_ = stack[15].m_obj;
lean_object* v___y_4370_ = stack[16].m_obj;
lean_object* v___y_4371_ = stack[17].m_obj;
lean_object* v_res_4374_;
v_res_4374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_4354_, v_a_4355_, v_c_4356_, v_numDigits_4357_, v_as_4358_, v_sz_4359_, v_i_4360_, v_b_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
stack->m_obj
 = v_res_4374_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4375_ = _args[0];
lean_object* v_a_4376_ = _args[1];
lean_object* v_c_4377_ = _args[2];
lean_object* v_numDigits_4378_ = _args[3];
lean_object* v_as_4379_ = _args[4];
lean_object* v_sz_4380_ = _args[5];
lean_object* v_i_4381_ = _args[6];
lean_object* v_b_4382_ = _args[7];
lean_object* v___y_4383_ = _args[8];
lean_object* v___y_4384_ = _args[9];
lean_object* v___y_4385_ = _args[10];
lean_object* v___y_4386_ = _args[11];
lean_object* v___y_4387_ = _args[12];
lean_object* v___y_4388_ = _args[13];
lean_object* v___y_4389_ = _args[14];
lean_object* v___y_4390_ = _args[15];
lean_object* v___y_4391_ = _args[16];
lean_object* v___y_4392_ = _args[17];
lean_object* v___y_4393_ = _args[18];
_start:
{
uint64_t v___x_8007__boxed_4394_; uint64_t v_a_8008__boxed_4395_; size_t v_sz_boxed_4396_; size_t v_i_boxed_4397_; lean_object* v_res_4398_; 
v___x_8007__boxed_4394_ = lean_unbox_uint64(v___x_4375_);
lean_dec_ref(v___x_4375_);
v_a_8008__boxed_4395_ = lean_unbox_uint64(v_a_4376_);
lean_dec_ref(v_a_4376_);
v_sz_boxed_4396_ = lean_unbox_usize(v_sz_4380_);
lean_dec(v_sz_4380_);
v_i_boxed_4397_ = lean_unbox_usize(v_i_4381_);
lean_dec(v_i_4381_);
v_res_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_8007__boxed_4394_, v_a_8008__boxed_4395_, v_c_4377_, v_numDigits_4378_, v_as_4379_, v_sz_boxed_4396_, v_i_boxed_4397_, v_b_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v_as_4379_);
lean_dec_ref(v_c_4377_);
return v_res_4398_;
}
}
lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_numDigits_4426_; uint64_t v_anchor_4427_; lean_object* v_ordinal_4428_; lean_object* v___x_4429_; 
v_numDigits_4426_ = lean_ctor_get(v_info_4423_, 0);
v_anchor_4427_ = lean_ctor_get_uint64(v_info_4423_, sizeof(void*)*2);
v_ordinal_4428_ = lean_ctor_get(v_info_4423_, 1);
v___x_4429_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4426_, v_anchor_4427_, v_a_4424_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4466_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4466_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4466_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = lean_nat_dec_eq(v_ordinal_4428_, v___x_4434_);
if (v___x_4435_ == 0)
{
lean_object* v_ref_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v_ref_4436_ = lean_ctor_get(v_a_4424_, 2);
v___x_4437_ = l_Lean_SourceInfo_fromRef(v_ref_4436_, v___x_4435_);
v___x_4438_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4439_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4437_, 3);
v___x_4440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4437_);
lean_ctor_set(v___x_4440_, 1, v___x_4438_);
v___x_4441_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4442_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4437_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
v___x_4444_ = lean_unsigned_to_nat(1u);
v___x_4445_ = lean_nat_add(v_ordinal_4428_, v___x_4444_);
v___x_4446_ = l_Nat_reprFast(v___x_4445_);
v___x_4447_ = lean_box(2);
v___x_4448_ = l_Lean_Syntax_mkNumLit(v___x_4446_, v___x_4447_);
v___x_4449_ = l_Lean_Syntax_node3(v___x_4437_, v___x_4441_, v_a_4430_, v___x_4443_, v___x_4448_);
v___x_4450_ = l_Lean_Syntax_node2(v___x_4437_, v___x_4439_, v___x_4440_, v___x_4449_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4450_);
v___x_4452_ = v___x_4432_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
else
{
lean_object* v_ref_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v_ref_4454_ = lean_ctor_get(v_a_4424_, 2);
v___x_4455_ = 0;
v___x_4456_ = l_Lean_SourceInfo_fromRef(v_ref_4454_, v___x_4455_);
v___x_4457_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4458_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4456_, 2);
v___x_4459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4456_);
lean_ctor_set(v___x_4459_, 1, v___x_4457_);
v___x_4460_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4461_ = l_Lean_Syntax_node1(v___x_4456_, v___x_4460_, v_a_4430_);
v___x_4462_ = l_Lean_Syntax_node2(v___x_4456_, v___x_4458_, v___x_4459_, v___x_4461_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4462_);
v___x_4464_ = v___x_4432_;
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
else
{
return v___x_4429_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_4423_ = stack[0].m_obj;
lean_object* v_a_4424_ = stack[1].m_obj;
lean_object* v_res_4467_;
v_res_4467_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4423_, v_a_4424_);
stack->m_obj
 = v_res_4467_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4468_, v_a_4469_);
lean_dec_ref(v_a_4469_);
lean_dec_ref(v_info_4468_);
return v_res_4471_;
}
}
lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4472_, v_a_4473_);
return v___x_4476_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_4472_ = stack[0].m_obj;
lean_object* v_a_4473_ = stack[1].m_obj;
lean_object* v_a_4474_ = stack[2].m_obj;
lean_object* v_res_4477_;
v_res_4477_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4472_, v_a_4473_, v_a_4474_);
stack->m_obj
 = v_res_4477_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4478_, v_a_4479_, v_a_4480_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec_ref(v_info_4478_);
return v_res_4482_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v_p_4514_; lean_object* v___x_4517_; 
lean_inc_ref(v_proof_4495_);
v___x_4517_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4495_, v_a_4497_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4544_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4544_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4544_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = l_Lean_Expr_cleanupAnnotations(v_a_4518_);
v___x_4523_ = l_Lean_Expr_isApp(v___x_4522_);
if (v___x_4523_ == 0)
{
lean_dec_ref(v___x_4522_);
lean_del_object(v___x_4520_);
v___y_4502_ = v_a_4496_;
v___y_4503_ = v_a_4497_;
v___y_4504_ = v_a_4498_;
v___y_4505_ = v_a_4499_;
goto v___jp_4501_;
}
else
{
lean_object* v_arg_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v_arg_4524_ = lean_ctor_get(v___x_4522_, 1);
lean_inc_ref(v_arg_4524_);
v___x_4525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4522_);
v___x_4526_ = l_Lean_Expr_isApp(v___x_4525_);
if (v___x_4526_ == 0)
{
lean_dec_ref(v___x_4525_);
lean_dec_ref(v_arg_4524_);
lean_del_object(v___x_4520_);
v___y_4502_ = v_a_4496_;
v___y_4503_ = v_a_4497_;
v___y_4504_ = v_a_4498_;
v___y_4505_ = v_a_4499_;
goto v___jp_4501_;
}
else
{
lean_object* v_arg_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v_arg_4527_ = lean_ctor_get(v___x_4525_, 1);
lean_inc_ref(v_arg_4527_);
v___x_4528_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4525_);
v___x_4529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4530_ = l_Lean_Expr_isConstOf(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; uint8_t v___x_4532_; 
lean_dec_ref(v_arg_4527_);
lean_del_object(v___x_4520_);
v___x_4531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4532_ = l_Lean_Expr_isConstOf(v___x_4528_, v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4534_ = l_Lean_Expr_isConstOf(v___x_4528_, v___x_4533_);
lean_dec_ref(v___x_4528_);
if (v___x_4534_ == 0)
{
lean_dec_ref(v_arg_4524_);
v___y_4502_ = v_a_4496_;
v___y_4503_ = v_a_4497_;
v___y_4504_ = v_a_4498_;
v___y_4505_ = v_a_4499_;
goto v___jp_4501_;
}
else
{
lean_dec_ref(v_proof_4495_);
v_p_4514_ = v_arg_4524_;
goto v___jp_4513_;
}
}
else
{
lean_dec_ref(v___x_4528_);
lean_dec_ref(v_proof_4495_);
v_p_4514_ = v_arg_4524_;
goto v___jp_4513_;
}
}
else
{
uint8_t v___x_4535_; 
lean_dec_ref(v___x_4528_);
lean_dec_ref(v_proof_4495_);
v___x_4535_ = l_Lean_Expr_isFalse(v_arg_4527_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
lean_dec_ref(v_arg_4524_);
v___x_4536_ = lean_box(0);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4536_);
v___x_4538_ = v___x_4520_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_arg_4524_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4540_);
v___x_4542_ = v___x_4520_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v_proof_4495_);
v_a_4545_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4517_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4517_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
v___jp_4501_:
{
if (lean_obj_tag(v_proof_4495_) == 6)
{
lean_object* v_body_4506_; uint8_t v___x_4507_; 
v_body_4506_ = lean_ctor_get(v_proof_4495_, 2);
lean_inc_ref(v_body_4506_);
lean_dec_ref_known(v_proof_4495_, 3);
v___x_4507_ = l_Lean_Expr_hasLooseBVars(v_body_4506_);
if (v___x_4507_ == 0)
{
v_proof_4495_ = v_body_4506_;
v_a_4496_ = v___y_4502_;
v_a_4497_ = v___y_4503_;
v_a_4498_ = v___y_4504_;
v_a_4499_ = v___y_4505_;
goto _start;
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref(v_body_4506_);
v___x_4509_ = lean_box(0);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec_ref(v_proof_4495_);
v___x_4511_ = lean_box(0);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
v___jp_4513_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4515_, 0, v_p_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_4495_ = stack[0].m_obj;
lean_object* v_a_4496_ = stack[1].m_obj;
lean_object* v_a_4497_ = stack[2].m_obj;
lean_object* v_a_4498_ = stack[3].m_obj;
lean_object* v_a_4499_ = stack[4].m_obj;
lean_object* v_res_4553_;
v_res_4553_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
stack->m_obj
 = v_res_4553_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
return v_res_4560_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4561_, lean_object* v___y_4562_){
_start:
{
uint8_t v___x_4564_; 
v___x_4564_ = l_Lean_Expr_hasMVar(v_e_4561_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_e_4561_);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; lean_object* v_mctx_4567_; lean_object* v___x_4568_; lean_object* v_fst_4569_; lean_object* v_snd_4570_; lean_object* v___x_4571_; lean_object* v_cache_4572_; lean_object* v_zetaDeltaFVarIds_4573_; lean_object* v_postponed_4574_; lean_object* v_diag_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4584_; 
v___x_4566_ = lean_st_ref_get(v___y_4562_);
v_mctx_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc_ref(v_mctx_4567_);
lean_dec(v___x_4566_);
v___x_4568_ = l_Lean_instantiateMVarsCore(v_mctx_4567_, v_e_4561_);
v_fst_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_fst_4569_);
v_snd_4570_ = lean_ctor_get(v___x_4568_, 1);
lean_inc(v_snd_4570_);
lean_dec_ref(v___x_4568_);
v___x_4571_ = lean_st_ref_take(v___y_4562_);
v_cache_4572_ = lean_ctor_get(v___x_4571_, 1);
v_zetaDeltaFVarIds_4573_ = lean_ctor_get(v___x_4571_, 2);
v_postponed_4574_ = lean_ctor_get(v___x_4571_, 3);
v_diag_4575_ = lean_ctor_get(v___x_4571_, 4);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4584_ == 0)
{
lean_object* v_unused_4585_; 
v_unused_4585_ = lean_ctor_get(v___x_4571_, 0);
lean_dec(v_unused_4585_);
v___x_4577_ = v___x_4571_;
v_isShared_4578_ = v_isSharedCheck_4584_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_diag_4575_);
lean_inc(v_postponed_4574_);
lean_inc(v_zetaDeltaFVarIds_4573_);
lean_inc(v_cache_4572_);
lean_dec(v___x_4571_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4584_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v_snd_4570_);
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_snd_4570_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_cache_4572_);
lean_ctor_set(v_reuseFailAlloc_4583_, 2, v_zetaDeltaFVarIds_4573_);
lean_ctor_set(v_reuseFailAlloc_4583_, 3, v_postponed_4574_);
lean_ctor_set(v_reuseFailAlloc_4583_, 4, v_diag_4575_);
v___x_4580_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = lean_st_ref_put(v___y_4562_, v___x_4580_);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_fst_4569_);
return v___x_4582_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4561_ = stack[0].m_obj;
lean_object* v___y_4562_ = stack[1].m_obj;
lean_object* v_res_4586_;
v_res_4586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4561_, v___y_4562_);
stack->m_obj
 = v_res_4586_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4587_, v___y_4588_);
lean_dec(v___y_4588_);
return v_res_4590_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4591_, v___y_4593_);
return v___x_4597_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4591_ = stack[0].m_obj;
lean_object* v___y_4592_ = stack[1].m_obj;
lean_object* v___y_4593_ = stack[2].m_obj;
lean_object* v___y_4594_ = stack[3].m_obj;
lean_object* v___y_4595_ = stack[4].m_obj;
lean_object* v_res_4598_;
v_res_4598_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
stack->m_obj
 = v_res_4598_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4606_, lean_object* v_x_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4606_, v_x_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
v_a_4622_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4613_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4613_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4606_ = stack[0].m_obj;
lean_object* v_x_4607_ = stack[1].m_obj;
lean_object* v___y_4608_ = stack[2].m_obj;
lean_object* v___y_4609_ = stack[3].m_obj;
lean_object* v___y_4610_ = stack[4].m_obj;
lean_object* v___y_4611_ = stack[5].m_obj;
lean_object* v_res_4630_;
v_res_4630_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4606_, v_x_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
stack->m_obj
 = v_res_4630_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4631_, lean_object* v_x_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4631_, v_x_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
return v_res_4638_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4639_, lean_object* v_mvarId_4640_, lean_object* v_x_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4640_, v_x_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4640_ = stack[1].m_obj;
lean_object* v_x_4641_ = stack[2].m_obj;
lean_object* v___y_4642_ = stack[3].m_obj;
lean_object* v___y_4643_ = stack[4].m_obj;
lean_object* v___y_4644_ = stack[5].m_obj;
lean_object* v___y_4645_ = stack[6].m_obj;
lean_object* v_res_4648_;
v_res_4648_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_box(0), v_mvarId_4640_, v_x_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
stack->m_obj
 = v_res_4648_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4649_, lean_object* v_mvarId_4650_, lean_object* v_x_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4649_, v_mvarId_4650_, v_x_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
return v_res_4657_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4675_; 
v___x_4664_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4658_, v___y_4660_);
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4675_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4675_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
uint8_t v___x_4669_; 
v___x_4669_ = l_Lean_Expr_hasSyntheticSorry(v_a_4665_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
lean_del_object(v___x_4667_);
v___x_4670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4665_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
return v___x_4670_;
}
else
{
lean_object* v___x_4671_; lean_object* v___x_4673_; 
lean_dec(v_a_4665_);
v___x_4671_ = lean_box(0);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v___x_4671_);
v___x_4673_ = v___x_4667_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4658_ = stack[0].m_obj;
lean_object* v___y_4659_ = stack[1].m_obj;
lean_object* v___y_4660_ = stack[2].m_obj;
lean_object* v___y_4661_ = stack[3].m_obj;
lean_object* v___y_4662_ = stack[4].m_obj;
lean_object* v_res_4676_;
v_res_4676_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
stack->m_obj
 = v_res_4676_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
return v_res_4683_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; lean_object* v___f_4691_; lean_object* v___x_4692_; 
lean_inc(v_mvarId_4684_);
v___x_4690_ = l_Lean_mkMVar(v_mvarId_4684_);
v___f_4691_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4691_, 0, v___x_4690_);
v___x_4692_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4684_, v___f_4691_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
return v___x_4692_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4684_ = stack[0].m_obj;
lean_object* v_a_4685_ = stack[1].m_obj;
lean_object* v_a_4686_ = stack[2].m_obj;
lean_object* v_a_4687_ = stack[3].m_obj;
lean_object* v_a_4688_ = stack[4].m_obj;
lean_object* v_res_4693_;
v_res_4693_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
stack->m_obj
 = v_res_4693_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
return v_res_4700_;
}
}
uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4722_){
_start:
{
if (lean_obj_tag(v_x_4722_) == 0)
{
uint8_t v___x_4723_; 
v___x_4723_ = 1;
return v___x_4723_;
}
else
{
lean_object* v_head_4724_; lean_object* v_tail_4725_; uint8_t v___y_4727_; lean_object* v___x_4729_; uint8_t v___x_4730_; 
v_head_4724_ = lean_ctor_get(v_x_4722_, 0);
lean_inc_n(v_head_4724_, 2);
v_tail_4725_ = lean_ctor_get(v_x_4722_, 1);
lean_inc(v_tail_4725_);
lean_dec_ref_known(v_x_4722_, 2);
v___x_4729_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4730_ = l_Lean_Syntax_isOfKind(v_head_4724_, v___x_4729_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4724_);
v___x_4732_ = l_Lean_Syntax_isOfKind(v_head_4724_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_dec(v_head_4724_);
v_x_4722_ = v_tail_4725_;
goto _start;
}
else
{
if (v___x_4730_ == 0)
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = l_Lean_Syntax_getArg(v_head_4724_, v___x_4734_);
lean_dec(v_head_4724_);
v___x_4736_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4737_ = l_Lean_Syntax_isOfKind(v___x_4735_, v___x_4736_);
if (v___x_4737_ == 0)
{
v_x_4722_ = v_tail_4725_;
goto _start;
}
else
{
v___y_4727_ = v___x_4730_;
goto v___jp_4726_;
}
}
else
{
lean_dec(v_head_4724_);
v___y_4727_ = v___x_4730_;
goto v___jp_4726_;
}
}
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4739_ = lean_unsigned_to_nat(3u);
v___x_4740_ = l_Lean_Syntax_getArg(v_head_4724_, v___x_4739_);
lean_dec(v_head_4724_);
v___x_4741_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4742_ = l_Lean_Syntax_isOfKind(v___x_4740_, v___x_4741_);
if (v___x_4742_ == 0)
{
v_x_4722_ = v_tail_4725_;
goto _start;
}
else
{
uint8_t v___x_4744_; 
lean_dec(v_tail_4725_);
v___x_4744_ = 0;
return v___x_4744_;
}
}
v___jp_4726_:
{
if (v___y_4727_ == 0)
{
lean_dec(v_tail_4725_);
return v___y_4727_;
}
else
{
v_x_4722_ = v_tail_4725_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4722_ = stack[0].m_obj;
uint8_t v_res_4745_;
v_res_4745_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4722_);
stack->m_num = v_res_4745_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4746_){
_start:
{
uint8_t v_res_4747_; lean_object* v_r_4748_; 
v_res_4747_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4746_);
v_r_4748_ = lean_box(v_res_4747_);
return v_r_4748_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_4749_ = stack[0].m_obj;
uint8_t v_res_4751_;
v_res_4751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4749_);
stack->m_num = v_res_4751_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4752_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4770_, lean_object* v_a_4771_){
_start:
{
if (lean_obj_tag(v_seq_4770_) == 0)
{
lean_object* v_ref_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v_ref_4773_ = lean_ctor_get(v_a_4771_, 2);
v___x_4774_ = 0;
v___x_4775_ = l_Lean_SourceInfo_fromRef(v_ref_4773_, v___x_4774_);
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4775_);
v___x_4778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4775_);
lean_ctor_set(v___x_4778_, 1, v___x_4776_);
v___x_4779_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4777_, v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
else
{
lean_object* v_tail_4781_; 
v_tail_4781_ = lean_ctor_get(v_seq_4770_, 1);
if (lean_obj_tag(v_tail_4781_) == 0)
{
lean_object* v_head_4782_; lean_object* v___x_4783_; 
v_head_4782_ = lean_ctor_get(v_seq_4770_, 0);
lean_inc(v_head_4782_);
lean_dec_ref_known(v_seq_4770_, 2);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_head_4782_);
return v___x_4783_;
}
else
{
lean_object* v_head_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4806_; 
lean_inc(v_tail_4781_);
v_head_4784_ = lean_ctor_get(v_seq_4770_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_seq_4770_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v_seq_4770_, 1);
lean_dec(v_unused_4807_);
v___x_4786_ = v_seq_4770_;
v_isShared_4787_ = v_isSharedCheck_4806_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_head_4784_);
lean_dec(v_seq_4770_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4806_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4788_; lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4805_; 
v___x_4788_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4781_, v_a_4771_);
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4805_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4805_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v_ref_4793_; uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v_ref_4793_ = lean_ctor_get(v_a_4771_, 2);
v___x_4794_ = 0;
v___x_4795_ = l_Lean_SourceInfo_fromRef(v_ref_4793_, v___x_4794_);
v___x_4796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4795_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 2);
lean_ctor_set(v___x_4786_, 1, v___x_4797_);
lean_ctor_set(v___x_4786_, 0, v___x_4795_);
v___x_4799_ = v___x_4786_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4795_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; lean_object* v___x_4802_; 
v___x_4800_ = l_Lean_Syntax_node3(v___x_4795_, v___x_4796_, v_head_4784_, v___x_4799_, v_a_4789_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4800_);
v___x_4802_ = v___x_4791_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_4770_ = stack[0].m_obj;
lean_object* v_a_4771_ = stack[1].m_obj;
lean_object* v_res_4808_;
v_res_4808_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4770_, v_a_4771_);
stack->m_obj
 = v_res_4808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4809_, v_a_4810_);
lean_dec_ref(v_a_4810_);
return v_res_4812_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4813_, v_a_4814_);
return v___x_4817_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_seq_4813_ = stack[0].m_obj;
lean_object* v_a_4814_ = stack[1].m_obj;
lean_object* v_a_4815_ = stack[2].m_obj;
lean_object* v_res_4818_;
v_res_4818_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4813_, v_a_4814_, v_a_4815_);
stack->m_obj
 = v_res_4818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4819_, v_a_4820_, v_a_4821_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
return v_res_4823_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4824_, lean_object* v_seq_4825_, lean_object* v_a_4826_){
_start:
{
if (lean_obj_tag(v_seq_4825_) == 0)
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4828_, 0, v_cases_4824_);
return v___x_4828_;
}
else
{
lean_object* v___x_4829_; lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4844_; 
v___x_4829_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4825_, v_a_4826_);
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4832_ = v___x_4829_;
v_isShared_4833_ = v_isSharedCheck_4844_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4829_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4844_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_ref_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4842_; 
v_ref_4834_ = lean_ctor_get(v_a_4826_, 2);
v___x_4835_ = 0;
v___x_4836_ = l_Lean_SourceInfo_fromRef(v_ref_4834_, v___x_4835_);
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4836_);
v___x_4839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4836_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
v___x_4840_ = l_Lean_Syntax_node3(v___x_4836_, v___x_4837_, v_cases_4824_, v___x_4839_, v_a_4830_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4840_);
v___x_4842_ = v___x_4832_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cases_4824_ = stack[0].m_obj;
lean_object* v_seq_4825_ = stack[1].m_obj;
lean_object* v_a_4826_ = stack[2].m_obj;
lean_object* v_res_4845_;
v_res_4845_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4824_, v_seq_4825_, v_a_4826_);
stack->m_obj
 = v_res_4845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4846_, lean_object* v_seq_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4846_, v_seq_4847_, v_a_4848_);
lean_dec_ref(v_a_4848_);
return v_res_4850_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4851_, lean_object* v_seq_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4851_, v_seq_4852_, v_a_4853_);
return v___x_4856_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen_0interp(lean_interpreter_value* stack)
{
lean_object* v_cases_4851_ = stack[0].m_obj;
lean_object* v_seq_4852_ = stack[1].m_obj;
lean_object* v_a_4853_ = stack[2].m_obj;
lean_object* v_a_4854_ = stack[3].m_obj;
lean_object* v_res_4857_;
v_res_4857_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4851_, v_seq_4852_, v_a_4853_, v_a_4854_);
stack->m_obj
 = v_res_4857_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4858_, lean_object* v_seq_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4858_, v_seq_4859_, v_a_4860_, v_a_4861_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
return v_res_4863_;
}
}
uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4864_, lean_object* v_x_4865_){
_start:
{
if (lean_obj_tag(v_x_4864_) == 0)
{
if (lean_obj_tag(v_x_4865_) == 0)
{
uint8_t v___x_4866_; 
v___x_4866_ = 1;
return v___x_4866_;
}
else
{
uint8_t v___x_4867_; 
v___x_4867_ = 0;
return v___x_4867_;
}
}
else
{
if (lean_obj_tag(v_x_4865_) == 0)
{
uint8_t v___x_4868_; 
v___x_4868_ = 0;
return v___x_4868_;
}
else
{
lean_object* v_head_4869_; lean_object* v_tail_4870_; lean_object* v_head_4871_; lean_object* v_tail_4872_; uint8_t v___x_4873_; 
v_head_4869_ = lean_ctor_get(v_x_4864_, 0);
v_tail_4870_ = lean_ctor_get(v_x_4864_, 1);
v_head_4871_ = lean_ctor_get(v_x_4865_, 0);
v_tail_4872_ = lean_ctor_get(v_x_4865_, 1);
v___x_4873_ = l_Lean_Syntax_structEq(v_head_4869_, v_head_4871_);
if (v___x_4873_ == 0)
{
return v___x_4873_;
}
else
{
v_x_4864_ = v_tail_4870_;
v_x_4865_ = v_tail_4872_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4864_ = stack[0].m_obj;
lean_object* v_x_4865_ = stack[1].m_obj;
uint8_t v_res_4875_;
v_res_4875_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4864_, v_x_4865_);
stack->m_num = v_res_4875_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4876_, lean_object* v_x_4877_){
_start:
{
uint8_t v_res_4878_; lean_object* v_r_4879_; 
v_res_4878_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4876_, v_x_4877_);
lean_dec(v_x_4877_);
lean_dec(v_x_4876_);
v_r_4879_ = lean_box(v_res_4878_);
return v_r_4879_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4880_, lean_object* v___x_4881_, lean_object* v_as_4882_, size_t v_i_4883_, size_t v_stop_4884_){
_start:
{
uint8_t v___x_4889_; 
v___x_4889_ = lean_usize_dec_eq(v_i_4883_, v_stop_4884_);
if (v___x_4889_ == 0)
{
lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4890_ = lean_array_uget_borrowed(v_as_4882_, v_i_4883_);
v___x_4891_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4890_, v_alt_4880_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = lean_nat_dec_lt(v___x_4892_, v___x_4881_);
if (v___x_4893_ == 0)
{
goto v___jp_4885_;
}
else
{
return v___x_4893_;
}
}
else
{
goto v___jp_4885_;
}
}
else
{
uint8_t v___x_4894_; 
v___x_4894_ = 0;
return v___x_4894_;
}
v___jp_4885_:
{
size_t v___x_4886_; size_t v___x_4887_; 
v___x_4886_ = ((size_t)1ULL);
v___x_4887_ = lean_usize_add(v_i_4883_, v___x_4886_);
v_i_4883_ = v___x_4887_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_4880_ = stack[0].m_obj;
lean_object* v___x_4881_ = stack[1].m_obj;
lean_object* v_as_4882_ = stack[2].m_obj;
size_t v_i_4883_ = stack[3].m_num;
size_t v_stop_4884_ = stack[4].m_num;
uint8_t v_res_4895_;
v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4880_, v___x_4881_, v_as_4882_, v_i_4883_, v_stop_4884_);
stack->m_num = v_res_4895_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4896_, lean_object* v___x_4897_, lean_object* v_as_4898_, lean_object* v_i_4899_, lean_object* v_stop_4900_){
_start:
{
size_t v_i_boxed_4901_; size_t v_stop_boxed_4902_; uint8_t v_res_4903_; lean_object* v_r_4904_; 
v_i_boxed_4901_ = lean_unbox_usize(v_i_4899_);
lean_dec(v_i_4899_);
v_stop_boxed_4902_ = lean_unbox_usize(v_stop_4900_);
lean_dec(v_stop_4900_);
v_res_4903_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4896_, v___x_4897_, v_as_4898_, v_i_boxed_4901_, v_stop_boxed_4902_);
lean_dec_ref(v_as_4898_);
lean_dec(v___x_4897_);
lean_dec(v_alt_4896_);
v_r_4904_ = lean_box(v_res_4903_);
return v_r_4904_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4905_){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; 
v___x_4906_ = lean_unsigned_to_nat(0u);
v___x_4907_ = lean_array_get_size(v_alts_4905_);
v___x_4908_ = lean_nat_dec_lt(v___x_4906_, v___x_4907_);
if (v___x_4908_ == 0)
{
uint8_t v___x_4909_; 
v___x_4909_ = 1;
return v___x_4909_;
}
else
{
lean_object* v_alt_4910_; uint8_t v___x_4911_; 
v_alt_4910_ = lean_array_fget_borrowed(v_alts_4905_, v___x_4906_);
lean_inc(v_alt_4910_);
v___x_4911_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4910_);
if (v___x_4911_ == 0)
{
return v___x_4911_;
}
else
{
if (v___x_4908_ == 0)
{
return v___x_4908_;
}
else
{
if (v___x_4908_ == 0)
{
return v___x_4908_;
}
else
{
size_t v___x_4912_; size_t v___x_4913_; uint8_t v___x_4914_; 
v___x_4912_ = ((size_t)0ULL);
v___x_4913_ = lean_usize_of_nat(v___x_4907_);
v___x_4914_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4910_, v___x_4907_, v_alts_4905_, v___x_4912_, v___x_4913_);
if (v___x_4914_ == 0)
{
return v___x_4908_;
}
else
{
uint8_t v___x_4915_; 
v___x_4915_ = 0;
return v___x_4915_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_4905_ = stack[0].m_obj;
uint8_t v_res_4916_;
v_res_4916_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4905_);
stack->m_num = v_res_4916_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4917_){
_start:
{
uint8_t v_res_4918_; lean_object* v_r_4919_; 
v_res_4918_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4917_);
lean_dec_ref(v_alts_4917_);
v_r_4919_ = lean_box(v_res_4918_);
return v_r_4919_;
}
}
uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4927_){
_start:
{
if (lean_obj_tag(v_alt_4927_) == 1)
{
lean_object* v_tail_4928_; 
v_tail_4928_ = lean_ctor_get(v_alt_4927_, 1);
if (lean_obj_tag(v_tail_4928_) == 0)
{
lean_object* v_head_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; 
v_head_4929_ = lean_ctor_get(v_alt_4927_, 0);
lean_inc(v_head_4929_);
lean_dec_ref_known(v_alt_4927_, 2);
v___x_4930_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4931_ = l_Lean_Syntax_isOfKind(v_head_4929_, v___x_4930_);
return v___x_4931_;
}
else
{
uint8_t v___x_4932_; 
lean_dec_ref_known(v_alt_4927_, 2);
v___x_4932_ = 0;
return v___x_4932_;
}
}
else
{
uint8_t v___x_4933_; 
lean_dec(v_alt_4927_);
v___x_4933_ = 0;
return v___x_4933_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_isSorryAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_4927_ = stack[0].m_obj;
uint8_t v_res_4934_;
v_res_4934_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4927_);
stack->m_num = v_res_4934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4935_){
_start:
{
uint8_t v_res_4936_; lean_object* v_r_4937_; 
v_res_4936_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4935_);
v_r_4937_ = lean_box(v_res_4936_);
return v_r_4937_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4938_, lean_object* v_x_4939_, lean_object* v___y_4940_){
_start:
{
if (lean_obj_tag(v_x_4938_) == 0)
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = l_List_reverse___redArg(v_x_4939_);
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
return v___x_4943_;
}
else
{
lean_object* v_head_4944_; lean_object* v_tail_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4963_; 
v_head_4944_ = lean_ctor_get(v_x_4938_, 0);
v_tail_4945_ = lean_ctor_get(v_x_4938_, 1);
v_isSharedCheck_4963_ = !lean_is_exclusive(v_x_4938_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4947_ = v_x_4938_;
v_isShared_4948_ = v_isSharedCheck_4963_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_tail_4945_);
lean_inc(v_head_4944_);
lean_dec(v_x_4938_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4963_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4944_, v___y_4940_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4949_, 1);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v_x_4939_);
lean_ctor_set(v___x_4947_, 0, v_a_4950_);
v___x_4952_ = v___x_4947_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4950_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v_x_4939_);
v___x_4952_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
v_x_4938_ = v_tail_4945_;
v_x_4939_ = v___x_4952_;
goto _start;
}
}
else
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
lean_del_object(v___x_4947_);
lean_dec(v_tail_4945_);
lean_dec(v_x_4939_);
v_a_4955_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4949_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4949_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
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
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4938_ = stack[0].m_obj;
lean_object* v_x_4939_ = stack[1].m_obj;
lean_object* v___y_4940_ = stack[2].m_obj;
lean_object* v_res_4964_;
v_res_4964_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4938_, v_x_4939_, v___y_4940_);
stack->m_obj
 = v_res_4964_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4965_, lean_object* v_x_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4965_, v_x_4966_, v___y_4967_);
lean_dec_ref(v___y_4967_);
return v_res_4969_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4970_, lean_object* v_alts_4971_, uint8_t v_compress_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v_seq_4977_; 
if (v_compress_4972_ == 0)
{
goto v___jp_4980_;
}
else
{
uint8_t v___x_4990_; 
v___x_4990_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4971_);
if (v___x_4990_ == 0)
{
goto v___jp_4980_;
}
else
{
lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4991_ = lean_unsigned_to_nat(0u);
v___x_4992_ = lean_array_get_size(v_alts_4971_);
v___x_4993_ = lean_nat_dec_lt(v___x_4991_, v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
lean_dec_ref(v_alts_4971_);
v___x_4994_ = lean_box(0);
v___x_4995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4995_, 0, v_cases_4970_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
return v___x_4996_;
}
else
{
lean_object* v___x_4997_; lean_object* v_firstAlt_4998_; uint8_t v___x_4999_; 
v___x_4997_ = lean_box(0);
v_firstAlt_4998_ = lean_array_get(v___x_4997_, v_alts_4971_, v___x_4991_);
lean_dec_ref(v_alts_4971_);
lean_inc(v_firstAlt_4998_);
v___x_4999_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4998_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5009_; 
v___x_5000_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4970_, v_firstAlt_4998_, v_a_4973_);
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5003_ = v___x_5000_;
v_isShared_5004_ = v_isSharedCheck_5009_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_5000_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5009_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5005_, 0, v_a_5001_);
lean_ctor_set(v___x_5005_, 1, v___x_4997_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 0, v___x_5005_);
v___x_5007_ = v___x_5003_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
else
{
lean_object* v___x_5010_; 
lean_dec(v_cases_4970_);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_firstAlt_4998_);
return v___x_5010_;
}
}
}
}
v___jp_4976_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4978_, 0, v_cases_4970_);
lean_ctor_set(v___x_4978_, 1, v_seq_4977_);
v___x_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
v___jp_4980_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4981_ = lean_array_get_size(v_alts_4971_);
v___x_4982_ = lean_unsigned_to_nat(1u);
v___x_4983_ = lean_nat_dec_eq(v___x_4981_, v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4984_ = lean_array_to_list(v_alts_4971_);
v___x_4985_ = lean_box(0);
v___x_4986_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4984_, v___x_4985_, v_a_4973_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v_seq_4977_ = v_a_4987_;
goto v___jp_4976_;
}
else
{
lean_dec(v_cases_4970_);
return v___x_4986_;
}
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = lean_unsigned_to_nat(0u);
v___x_4989_ = lean_array_fget(v_alts_4971_, v___x_4988_);
lean_dec_ref(v_alts_4971_);
v_seq_4977_ = v___x_4989_;
goto v___jp_4976_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cases_4970_ = stack[0].m_obj;
lean_object* v_alts_4971_ = stack[1].m_obj;
uint8_t v_compress_4972_ = stack[2].m_num;
lean_object* v_a_4973_ = stack[3].m_obj;
lean_object* v_a_4974_ = stack[4].m_obj;
lean_object* v_res_5011_;
v_res_5011_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4970_, v_alts_4971_, v_compress_4972_, v_a_4973_, v_a_4974_);
stack->m_obj
 = v_res_5011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_5012_, lean_object* v_alts_5013_, lean_object* v_compress_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_){
_start:
{
uint8_t v_compress_boxed_5018_; lean_object* v_res_5019_; 
v_compress_boxed_5018_ = lean_unbox(v_compress_5014_);
v_res_5019_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_5012_, v_alts_5013_, v_compress_boxed_5018_, v_a_5015_, v_a_5016_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
return v_res_5019_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_5020_, lean_object* v_x_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_5020_, v_x_5021_, v___y_5022_);
return v___x_5025_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5020_ = stack[0].m_obj;
lean_object* v_x_5021_ = stack[1].m_obj;
lean_object* v___y_5022_ = stack[2].m_obj;
lean_object* v___y_5023_ = stack[3].m_obj;
lean_object* v_res_5026_;
v_res_5026_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5020_, v_x_5021_, v___y_5022_, v___y_5023_);
stack->m_obj
 = v_res_5026_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_5027_, lean_object* v_x_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_5027_, v_x_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
return v_res_5032_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v___x_5036_; lean_object* v_env_5037_; uint8_t v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5036_ = lean_st_ref_get(v___y_5034_);
v_env_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc_ref(v_env_5037_);
lean_dec(v___x_5036_);
v___x_5038_ = l_Lean_Meta_isMatcherAppCore(v_env_5037_, v_e_5033_);
v___x_5039_ = lean_box(v___x_5038_);
v___x_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
return v___x_5040_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5033_ = stack[0].m_obj;
lean_object* v___y_5034_ = stack[1].m_obj;
lean_object* v_res_5041_;
v_res_5041_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5033_, v___y_5034_);
stack->m_obj
 = v_res_5041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5042_, v___y_5043_);
lean_dec(v___y_5043_);
lean_dec_ref(v_e_5042_);
return v_res_5045_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_5046_, v___y_5056_);
return v___x_5058_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5046_ = stack[0].m_obj;
lean_object* v___y_5047_ = stack[1].m_obj;
lean_object* v___y_5048_ = stack[2].m_obj;
lean_object* v___y_5049_ = stack[3].m_obj;
lean_object* v___y_5050_ = stack[4].m_obj;
lean_object* v___y_5051_ = stack[5].m_obj;
lean_object* v___y_5052_ = stack[6].m_obj;
lean_object* v___y_5053_ = stack[7].m_obj;
lean_object* v___y_5054_ = stack[8].m_obj;
lean_object* v___y_5055_ = stack[9].m_obj;
lean_object* v___y_5056_ = stack[10].m_obj;
lean_object* v_res_5059_;
v_res_5059_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
stack->m_obj
 = v_res_5059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec(v___y_5061_);
lean_dec_ref(v_e_5060_);
return v_res_5072_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5084_; 
lean_inc(v___y_5078_);
lean_inc_ref(v___y_5077_);
lean_inc(v___y_5076_);
lean_inc_ref(v___y_5075_);
lean_inc(v___y_5074_);
v___x_5084_ = lean_apply_10(v_x_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, lean_box(0));
return v___x_5084_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5073_ = stack[0].m_obj;
lean_object* v___y_5074_ = stack[1].m_obj;
lean_object* v___y_5075_ = stack[2].m_obj;
lean_object* v___y_5076_ = stack[3].m_obj;
lean_object* v___y_5077_ = stack[4].m_obj;
lean_object* v___y_5078_ = stack[5].m_obj;
lean_object* v___y_5079_ = stack[6].m_obj;
lean_object* v___y_5080_ = stack[7].m_obj;
lean_object* v___y_5081_ = stack[8].m_obj;
lean_object* v___y_5082_ = stack[9].m_obj;
lean_object* v_res_5085_;
v_res_5085_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
stack->m_obj
 = v_res_5085_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
return v_res_5097_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_5098_, lean_object* v_x_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v___f_5110_; lean_object* v___x_5111_; 
lean_inc(v___y_5104_);
lean_inc_ref(v___y_5103_);
lean_inc(v___y_5102_);
lean_inc_ref(v___y_5101_);
lean_inc(v___y_5100_);
v___f_5110_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5110_, 0, v_x_5099_);
lean_closure_set(v___f_5110_, 1, v___y_5100_);
lean_closure_set(v___f_5110_, 2, v___y_5101_);
lean_closure_set(v___f_5110_, 3, v___y_5102_);
lean_closure_set(v___f_5110_, 4, v___y_5103_);
lean_closure_set(v___f_5110_, 5, v___y_5104_);
v___x_5111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5098_, v___f_5110_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
if (lean_obj_tag(v___x_5111_) == 0)
{
return v___x_5111_;
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5098_ = stack[0].m_obj;
lean_object* v_x_5099_ = stack[1].m_obj;
lean_object* v___y_5100_ = stack[2].m_obj;
lean_object* v___y_5101_ = stack[3].m_obj;
lean_object* v___y_5102_ = stack[4].m_obj;
lean_object* v___y_5103_ = stack[5].m_obj;
lean_object* v___y_5104_ = stack[6].m_obj;
lean_object* v___y_5105_ = stack[7].m_obj;
lean_object* v___y_5106_ = stack[8].m_obj;
lean_object* v___y_5107_ = stack[9].m_obj;
lean_object* v___y_5108_ = stack[10].m_obj;
lean_object* v_res_5120_;
v_res_5120_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5098_, v_x_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
stack->m_obj
 = v_res_5120_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5121_, lean_object* v_x_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5121_, v_x_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v___y_5123_);
return v_res_5133_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5134_, lean_object* v_mvarId_5135_, lean_object* v_x_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5135_, v_x_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
return v___x_5147_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5135_ = stack[1].m_obj;
lean_object* v_x_5136_ = stack[2].m_obj;
lean_object* v___y_5137_ = stack[3].m_obj;
lean_object* v___y_5138_ = stack[4].m_obj;
lean_object* v___y_5139_ = stack[5].m_obj;
lean_object* v___y_5140_ = stack[6].m_obj;
lean_object* v___y_5141_ = stack[7].m_obj;
lean_object* v___y_5142_ = stack[8].m_obj;
lean_object* v___y_5143_ = stack[9].m_obj;
lean_object* v___y_5144_ = stack[10].m_obj;
lean_object* v___y_5145_ = stack[11].m_obj;
lean_object* v_res_5148_;
v_res_5148_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_box(0), v_mvarId_5135_, v_x_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
stack->m_obj
 = v_res_5148_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5149_, lean_object* v_mvarId_5150_, lean_object* v_x_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5149_, v_mvarId_5150_, v_x_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
return v_res_5162_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5163_, lean_object* v___y_5164_){
_start:
{
uint8_t v___x_5166_; 
v___x_5166_ = l_Lean_Expr_hasMVar(v_e_5163_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v_e_5163_);
return v___x_5167_;
}
else
{
lean_object* v___x_5168_; lean_object* v_mctx_5169_; lean_object* v___x_5170_; lean_object* v_fst_5171_; lean_object* v_snd_5172_; lean_object* v___x_5173_; lean_object* v_cache_5174_; lean_object* v_zetaDeltaFVarIds_5175_; lean_object* v_postponed_5176_; lean_object* v_diag_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5186_; 
v___x_5168_ = lean_st_ref_get(v___y_5164_);
v_mctx_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc_ref(v_mctx_5169_);
lean_dec(v___x_5168_);
v___x_5170_ = l_Lean_instantiateMVarsCore(v_mctx_5169_, v_e_5163_);
v_fst_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_fst_5171_);
v_snd_5172_ = lean_ctor_get(v___x_5170_, 1);
lean_inc(v_snd_5172_);
lean_dec_ref(v___x_5170_);
v___x_5173_ = lean_st_ref_take(v___y_5164_);
v_cache_5174_ = lean_ctor_get(v___x_5173_, 1);
v_zetaDeltaFVarIds_5175_ = lean_ctor_get(v___x_5173_, 2);
v_postponed_5176_ = lean_ctor_get(v___x_5173_, 3);
v_diag_5177_ = lean_ctor_get(v___x_5173_, 4);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5186_ == 0)
{
lean_object* v_unused_5187_; 
v_unused_5187_ = lean_ctor_get(v___x_5173_, 0);
lean_dec(v_unused_5187_);
v___x_5179_ = v___x_5173_;
v_isShared_5180_ = v_isSharedCheck_5186_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_diag_5177_);
lean_inc(v_postponed_5176_);
lean_inc(v_zetaDeltaFVarIds_5175_);
lean_inc(v_cache_5174_);
lean_dec(v___x_5173_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5186_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 0, v_snd_5172_);
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_snd_5172_);
lean_ctor_set(v_reuseFailAlloc_5185_, 1, v_cache_5174_);
lean_ctor_set(v_reuseFailAlloc_5185_, 2, v_zetaDeltaFVarIds_5175_);
lean_ctor_set(v_reuseFailAlloc_5185_, 3, v_postponed_5176_);
lean_ctor_set(v_reuseFailAlloc_5185_, 4, v_diag_5177_);
v___x_5182_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5183_ = lean_st_ref_put(v___y_5164_, v___x_5182_);
v___x_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5184_, 0, v_fst_5171_);
return v___x_5184_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5163_ = stack[0].m_obj;
lean_object* v___y_5164_ = stack[1].m_obj;
lean_object* v_res_5188_;
v_res_5188_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5163_, v___y_5164_);
stack->m_obj
 = v_res_5188_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5189_, v___y_5190_);
lean_dec(v___y_5190_);
return v_res_5192_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5193_, v___y_5200_);
return v___x_5204_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5193_ = stack[0].m_obj;
lean_object* v___y_5194_ = stack[1].m_obj;
lean_object* v___y_5195_ = stack[2].m_obj;
lean_object* v___y_5196_ = stack[3].m_obj;
lean_object* v___y_5197_ = stack[4].m_obj;
lean_object* v___y_5198_ = stack[5].m_obj;
lean_object* v___y_5199_ = stack[6].m_obj;
lean_object* v___y_5200_ = stack[7].m_obj;
lean_object* v___y_5201_ = stack[8].m_obj;
lean_object* v___y_5202_ = stack[9].m_obj;
lean_object* v_res_5205_;
v_res_5205_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
stack->m_obj
 = v_res_5205_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
return v_res_5217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5219_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5220_ = l_Lean_stringToMessageData(v___x_5219_);
return v___x_5220_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5221_, lean_object* v_c_5222_, lean_object* v_a_5223_, lean_object* v_numCases_5224_, uint8_t v_isRec_5225_, lean_object* v_anchorInfo_x3f_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_mvarIds_5239_; lean_object* v___x_5289_; 
v___x_5289_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5221_, v___y_5227_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v___y_5292_; lean_object* v___x_5344_; uint8_t v___x_5347_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_a_5290_);
lean_dec_ref_known(v___x_5289_, 1);
v___x_5344_ = lean_unsigned_to_nat(1u);
v___x_5347_ = lean_nat_dec_lt(v___x_5344_, v_numCases_5224_);
if (v___x_5347_ == 0)
{
if (v_isRec_5225_ == 0)
{
lean_inc(v_a_5290_);
v___y_5292_ = v_a_5290_;
goto v___jp_5291_;
}
else
{
goto v___jp_5345_;
}
}
else
{
goto v___jp_5345_;
}
v___jp_5291_:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5293_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5222_);
lean_inc_ref(v___x_5221_);
v___x_5294_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5221_, v___y_5292_, v_numCases_5224_, v___x_5293_, v___y_5230_, v___y_5233_, v___y_5235_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v___x_5295_; 
lean_dec_ref_known(v___x_5294_, 1);
lean_inc_ref(v___x_5221_);
v___x_5295_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_toCold_5296_; lean_object* v_options_5297_; uint8_t v_hasTrace_5298_; 
lean_dec_ref_known(v___x_5295_, 1);
v_toCold_5296_ = lean_ctor_get(v___y_5235_, 0);
v_options_5297_ = lean_ctor_get(v_toCold_5296_, 2);
v_hasTrace_5298_ = lean_ctor_get_uint8(v_options_5297_, sizeof(void*)*1);
if (v_hasTrace_5298_ == 0)
{
lean_dec(v_a_5290_);
goto v___jp_5242_;
}
else
{
lean_object* v_inheritedTraceOptions_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v_inheritedTraceOptions_5299_ = lean_ctor_get(v_toCold_5296_, 11);
v___x_5300_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5301_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5302_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5299_, v_options_5297_, v___x_5301_);
if (v___x_5302_ == 0)
{
lean_dec(v_a_5290_);
goto v___jp_5242_;
}
else
{
lean_object* v___x_5303_; 
v___x_5303_ = l_Lean_Meta_Grind_updateLastTag(v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
lean_dec_ref_known(v___x_5303_, 1);
lean_inc_ref(v___x_5221_);
v___x_5304_ = l_Lean_MessageData_ofExpr(v___x_5221_);
v___x_5305_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5304_);
lean_ctor_set(v___x_5306_, 1, v___x_5305_);
v___x_5307_ = l_Nat_reprFast(v_a_5290_);
v___x_5308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
v___x_5309_ = l_Lean_MessageData_ofFormat(v___x_5308_);
v___x_5310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5306_);
lean_ctor_set(v___x_5310_, 1, v___x_5309_);
v___x_5311_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5300_, v___x_5310_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_dec_ref_known(v___x_5311_, 1);
goto v___jp_5242_;
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_a_5223_);
lean_dec_ref(v_c_5222_);
lean_dec_ref(v___x_5221_);
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5311_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
lean_dec(v_a_5290_);
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_a_5223_);
lean_dec_ref(v_c_5222_);
lean_dec_ref(v___x_5221_);
v_a_5320_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5303_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5303_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
}
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
lean_dec(v_a_5290_);
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_a_5223_);
lean_dec_ref(v_c_5222_);
lean_dec_ref(v___x_5221_);
v_a_5328_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5295_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_dec(v___x_5295_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
lean_dec(v_a_5290_);
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_a_5223_);
lean_dec_ref(v_c_5222_);
lean_dec_ref(v___x_5221_);
v_a_5336_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5294_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5294_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
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
v___jp_5345_:
{
lean_object* v___x_5346_; 
v___x_5346_ = lean_nat_add(v_a_5290_, v___x_5344_);
v___y_5292_ = v___x_5346_;
goto v___jp_5291_;
}
}
else
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_numCases_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_c_5222_);
lean_dec_ref(v___x_5221_);
v_a_5348_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5289_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5289_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
v___jp_5238_:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5240_, 0, v_mvarIds_5239_);
lean_ctor_set(v___x_5240_, 1, v_anchorInfo_x3f_5226_);
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5240_);
return v___x_5241_;
}
v___jp_5242_:
{
lean_object* v___x_5243_; 
v___x_5243_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5221_, v___y_5236_);
if (lean_obj_tag(v_c_5222_) == 1)
{
lean_object* v_e_5244_; lean_object* v_binderType_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_dec_ref(v___x_5243_);
lean_dec_ref(v___x_5221_);
v_e_5244_ = lean_ctor_get(v_c_5222_, 0);
lean_inc_ref(v_e_5244_);
lean_dec_ref_known(v_c_5222_, 2);
v_binderType_5245_ = lean_ctor_get(v_e_5244_, 1);
lean_inc_ref(v_binderType_5245_);
lean_dec_ref(v_e_5244_);
v___x_5246_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5245_);
v___x_5247_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5223_, v___x_5246_, v___y_5229_, v___y_5230_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v_mvarIds_5239_ = v_a_5248_;
goto v___jp_5238_;
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
lean_dec(v_anchorInfo_x3f_5226_);
v_a_5249_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5247_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5247_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
else
{
lean_object* v_a_5257_; uint8_t v___x_5258_; 
lean_dec_ref(v_c_5222_);
v_a_5257_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5257_);
lean_dec_ref(v___x_5243_);
v___x_5258_ = lean_unbox(v_a_5257_);
lean_dec(v_a_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
v___x_5259_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5259_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5261_; 
v_a_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_a_5260_);
lean_dec_ref_known(v___x_5259_, 1);
v___x_5261_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5223_, v_a_5260_, v___y_5229_, v___y_5230_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; 
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
lean_inc(v_a_5262_);
lean_dec_ref_known(v___x_5261_, 1);
v_mvarIds_5239_ = v_a_5262_;
goto v___jp_5238_;
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_dec(v_anchorInfo_x3f_5226_);
v_a_5263_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5261_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5261_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
else
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5278_; 
lean_dec(v_anchorInfo_x3f_5226_);
lean_dec(v_a_5223_);
v_a_5271_ = lean_ctor_get(v___x_5259_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5259_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5273_ = v___x_5259_;
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v___x_5259_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5276_; 
if (v_isShared_5274_ == 0)
{
v___x_5276_ = v___x_5273_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
v___x_5276_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
return v___x_5276_;
}
}
}
}
else
{
lean_object* v___x_5279_; 
v___x_5279_ = l_Lean_Meta_Grind_casesMatch(v_a_5223_, v___x_5221_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
v_mvarIds_5239_ = v_a_5280_;
goto v___jp_5238_;
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_dec(v_anchorInfo_x3f_5226_);
v_a_5281_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5279_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5279_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5221_ = stack[0].m_obj;
lean_object* v_c_5222_ = stack[1].m_obj;
lean_object* v_a_5223_ = stack[2].m_obj;
lean_object* v_numCases_5224_ = stack[3].m_obj;
uint8_t v_isRec_5225_ = stack[4].m_num;
lean_object* v_anchorInfo_x3f_5226_ = stack[5].m_obj;
lean_object* v___y_5227_ = stack[6].m_obj;
lean_object* v___y_5228_ = stack[7].m_obj;
lean_object* v___y_5229_ = stack[8].m_obj;
lean_object* v___y_5230_ = stack[9].m_obj;
lean_object* v___y_5231_ = stack[10].m_obj;
lean_object* v___y_5232_ = stack[11].m_obj;
lean_object* v___y_5233_ = stack[12].m_obj;
lean_object* v___y_5234_ = stack[13].m_obj;
lean_object* v___y_5235_ = stack[14].m_obj;
lean_object* v___y_5236_ = stack[15].m_obj;
lean_object* v_res_5356_;
v_res_5356_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5221_, v_c_5222_, v_a_5223_, v_numCases_5224_, v_isRec_5225_, v_anchorInfo_x3f_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
stack->m_obj
 = v_res_5356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5357_ = _args[0];
lean_object* v_c_5358_ = _args[1];
lean_object* v_a_5359_ = _args[2];
lean_object* v_numCases_5360_ = _args[3];
lean_object* v_isRec_5361_ = _args[4];
lean_object* v_anchorInfo_x3f_5362_ = _args[5];
lean_object* v___y_5363_ = _args[6];
lean_object* v___y_5364_ = _args[7];
lean_object* v___y_5365_ = _args[8];
lean_object* v___y_5366_ = _args[9];
lean_object* v___y_5367_ = _args[10];
lean_object* v___y_5368_ = _args[11];
lean_object* v___y_5369_ = _args[12];
lean_object* v___y_5370_ = _args[13];
lean_object* v___y_5371_ = _args[14];
lean_object* v___y_5372_ = _args[15];
lean_object* v___y_5373_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5374_; lean_object* v_res_5375_; 
v_isRec_boxed_5374_ = lean_unbox(v_isRec_5361_);
v_res_5375_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5357_, v_c_5358_, v_a_5359_, v_numCases_5360_, v_isRec_boxed_5374_, v_anchorInfo_x3f_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec(v___y_5363_);
return v_res_5375_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5376_, uint8_t v_trace_5377_, lean_object* v___f_5378_, lean_object* v_c_5379_, lean_object* v_candidates_x3f_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v___x_5391_; lean_object* v___y_5393_; 
v___x_5391_ = lean_st_mk_ref(v_goal_5376_);
if (v_trace_5377_ == 0)
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
lean_dec(v_candidates_x3f_5380_);
v___x_5412_ = lean_box(0);
lean_inc(v___x_5391_);
v___x_5413_ = lean_apply_12(v___f_5378_, v___x_5412_, v___x_5391_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, lean_box(0));
v___y_5393_ = v___x_5413_;
goto v___jp_5392_;
}
else
{
lean_object* v___x_5414_; 
v___x_5414_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5379_, v_candidates_x3f_5380_, v___x_5391_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
lean_inc(v_a_5415_);
lean_dec_ref_known(v___x_5414_, 1);
v___x_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5416_, 0, v_a_5415_);
lean_inc(v___x_5391_);
v___x_5417_ = lean_apply_12(v___f_5378_, v___x_5416_, v___x_5391_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, lean_box(0));
v___y_5393_ = v___x_5417_;
goto v___jp_5392_;
}
else
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5425_; 
lean_dec(v___x_5391_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___f_5378_);
v_a_5418_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5420_ = v___x_5414_;
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___x_5414_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5423_; 
if (v_isShared_5421_ == 0)
{
v___x_5423_ = v___x_5420_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5418_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
v___jp_5392_:
{
if (lean_obj_tag(v___y_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5403_; 
v_a_5394_ = lean_ctor_get(v___y_5393_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___y_5393_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5396_ = v___y_5393_;
v_isShared_5397_ = v_isSharedCheck_5403_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___y_5393_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5403_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5401_; 
v___x_5398_ = lean_st_ref_get(v___x_5391_);
lean_dec(v___x_5391_);
v___x_5399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5399_, 0, v_a_5394_);
lean_ctor_set(v___x_5399_, 1, v___x_5398_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v___x_5399_);
v___x_5401_ = v___x_5396_;
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
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v___x_5391_);
v_a_5404_ = lean_ctor_get(v___y_5393_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___y_5393_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___y_5393_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___y_5393_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_5376_ = stack[0].m_obj;
uint8_t v_trace_5377_ = stack[1].m_num;
lean_object* v___f_5378_ = stack[2].m_obj;
lean_object* v_c_5379_ = stack[3].m_obj;
lean_object* v_candidates_x3f_5380_ = stack[4].m_obj;
lean_object* v___y_5381_ = stack[5].m_obj;
lean_object* v___y_5382_ = stack[6].m_obj;
lean_object* v___y_5383_ = stack[7].m_obj;
lean_object* v___y_5384_ = stack[8].m_obj;
lean_object* v___y_5385_ = stack[9].m_obj;
lean_object* v___y_5386_ = stack[10].m_obj;
lean_object* v___y_5387_ = stack[11].m_obj;
lean_object* v___y_5388_ = stack[12].m_obj;
lean_object* v___y_5389_ = stack[13].m_obj;
lean_object* v_res_5426_;
v_res_5426_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5376_, v_trace_5377_, v___f_5378_, v_c_5379_, v_candidates_x3f_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
stack->m_obj
 = v_res_5426_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5427_, lean_object* v_trace_5428_, lean_object* v___f_5429_, lean_object* v_c_5430_, lean_object* v_candidates_x3f_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
uint8_t v_trace_boxed_5442_; lean_object* v_res_5443_; 
v_trace_boxed_5442_ = lean_unbox(v_trace_5428_);
v_res_5443_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5427_, v_trace_boxed_5442_, v___f_5429_, v_c_5430_, v_candidates_x3f_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
lean_dec_ref(v_c_5430_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5444_, lean_object* v_x_5445_, lean_object* v_x_5446_, lean_object* v_x_5447_){
_start:
{
lean_object* v_ks_5448_; lean_object* v_vs_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5473_; 
v_ks_5448_ = lean_ctor_get(v_x_5444_, 0);
v_vs_5449_ = lean_ctor_get(v_x_5444_, 1);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_x_5444_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5451_ = v_x_5444_;
v_isShared_5452_ = v_isSharedCheck_5473_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_vs_5449_);
lean_inc(v_ks_5448_);
lean_dec(v_x_5444_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5473_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; uint8_t v___x_5454_; 
v___x_5453_ = lean_array_get_size(v_ks_5448_);
v___x_5454_ = lean_nat_dec_lt(v_x_5445_, v___x_5453_);
if (v___x_5454_ == 0)
{
lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5458_; 
lean_dec(v_x_5445_);
v___x_5455_ = lean_array_push(v_ks_5448_, v_x_5446_);
v___x_5456_ = lean_array_push(v_vs_5449_, v_x_5447_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 1, v___x_5456_);
lean_ctor_set(v___x_5451_, 0, v___x_5455_);
v___x_5458_ = v___x_5451_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5455_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v___x_5456_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
else
{
lean_object* v_k_x27_5460_; uint8_t v___x_5461_; 
v_k_x27_5460_ = lean_array_fget_borrowed(v_ks_5448_, v_x_5445_);
v___x_5461_ = l_Lean_instBEqMVarId_beq(v_x_5446_, v_k_x27_5460_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5463_; 
if (v_isShared_5452_ == 0)
{
v___x_5463_ = v___x_5451_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_ks_5448_);
lean_ctor_set(v_reuseFailAlloc_5467_, 1, v_vs_5449_);
v___x_5463_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5464_ = lean_unsigned_to_nat(1u);
v___x_5465_ = lean_nat_add(v_x_5445_, v___x_5464_);
lean_dec(v_x_5445_);
v_x_5444_ = v___x_5463_;
v_x_5445_ = v___x_5465_;
goto _start;
}
}
else
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5471_; 
v___x_5468_ = lean_array_fset(v_ks_5448_, v_x_5445_, v_x_5446_);
v___x_5469_ = lean_array_fset(v_vs_5449_, v_x_5445_, v_x_5447_);
lean_dec(v_x_5445_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 1, v___x_5469_);
lean_ctor_set(v___x_5451_, 0, v___x_5468_);
v___x_5471_ = v___x_5451_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v___x_5469_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5474_, lean_object* v_k_5475_, lean_object* v_v_5476_){
_start:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5477_ = lean_unsigned_to_nat(0u);
v___x_5478_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5474_, v___x_5477_, v_k_5475_, v_v_5476_);
return v___x_5478_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5479_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5480_, size_t v_x_5481_, size_t v_x_5482_, lean_object* v_x_5483_, lean_object* v_x_5484_){
_start:
{
if (lean_obj_tag(v_x_5480_) == 0)
{
lean_object* v_es_5485_; size_t v___x_5486_; size_t v___x_5487_; lean_object* v_j_5488_; lean_object* v___x_5489_; uint8_t v___x_5490_; 
v_es_5485_ = lean_ctor_get(v_x_5480_, 0);
v___x_5486_ = ((size_t)31ULL);
v___x_5487_ = lean_usize_land(v_x_5481_, v___x_5486_);
v_j_5488_ = lean_usize_to_nat(v___x_5487_);
v___x_5489_ = lean_array_get_size(v_es_5485_);
v___x_5490_ = lean_nat_dec_lt(v_j_5488_, v___x_5489_);
if (v___x_5490_ == 0)
{
lean_dec(v_j_5488_);
lean_dec(v_x_5484_);
lean_dec(v_x_5483_);
return v_x_5480_;
}
else
{
lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5529_; 
lean_inc_ref(v_es_5485_);
v_isSharedCheck_5529_ = !lean_is_exclusive(v_x_5480_);
if (v_isSharedCheck_5529_ == 0)
{
lean_object* v_unused_5530_; 
v_unused_5530_ = lean_ctor_get(v_x_5480_, 0);
lean_dec(v_unused_5530_);
v___x_5492_ = v_x_5480_;
v_isShared_5493_ = v_isSharedCheck_5529_;
goto v_resetjp_5491_;
}
else
{
lean_dec(v_x_5480_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5529_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v_v_5494_; lean_object* v___x_5495_; lean_object* v_xs_x27_5496_; lean_object* v___y_5498_; 
v_v_5494_ = lean_array_fget(v_es_5485_, v_j_5488_);
v___x_5495_ = lean_box(0);
v_xs_x27_5496_ = lean_array_fset(v_es_5485_, v_j_5488_, v___x_5495_);
switch(lean_obj_tag(v_v_5494_))
{
case 0:
{
lean_object* v_key_5503_; lean_object* v_val_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5514_; 
v_key_5503_ = lean_ctor_get(v_v_5494_, 0);
v_val_5504_ = lean_ctor_get(v_v_5494_, 1);
v_isSharedCheck_5514_ = !lean_is_exclusive(v_v_5494_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5506_ = v_v_5494_;
v_isShared_5507_ = v_isSharedCheck_5514_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_val_5504_);
lean_inc(v_key_5503_);
lean_dec(v_v_5494_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5514_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
uint8_t v___x_5508_; 
v___x_5508_ = l_Lean_instBEqMVarId_beq(v_x_5483_, v_key_5503_);
if (v___x_5508_ == 0)
{
lean_object* v___x_5509_; lean_object* v___x_5510_; 
lean_del_object(v___x_5506_);
v___x_5509_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5503_, v_val_5504_, v_x_5483_, v_x_5484_);
v___x_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5510_, 0, v___x_5509_);
v___y_5498_ = v___x_5510_;
goto v___jp_5497_;
}
else
{
lean_object* v___x_5512_; 
lean_dec(v_val_5504_);
lean_dec(v_key_5503_);
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 1, v_x_5484_);
lean_ctor_set(v___x_5506_, 0, v_x_5483_);
v___x_5512_ = v___x_5506_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_x_5483_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_x_5484_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
v___y_5498_ = v___x_5512_;
goto v___jp_5497_;
}
}
}
}
case 1:
{
lean_object* v_node_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5527_; 
v_node_5515_ = lean_ctor_get(v_v_5494_, 0);
v_isSharedCheck_5527_ = !lean_is_exclusive(v_v_5494_);
if (v_isSharedCheck_5527_ == 0)
{
v___x_5517_ = v_v_5494_;
v_isShared_5518_ = v_isSharedCheck_5527_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_node_5515_);
lean_dec(v_v_5494_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5527_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
size_t v___x_5519_; size_t v___x_5520_; size_t v___x_5521_; size_t v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5525_; 
v___x_5519_ = ((size_t)5ULL);
v___x_5520_ = lean_usize_shift_right(v_x_5481_, v___x_5519_);
v___x_5521_ = ((size_t)1ULL);
v___x_5522_ = lean_usize_add(v_x_5482_, v___x_5521_);
v___x_5523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5515_, v___x_5520_, v___x_5522_, v_x_5483_, v_x_5484_);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 0, v___x_5523_);
v___x_5525_ = v___x_5517_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
v___y_5498_ = v___x_5525_;
goto v___jp_5497_;
}
}
}
default: 
{
lean_object* v___x_5528_; 
v___x_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5528_, 0, v_x_5483_);
lean_ctor_set(v___x_5528_, 1, v_x_5484_);
v___y_5498_ = v___x_5528_;
goto v___jp_5497_;
}
}
v___jp_5497_:
{
lean_object* v___x_5499_; lean_object* v___x_5501_; 
v___x_5499_ = lean_array_fset(v_xs_x27_5496_, v_j_5488_, v___y_5498_);
lean_dec(v_j_5488_);
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 0, v___x_5499_);
v___x_5501_ = v___x_5492_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5499_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
}
}
else
{
lean_object* v_ks_5531_; lean_object* v_vs_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5550_; 
v_ks_5531_ = lean_ctor_get(v_x_5480_, 0);
v_vs_5532_ = lean_ctor_get(v_x_5480_, 1);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_x_5480_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5534_ = v_x_5480_;
v_isShared_5535_ = v_isSharedCheck_5550_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_vs_5532_);
lean_inc(v_ks_5531_);
lean_dec(v_x_5480_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5550_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_ks_5531_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_vs_5532_);
v___x_5537_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v_newNode_5538_; size_t v___x_5539_; uint8_t v___x_5540_; 
v_newNode_5538_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5537_, v_x_5483_, v_x_5484_);
v___x_5539_ = ((size_t)7ULL);
v___x_5540_ = lean_usize_dec_le(v___x_5539_, v_x_5482_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; lean_object* v___x_5542_; uint8_t v___x_5543_; 
v___x_5541_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5538_);
v___x_5542_ = lean_unsigned_to_nat(4u);
v___x_5543_ = lean_nat_dec_lt(v___x_5541_, v___x_5542_);
lean_dec(v___x_5541_);
if (v___x_5543_ == 0)
{
lean_object* v_ks_5544_; lean_object* v_vs_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v_ks_5544_ = lean_ctor_get(v_newNode_5538_, 0);
lean_inc_ref(v_ks_5544_);
v_vs_5545_ = lean_ctor_get(v_newNode_5538_, 1);
lean_inc_ref(v_vs_5545_);
lean_dec_ref(v_newNode_5538_);
v___x_5546_ = lean_unsigned_to_nat(0u);
v___x_5547_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5482_, v_ks_5544_, v_vs_5545_, v___x_5546_, v___x_5547_);
lean_dec_ref(v_vs_5545_);
lean_dec_ref(v_ks_5544_);
return v___x_5548_;
}
else
{
return v_newNode_5538_;
}
}
else
{
return v_newNode_5538_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5480_ = stack[0].m_obj;
size_t v_x_5481_ = stack[1].m_num;
size_t v_x_5482_ = stack[2].m_num;
lean_object* v_x_5483_ = stack[3].m_obj;
lean_object* v_x_5484_ = stack[4].m_obj;
lean_object* v_res_5551_;
v_res_5551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5480_, v_x_5481_, v_x_5482_, v_x_5483_, v_x_5484_);
stack->m_obj
 = v_res_5551_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5552_, lean_object* v_keys_5553_, lean_object* v_vals_5554_, lean_object* v_i_5555_, lean_object* v_entries_5556_){
_start:
{
lean_object* v___x_5557_; uint8_t v___x_5558_; 
v___x_5557_ = lean_array_get_size(v_keys_5553_);
v___x_5558_ = lean_nat_dec_lt(v_i_5555_, v___x_5557_);
if (v___x_5558_ == 0)
{
lean_dec(v_i_5555_);
return v_entries_5556_;
}
else
{
lean_object* v_k_5559_; lean_object* v_v_5560_; uint64_t v___x_5561_; size_t v_h_5562_; size_t v___x_5563_; lean_object* v___x_5564_; size_t v___x_5565_; size_t v___x_5566_; size_t v___x_5567_; size_t v_h_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; 
v_k_5559_ = lean_array_fget_borrowed(v_keys_5553_, v_i_5555_);
v_v_5560_ = lean_array_fget_borrowed(v_vals_5554_, v_i_5555_);
v___x_5561_ = l_Lean_instHashableMVarId_hash(v_k_5559_);
v_h_5562_ = lean_uint64_to_usize(v___x_5561_);
v___x_5563_ = ((size_t)5ULL);
v___x_5564_ = lean_unsigned_to_nat(1u);
v___x_5565_ = ((size_t)1ULL);
v___x_5566_ = lean_usize_sub(v_depth_5552_, v___x_5565_);
v___x_5567_ = lean_usize_mul(v___x_5563_, v___x_5566_);
v_h_5568_ = lean_usize_shift_right(v_h_5562_, v___x_5567_);
v___x_5569_ = lean_nat_add(v_i_5555_, v___x_5564_);
lean_dec(v_i_5555_);
lean_inc(v_v_5560_);
lean_inc(v_k_5559_);
v___x_5570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5556_, v_h_5568_, v_depth_5552_, v_k_5559_, v_v_5560_);
v_i_5555_ = v___x_5569_;
v_entries_5556_ = v___x_5570_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_5552_ = stack[0].m_num;
lean_object* v_keys_5553_ = stack[1].m_obj;
lean_object* v_vals_5554_ = stack[2].m_obj;
lean_object* v_i_5555_ = stack[3].m_obj;
lean_object* v_entries_5556_ = stack[4].m_obj;
lean_object* v_res_5572_;
v_res_5572_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_5552_, v_keys_5553_, v_vals_5554_, v_i_5555_, v_entries_5556_);
stack->m_obj
 = v_res_5572_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5573_, lean_object* v_keys_5574_, lean_object* v_vals_5575_, lean_object* v_i_5576_, lean_object* v_entries_5577_){
_start:
{
size_t v_depth_boxed_5578_; lean_object* v_res_5579_; 
v_depth_boxed_5578_ = lean_unbox_usize(v_depth_5573_);
lean_dec(v_depth_5573_);
v_res_5579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5578_, v_keys_5574_, v_vals_5575_, v_i_5576_, v_entries_5577_);
lean_dec_ref(v_vals_5575_);
lean_dec_ref(v_keys_5574_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5580_, lean_object* v_x_5581_, lean_object* v_x_5582_, lean_object* v_x_5583_, lean_object* v_x_5584_){
_start:
{
size_t v_x_67301__boxed_5585_; size_t v_x_67302__boxed_5586_; lean_object* v_res_5587_; 
v_x_67301__boxed_5585_ = lean_unbox_usize(v_x_5581_);
lean_dec(v_x_5581_);
v_x_67302__boxed_5586_ = lean_unbox_usize(v_x_5582_);
lean_dec(v_x_5582_);
v_res_5587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5580_, v_x_67301__boxed_5585_, v_x_67302__boxed_5586_, v_x_5583_, v_x_5584_);
return v_res_5587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5588_, lean_object* v_x_5589_, lean_object* v_x_5590_){
_start:
{
uint64_t v___x_5591_; size_t v___x_5592_; size_t v___x_5593_; lean_object* v___x_5594_; 
v___x_5591_ = l_Lean_instHashableMVarId_hash(v_x_5589_);
v___x_5592_ = lean_uint64_to_usize(v___x_5591_);
v___x_5593_ = ((size_t)1ULL);
v___x_5594_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5588_, v___x_5592_, v___x_5593_, v_x_5589_, v_x_5590_);
return v___x_5594_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5595_, lean_object* v_val_5596_, lean_object* v___y_5597_){
_start:
{
lean_object* v___x_5599_; lean_object* v_mctx_5600_; lean_object* v_cache_5601_; lean_object* v_zetaDeltaFVarIds_5602_; lean_object* v_postponed_5603_; lean_object* v_diag_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5634_; 
v___x_5599_ = lean_st_ref_take(v___y_5597_);
v_mctx_5600_ = lean_ctor_get(v___x_5599_, 0);
v_cache_5601_ = lean_ctor_get(v___x_5599_, 1);
v_zetaDeltaFVarIds_5602_ = lean_ctor_get(v___x_5599_, 2);
v_postponed_5603_ = lean_ctor_get(v___x_5599_, 3);
v_diag_5604_ = lean_ctor_get(v___x_5599_, 4);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5606_ = v___x_5599_;
v_isShared_5607_ = v_isSharedCheck_5634_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_diag_5604_);
lean_inc(v_postponed_5603_);
lean_inc(v_zetaDeltaFVarIds_5602_);
lean_inc(v_cache_5601_);
lean_inc(v_mctx_5600_);
lean_dec(v___x_5599_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5634_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v_depth_5608_; lean_object* v_levelAssignDepth_5609_; lean_object* v_lmvarCounter_5610_; lean_object* v_mvarCounter_5611_; lean_object* v_lDecls_5612_; lean_object* v_decls_5613_; lean_object* v_userNames_5614_; lean_object* v_lAssignment_5615_; lean_object* v_eAssignment_5616_; lean_object* v_dAssignment_5617_; lean_object* v_instanceTypedMVars_5618_; lean_object* v_synthNormMemo_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5633_; 
v_depth_5608_ = lean_ctor_get(v_mctx_5600_, 0);
v_levelAssignDepth_5609_ = lean_ctor_get(v_mctx_5600_, 1);
v_lmvarCounter_5610_ = lean_ctor_get(v_mctx_5600_, 2);
v_mvarCounter_5611_ = lean_ctor_get(v_mctx_5600_, 3);
v_lDecls_5612_ = lean_ctor_get(v_mctx_5600_, 4);
v_decls_5613_ = lean_ctor_get(v_mctx_5600_, 5);
v_userNames_5614_ = lean_ctor_get(v_mctx_5600_, 6);
v_lAssignment_5615_ = lean_ctor_get(v_mctx_5600_, 7);
v_eAssignment_5616_ = lean_ctor_get(v_mctx_5600_, 8);
v_dAssignment_5617_ = lean_ctor_get(v_mctx_5600_, 9);
v_instanceTypedMVars_5618_ = lean_ctor_get(v_mctx_5600_, 10);
v_synthNormMemo_5619_ = lean_ctor_get(v_mctx_5600_, 11);
v_isSharedCheck_5633_ = !lean_is_exclusive(v_mctx_5600_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5621_ = v_mctx_5600_;
v_isShared_5622_ = v_isSharedCheck_5633_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_synthNormMemo_5619_);
lean_inc(v_instanceTypedMVars_5618_);
lean_inc(v_dAssignment_5617_);
lean_inc(v_eAssignment_5616_);
lean_inc(v_lAssignment_5615_);
lean_inc(v_userNames_5614_);
lean_inc(v_decls_5613_);
lean_inc(v_lDecls_5612_);
lean_inc(v_mvarCounter_5611_);
lean_inc(v_lmvarCounter_5610_);
lean_inc(v_levelAssignDepth_5609_);
lean_inc(v_depth_5608_);
lean_dec(v_mctx_5600_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5633_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___x_5623_ = lean_box(0);
v___x_5624_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5616_, v_mvarId_5595_, v_val_5596_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 8, v___x_5624_);
v___x_5626_ = v___x_5621_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_depth_5608_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_levelAssignDepth_5609_);
lean_ctor_set(v_reuseFailAlloc_5632_, 2, v_lmvarCounter_5610_);
lean_ctor_set(v_reuseFailAlloc_5632_, 3, v_mvarCounter_5611_);
lean_ctor_set(v_reuseFailAlloc_5632_, 4, v_lDecls_5612_);
lean_ctor_set(v_reuseFailAlloc_5632_, 5, v_decls_5613_);
lean_ctor_set(v_reuseFailAlloc_5632_, 6, v_userNames_5614_);
lean_ctor_set(v_reuseFailAlloc_5632_, 7, v_lAssignment_5615_);
lean_ctor_set(v_reuseFailAlloc_5632_, 8, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5632_, 9, v_dAssignment_5617_);
lean_ctor_set(v_reuseFailAlloc_5632_, 10, v_instanceTypedMVars_5618_);
lean_ctor_set(v_reuseFailAlloc_5632_, 11, v_synthNormMemo_5619_);
v___x_5626_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
lean_object* v___x_5628_; 
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 0, v___x_5626_);
v___x_5628_ = v___x_5606_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5626_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_cache_5601_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_zetaDeltaFVarIds_5602_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v_postponed_5603_);
lean_ctor_set(v_reuseFailAlloc_5631_, 4, v_diag_5604_);
v___x_5628_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5629_ = lean_st_ref_put(v___y_5597_, v___x_5628_);
v___x_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5623_);
return v___x_5630_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5595_ = stack[0].m_obj;
lean_object* v_val_5596_ = stack[1].m_obj;
lean_object* v___y_5597_ = stack[2].m_obj;
lean_object* v_res_5635_;
v_res_5635_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5595_, v_val_5596_, v___y_5597_);
stack->m_obj
 = v_res_5635_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5636_, lean_object* v_val_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5636_, v_val_5637_, v___y_5638_);
lean_dec(v___y_5638_);
return v_res_5640_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5641_, lean_object* v_snd_5642_, uint8_t v_stopAtFirstFailure_5643_, lean_object* v_as_x27_5644_, lean_object* v_b_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
if (lean_obj_tag(v_as_x27_5644_) == 0)
{
lean_object* v___x_5656_; 
lean_dec_ref(v_snd_5642_);
lean_dec_ref(v_kp_5641_);
v___x_5656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5656_, 0, v_b_5645_);
return v___x_5656_;
}
else
{
lean_object* v_snd_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5763_; 
v_snd_5657_ = lean_ctor_get(v_b_5645_, 1);
v_isSharedCheck_5763_ = !lean_is_exclusive(v_b_5645_);
if (v_isSharedCheck_5763_ == 0)
{
lean_object* v_unused_5764_; 
v_unused_5764_ = lean_ctor_get(v_b_5645_, 0);
lean_dec(v_unused_5764_);
v___x_5659_ = v_b_5645_;
v_isShared_5660_ = v_isSharedCheck_5763_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_snd_5657_);
lean_dec(v_b_5645_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5763_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v_head_5661_; lean_object* v_tail_5662_; lean_object* v_fst_5663_; lean_object* v_snd_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5762_; 
v_head_5661_ = lean_ctor_get(v_as_x27_5644_, 0);
v_tail_5662_ = lean_ctor_get(v_as_x27_5644_, 1);
v_fst_5663_ = lean_ctor_get(v_snd_5657_, 0);
v_snd_5664_ = lean_ctor_get(v_snd_5657_, 1);
v_isSharedCheck_5762_ = !lean_is_exclusive(v_snd_5657_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5666_ = v_snd_5657_;
v_isShared_5667_ = v_isSharedCheck_5762_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_snd_5664_);
lean_inc(v_fst_5663_);
lean_dec(v_snd_5657_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5762_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5668_ = lean_box(0);
lean_inc_ref(v_kp_5641_);
lean_inc(v___y_5654_);
lean_inc_ref(v___y_5653_);
lean_inc(v___y_5652_);
lean_inc_ref(v___y_5651_);
lean_inc(v___y_5650_);
lean_inc_ref(v___y_5649_);
lean_inc(v___y_5648_);
lean_inc_ref(v___y_5647_);
lean_inc(v___y_5646_);
lean_inc(v_head_5661_);
v___x_5669_ = lean_apply_11(v_kp_5641_, v_head_5661_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, lean_box(0));
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5753_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5672_ = v___x_5669_;
v_isShared_5673_ = v_isSharedCheck_5753_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5669_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5753_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
if (lean_obj_tag(v_a_5670_) == 0)
{
lean_object* v_seq_5674_; lean_object* v_mvarId_5675_; lean_object* v___x_5676_; 
lean_del_object(v___x_5672_);
v_seq_5674_ = lean_ctor_get(v_a_5670_, 0);
v_mvarId_5675_ = lean_ctor_get(v_head_5661_, 1);
lean_inc(v_mvarId_5675_);
v___x_5676_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5675_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_object* v_a_5677_; 
v_a_5677_ = lean_ctor_get(v___x_5676_, 0);
lean_inc(v_a_5677_);
lean_dec_ref_known(v___x_5676_, 1);
if (lean_obj_tag(v_a_5677_) == 1)
{
lean_object* v_val_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5709_; 
lean_dec_ref(v_kp_5641_);
v_val_5678_ = lean_ctor_get(v_a_5677_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_a_5677_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5680_ = v_a_5677_;
v_isShared_5681_ = v_isSharedCheck_5709_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_val_5678_);
lean_dec(v_a_5677_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5709_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v_mvarId_5682_; lean_object* v___x_5683_; 
v_mvarId_5682_ = lean_ctor_get(v_snd_5642_, 1);
lean_inc(v_mvarId_5682_);
lean_dec_ref(v_snd_5642_);
v___x_5683_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5682_, v_val_5678_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5699_; 
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5699_ == 0)
{
lean_object* v_unused_5700_; 
v_unused_5700_ = lean_ctor_get(v___x_5683_, 0);
lean_dec(v_unused_5700_);
v___x_5685_ = v___x_5683_;
v_isShared_5686_ = v_isSharedCheck_5699_;
goto v_resetjp_5684_;
}
else
{
lean_dec(v___x_5683_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5699_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5681_ == 0)
{
lean_ctor_set(v___x_5680_, 0, v_a_5670_);
v___x_5688_ = v___x_5680_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_a_5670_);
v___x_5688_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
lean_object* v___x_5690_; 
if (v_isShared_5667_ == 0)
{
v___x_5690_ = v___x_5666_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5697_, 1, v_snd_5664_);
v___x_5690_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5692_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v___x_5690_);
lean_ctor_set(v___x_5659_, 0, v___x_5688_);
v___x_5692_ = v___x_5659_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5688_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v___x_5690_);
v___x_5692_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5694_; 
if (v_isShared_5686_ == 0)
{
lean_ctor_set(v___x_5685_, 0, v___x_5692_);
v___x_5694_ = v___x_5685_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_del_object(v___x_5680_);
lean_dec_ref_known(v_a_5670_, 1);
lean_del_object(v___x_5666_);
lean_dec(v_snd_5664_);
lean_dec(v_fst_5663_);
lean_del_object(v___x_5659_);
v_a_5701_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5683_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5683_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
}
else
{
uint8_t v___x_5710_; 
lean_inc(v_seq_5674_);
lean_dec(v_a_5677_);
lean_dec_ref_known(v_a_5670_, 1);
v___x_5710_ = l_List_isEmpty___redArg(v_seq_5674_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; lean_object* v___x_5713_; 
v___x_5711_ = lean_array_push(v_fst_5663_, v_seq_5674_);
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 0, v___x_5711_);
v___x_5713_ = v___x_5666_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5711_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_snd_5664_);
v___x_5713_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
lean_object* v___x_5715_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v___x_5713_);
lean_ctor_set(v___x_5659_, 0, v___x_5668_);
v___x_5715_ = v___x_5659_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5668_);
lean_ctor_set(v_reuseFailAlloc_5717_, 1, v___x_5713_);
v___x_5715_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
v_as_x27_5644_ = v_tail_5662_;
v_b_5645_ = v___x_5715_;
goto _start;
}
}
}
else
{
lean_object* v___x_5720_; 
lean_dec(v_seq_5674_);
if (v_isShared_5667_ == 0)
{
v___x_5720_ = v___x_5666_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_snd_5664_);
v___x_5720_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
lean_object* v___x_5722_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v___x_5720_);
lean_ctor_set(v___x_5659_, 0, v___x_5668_);
v___x_5722_ = v___x_5659_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v___x_5668_);
lean_ctor_set(v_reuseFailAlloc_5724_, 1, v___x_5720_);
v___x_5722_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
v_as_x27_5644_ = v_tail_5662_;
v_b_5645_ = v___x_5722_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5733_; 
lean_dec_ref_known(v_a_5670_, 1);
lean_del_object(v___x_5666_);
lean_dec(v_snd_5664_);
lean_dec(v_fst_5663_);
lean_del_object(v___x_5659_);
lean_dec_ref(v_snd_5642_);
lean_dec_ref(v_kp_5641_);
v_a_5726_ = lean_ctor_get(v___x_5676_, 0);
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5676_);
if (v_isSharedCheck_5733_ == 0)
{
v___x_5728_ = v___x_5676_;
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_a_5726_);
lean_dec(v___x_5676_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v___x_5731_; 
if (v_isShared_5729_ == 0)
{
v___x_5731_ = v___x_5728_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5726_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5643_ == 0)
{
lean_object* v_gs_5734_; lean_object* v___x_5735_; lean_object* v___x_5737_; 
lean_del_object(v___x_5672_);
v_gs_5734_ = lean_ctor_get(v_a_5670_, 0);
lean_inc(v_gs_5734_);
lean_dec_ref_known(v_a_5670_, 1);
v___x_5735_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5664_, v_gs_5734_);
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 1, v___x_5735_);
v___x_5737_ = v___x_5666_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v___x_5735_);
v___x_5737_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
lean_object* v___x_5739_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v___x_5737_);
lean_ctor_set(v___x_5659_, 0, v___x_5668_);
v___x_5739_ = v___x_5659_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5668_);
lean_ctor_set(v_reuseFailAlloc_5741_, 1, v___x_5737_);
v___x_5739_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
v_as_x27_5644_ = v_tail_5662_;
v_b_5645_ = v___x_5739_;
goto _start;
}
}
}
else
{
lean_object* v___x_5743_; lean_object* v___x_5745_; 
lean_dec_ref(v_snd_5642_);
lean_dec_ref(v_kp_5641_);
v___x_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5743_, 0, v_a_5670_);
if (v_isShared_5667_ == 0)
{
v___x_5745_ = v___x_5666_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_fst_5663_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_snd_5664_);
v___x_5745_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
lean_object* v___x_5747_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 1, v___x_5745_);
lean_ctor_set(v___x_5659_, 0, v___x_5743_);
v___x_5747_ = v___x_5659_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v___x_5743_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5745_);
v___x_5747_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5749_; 
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 0, v___x_5747_);
v___x_5749_ = v___x_5672_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5754_; lean_object* v___x_5756_; uint8_t v_isShared_5757_; uint8_t v_isSharedCheck_5761_; 
lean_del_object(v___x_5666_);
lean_dec(v_snd_5664_);
lean_dec(v_fst_5663_);
lean_del_object(v___x_5659_);
lean_dec_ref(v_snd_5642_);
lean_dec_ref(v_kp_5641_);
v_a_5754_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5756_ = v___x_5669_;
v_isShared_5757_ = v_isSharedCheck_5761_;
goto v_resetjp_5755_;
}
else
{
lean_inc(v_a_5754_);
lean_dec(v___x_5669_);
v___x_5756_ = lean_box(0);
v_isShared_5757_ = v_isSharedCheck_5761_;
goto v_resetjp_5755_;
}
v_resetjp_5755_:
{
lean_object* v___x_5759_; 
if (v_isShared_5757_ == 0)
{
v___x_5759_ = v___x_5756_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_a_5754_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kp_5641_ = stack[0].m_obj;
lean_object* v_snd_5642_ = stack[1].m_obj;
uint8_t v_stopAtFirstFailure_5643_ = stack[2].m_num;
lean_object* v_as_x27_5644_ = stack[3].m_obj;
lean_object* v_b_5645_ = stack[4].m_obj;
lean_object* v___y_5646_ = stack[5].m_obj;
lean_object* v___y_5647_ = stack[6].m_obj;
lean_object* v___y_5648_ = stack[7].m_obj;
lean_object* v___y_5649_ = stack[8].m_obj;
lean_object* v___y_5650_ = stack[9].m_obj;
lean_object* v___y_5651_ = stack[10].m_obj;
lean_object* v___y_5652_ = stack[11].m_obj;
lean_object* v___y_5653_ = stack[12].m_obj;
lean_object* v___y_5654_ = stack[13].m_obj;
lean_object* v_res_5765_;
v_res_5765_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5641_, v_snd_5642_, v_stopAtFirstFailure_5643_, v_as_x27_5644_, v_b_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_);
stack->m_obj
 = v_res_5765_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5766_, lean_object* v_snd_5767_, lean_object* v_stopAtFirstFailure_5768_, lean_object* v_as_x27_5769_, lean_object* v_b_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5781_; lean_object* v_res_5782_; 
v_stopAtFirstFailure_boxed_5781_ = lean_unbox(v_stopAtFirstFailure_5768_);
v_res_5782_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5766_, v_snd_5767_, v_stopAtFirstFailure_boxed_5781_, v_as_x27_5769_, v_b_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
lean_dec(v___y_5777_);
lean_dec_ref(v___y_5776_);
lean_dec(v___y_5775_);
lean_dec_ref(v___y_5774_);
lean_dec(v___y_5773_);
lean_dec_ref(v___y_5772_);
lean_dec(v___y_5771_);
lean_dec(v_as_x27_5769_);
return v_res_5782_;
}
}
lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5783_, lean_object* v_c_5784_, lean_object* v___x_5785_, lean_object* v___x_5786_, uint8_t v_isRec_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_){
_start:
{
if (lean_obj_tag(v_a_5788_) == 0)
{
lean_object* v___x_5790_; 
lean_dec(v___x_5786_);
lean_dec_ref(v___x_5785_);
lean_dec_ref(v_snd_5783_);
v___x_5790_ = lean_array_to_list(v_a_5789_);
return v___x_5790_;
}
else
{
lean_object* v_toGoalState_5791_; lean_object* v_split_5792_; lean_object* v_head_5793_; lean_object* v_tail_5794_; lean_object* v___x_5796_; uint8_t v_isShared_5797_; uint8_t v_isSharedCheck_5854_; 
v_toGoalState_5791_ = lean_ctor_get(v_snd_5783_, 0);
lean_inc_ref(v_toGoalState_5791_);
v_split_5792_ = lean_ctor_get(v_toGoalState_5791_, 14);
lean_inc_ref(v_split_5792_);
v_head_5793_ = lean_ctor_get(v_a_5788_, 0);
v_tail_5794_ = lean_ctor_get(v_a_5788_, 1);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_a_5788_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5796_ = v_a_5788_;
v_isShared_5797_ = v_isSharedCheck_5854_;
goto v_resetjp_5795_;
}
else
{
lean_inc(v_tail_5794_);
lean_inc(v_head_5793_);
lean_dec(v_a_5788_);
v___x_5796_ = lean_box(0);
v_isShared_5797_ = v_isSharedCheck_5854_;
goto v_resetjp_5795_;
}
v_resetjp_5795_:
{
lean_object* v_nextDeclIdx_5798_; lean_object* v_enodeMap_5799_; lean_object* v_exprs_5800_; lean_object* v_parents_5801_; lean_object* v_congrTable_5802_; lean_object* v_appMap_5803_; lean_object* v_indicesFound_5804_; lean_object* v_toProcess_5805_; uint8_t v_inconsistent_5806_; lean_object* v_nextIdx_5807_; lean_object* v_newRawFacts_5808_; lean_object* v_facts_5809_; lean_object* v_extThms_5810_; lean_object* v_ematch_5811_; lean_object* v_inj_5812_; lean_object* v_clean_5813_; lean_object* v_sstates_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5852_; 
v_nextDeclIdx_5798_ = lean_ctor_get(v_toGoalState_5791_, 0);
v_enodeMap_5799_ = lean_ctor_get(v_toGoalState_5791_, 1);
v_exprs_5800_ = lean_ctor_get(v_toGoalState_5791_, 2);
v_parents_5801_ = lean_ctor_get(v_toGoalState_5791_, 3);
v_congrTable_5802_ = lean_ctor_get(v_toGoalState_5791_, 4);
v_appMap_5803_ = lean_ctor_get(v_toGoalState_5791_, 5);
v_indicesFound_5804_ = lean_ctor_get(v_toGoalState_5791_, 6);
v_toProcess_5805_ = lean_ctor_get(v_toGoalState_5791_, 7);
v_inconsistent_5806_ = lean_ctor_get_uint8(v_toGoalState_5791_, sizeof(void*)*17);
v_nextIdx_5807_ = lean_ctor_get(v_toGoalState_5791_, 8);
v_newRawFacts_5808_ = lean_ctor_get(v_toGoalState_5791_, 9);
v_facts_5809_ = lean_ctor_get(v_toGoalState_5791_, 10);
v_extThms_5810_ = lean_ctor_get(v_toGoalState_5791_, 11);
v_ematch_5811_ = lean_ctor_get(v_toGoalState_5791_, 12);
v_inj_5812_ = lean_ctor_get(v_toGoalState_5791_, 13);
v_clean_5813_ = lean_ctor_get(v_toGoalState_5791_, 15);
v_sstates_5814_ = lean_ctor_get(v_toGoalState_5791_, 16);
v_isSharedCheck_5852_ = !lean_is_exclusive(v_toGoalState_5791_);
if (v_isSharedCheck_5852_ == 0)
{
lean_object* v_unused_5853_; 
v_unused_5853_ = lean_ctor_get(v_toGoalState_5791_, 14);
lean_dec(v_unused_5853_);
v___x_5816_ = v_toGoalState_5791_;
v_isShared_5817_ = v_isSharedCheck_5852_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_sstates_5814_);
lean_inc(v_clean_5813_);
lean_inc(v_inj_5812_);
lean_inc(v_ematch_5811_);
lean_inc(v_extThms_5810_);
lean_inc(v_facts_5809_);
lean_inc(v_newRawFacts_5808_);
lean_inc(v_nextIdx_5807_);
lean_inc(v_toProcess_5805_);
lean_inc(v_indicesFound_5804_);
lean_inc(v_appMap_5803_);
lean_inc(v_congrTable_5802_);
lean_inc(v_parents_5801_);
lean_inc(v_exprs_5800_);
lean_inc(v_enodeMap_5799_);
lean_inc(v_nextDeclIdx_5798_);
lean_dec(v_toGoalState_5791_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5852_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v_num_5818_; lean_object* v_candidates_5819_; lean_object* v_added_5820_; lean_object* v_resolved_5821_; lean_object* v_trace_5822_; lean_object* v_lookaheads_5823_; lean_object* v_argPosMap_5824_; lean_object* v_argsAt_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5851_; 
v_num_5818_ = lean_ctor_get(v_split_5792_, 0);
v_candidates_5819_ = lean_ctor_get(v_split_5792_, 1);
v_added_5820_ = lean_ctor_get(v_split_5792_, 2);
v_resolved_5821_ = lean_ctor_get(v_split_5792_, 3);
v_trace_5822_ = lean_ctor_get(v_split_5792_, 4);
v_lookaheads_5823_ = lean_ctor_get(v_split_5792_, 5);
v_argPosMap_5824_ = lean_ctor_get(v_split_5792_, 6);
v_argsAt_5825_ = lean_ctor_get(v_split_5792_, 7);
v_isSharedCheck_5851_ = !lean_is_exclusive(v_split_5792_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5827_ = v_split_5792_;
v_isShared_5828_ = v_isSharedCheck_5851_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_argsAt_5825_);
lean_inc(v_argPosMap_5824_);
lean_inc(v_lookaheads_5823_);
lean_inc(v_trace_5822_);
lean_inc(v_resolved_5821_);
lean_inc(v_added_5820_);
lean_inc(v_candidates_5819_);
lean_inc(v_num_5818_);
lean_dec(v_split_5792_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5851_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5829_; lean_object* v___y_5831_; lean_object* v___x_5849_; uint8_t v___x_5850_; 
v___x_5829_ = lean_array_get_size(v_a_5789_);
v___x_5849_ = lean_unsigned_to_nat(0u);
v___x_5850_ = lean_nat_dec_lt(v___x_5849_, v___x_5829_);
if (v___x_5850_ == 0)
{
if (v_isRec_5787_ == 0)
{
v___y_5831_ = v_num_5818_;
goto v___jp_5830_;
}
else
{
goto v___jp_5846_;
}
}
else
{
goto v___jp_5846_;
}
v___jp_5830_:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5835_; 
v___x_5832_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5784_);
lean_inc(v___x_5786_);
lean_inc_ref(v___x_5785_);
v___x_5833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5785_);
lean_ctor_set(v___x_5833_, 1, v___x_5829_);
lean_ctor_set(v___x_5833_, 2, v___x_5786_);
lean_ctor_set(v___x_5833_, 3, v___x_5832_);
if (v_isShared_5797_ == 0)
{
lean_ctor_set(v___x_5796_, 1, v_trace_5822_);
lean_ctor_set(v___x_5796_, 0, v___x_5833_);
v___x_5835_ = v___x_5796_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5833_);
lean_ctor_set(v_reuseFailAlloc_5845_, 1, v_trace_5822_);
v___x_5835_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
lean_object* v___x_5837_; 
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 4, v___x_5835_);
lean_ctor_set(v___x_5827_, 0, v___y_5831_);
v___x_5837_ = v___x_5827_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v___y_5831_);
lean_ctor_set(v_reuseFailAlloc_5844_, 1, v_candidates_5819_);
lean_ctor_set(v_reuseFailAlloc_5844_, 2, v_added_5820_);
lean_ctor_set(v_reuseFailAlloc_5844_, 3, v_resolved_5821_);
lean_ctor_set(v_reuseFailAlloc_5844_, 4, v___x_5835_);
lean_ctor_set(v_reuseFailAlloc_5844_, 5, v_lookaheads_5823_);
lean_ctor_set(v_reuseFailAlloc_5844_, 6, v_argPosMap_5824_);
lean_ctor_set(v_reuseFailAlloc_5844_, 7, v_argsAt_5825_);
v___x_5837_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
lean_object* v___x_5839_; 
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 14, v___x_5837_);
v___x_5839_ = v___x_5816_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_nextDeclIdx_5798_);
lean_ctor_set(v_reuseFailAlloc_5843_, 1, v_enodeMap_5799_);
lean_ctor_set(v_reuseFailAlloc_5843_, 2, v_exprs_5800_);
lean_ctor_set(v_reuseFailAlloc_5843_, 3, v_parents_5801_);
lean_ctor_set(v_reuseFailAlloc_5843_, 4, v_congrTable_5802_);
lean_ctor_set(v_reuseFailAlloc_5843_, 5, v_appMap_5803_);
lean_ctor_set(v_reuseFailAlloc_5843_, 6, v_indicesFound_5804_);
lean_ctor_set(v_reuseFailAlloc_5843_, 7, v_toProcess_5805_);
lean_ctor_set(v_reuseFailAlloc_5843_, 8, v_nextIdx_5807_);
lean_ctor_set(v_reuseFailAlloc_5843_, 9, v_newRawFacts_5808_);
lean_ctor_set(v_reuseFailAlloc_5843_, 10, v_facts_5809_);
lean_ctor_set(v_reuseFailAlloc_5843_, 11, v_extThms_5810_);
lean_ctor_set(v_reuseFailAlloc_5843_, 12, v_ematch_5811_);
lean_ctor_set(v_reuseFailAlloc_5843_, 13, v_inj_5812_);
lean_ctor_set(v_reuseFailAlloc_5843_, 14, v___x_5837_);
lean_ctor_set(v_reuseFailAlloc_5843_, 15, v_clean_5813_);
lean_ctor_set(v_reuseFailAlloc_5843_, 16, v_sstates_5814_);
lean_ctor_set_uint8(v_reuseFailAlloc_5843_, sizeof(void*)*17, v_inconsistent_5806_);
v___x_5839_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5839_);
lean_ctor_set(v___x_5840_, 1, v_head_5793_);
v___x_5841_ = lean_array_push(v_a_5789_, v___x_5840_);
v_a_5788_ = v_tail_5794_;
v_a_5789_ = v___x_5841_;
goto _start;
}
}
}
}
v___jp_5846_:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5847_ = lean_unsigned_to_nat(1u);
v___x_5848_ = lean_nat_add(v_num_5818_, v___x_5847_);
lean_dec(v_num_5818_);
v___y_5831_ = v___x_5848_;
goto v___jp_5830_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_5783_ = stack[0].m_obj;
lean_object* v_c_5784_ = stack[1].m_obj;
lean_object* v___x_5785_ = stack[2].m_obj;
lean_object* v___x_5786_ = stack[3].m_obj;
uint8_t v_isRec_5787_ = stack[4].m_num;
lean_object* v_a_5788_ = stack[5].m_obj;
lean_object* v_a_5789_ = stack[6].m_obj;
lean_object* v_res_5855_;
v_res_5855_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5783_, v_c_5784_, v___x_5785_, v___x_5786_, v_isRec_5787_, v_a_5788_, v_a_5789_);
stack->m_obj
 = v_res_5855_;
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5856_, lean_object* v_c_5857_, lean_object* v___x_5858_, lean_object* v___x_5859_, lean_object* v_isRec_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_){
_start:
{
uint8_t v_isRec_boxed_5863_; lean_object* v_res_5864_; 
v_isRec_boxed_5863_ = lean_unbox(v_isRec_5860_);
v_res_5864_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5856_, v_c_5857_, v___x_5858_, v___x_5859_, v_isRec_boxed_5863_, v_a_5861_, v_a_5862_);
lean_dec_ref(v_c_5857_);
return v_res_5864_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5876_ = lean_box(0);
v___x_5877_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5878_ = l_Lean_mkConst(v___x_5877_, v___x_5876_);
return v___x_5878_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5879_, lean_object* v_numCases_5880_, uint8_t v_isRec_5881_, uint8_t v_stopAtFirstFailure_5882_, uint8_t v_compress_5883_, lean_object* v_candidates_x3f_5884_, lean_object* v_goal_5885_, lean_object* v_kp_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_){
_start:
{
lean_object* v___x_5897_; 
v___x_5897_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5888_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; uint8_t v_trace_5899_; lean_object* v___x_5900_; 
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5898_);
lean_dec_ref_known(v___x_5897_, 1);
v_trace_5899_ = lean_ctor_get_uint8(v_a_5898_, sizeof(void*)*14);
lean_dec(v_a_5898_);
lean_inc_ref(v_goal_5885_);
v___x_5900_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5885_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; lean_object* v_mvarId_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___f_5905_; lean_object* v___x_5906_; lean_object* v___f_5907_; lean_object* v___x_5908_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc_n(v_a_5901_, 2);
lean_dec_ref_known(v___x_5900_, 1);
v_mvarId_5902_ = lean_ctor_get(v_goal_5885_, 1);
lean_inc(v_mvarId_5902_);
v___x_5903_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5879_);
v___x_5904_ = lean_box(v_isRec_5881_);
lean_inc_ref_n(v_c_5879_, 2);
lean_inc_ref(v___x_5903_);
v___f_5905_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5905_, 0, v___x_5903_);
lean_closure_set(v___f_5905_, 1, v_c_5879_);
lean_closure_set(v___f_5905_, 2, v_a_5901_);
lean_closure_set(v___f_5905_, 3, v_numCases_5880_);
lean_closure_set(v___f_5905_, 4, v___x_5904_);
v___x_5906_ = lean_box(v_trace_5899_);
v___f_5907_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5907_, 0, v_goal_5885_);
lean_closure_set(v___f_5907_, 1, v___x_5906_);
lean_closure_set(v___f_5907_, 2, v___f_5905_);
lean_closure_set(v___f_5907_, 3, v_c_5879_);
lean_closure_set(v___f_5907_, 4, v_candidates_x3f_5884_);
v___x_5908_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5902_, v___f_5907_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
if (lean_obj_tag(v___x_5908_) == 0)
{
lean_object* v_a_5909_; lean_object* v_fst_5910_; lean_object* v_snd_5911_; lean_object* v_fst_5912_; lean_object* v_snd_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v_a_5909_ = lean_ctor_get(v___x_5908_, 0);
lean_inc(v_a_5909_);
lean_dec_ref_known(v___x_5908_, 1);
v_fst_5910_ = lean_ctor_get(v_a_5909_, 0);
lean_inc(v_fst_5910_);
v_snd_5911_ = lean_ctor_get(v_a_5909_, 1);
lean_inc_n(v_snd_5911_, 3);
lean_dec(v_a_5909_);
v_fst_5912_ = lean_ctor_get(v_fst_5910_, 0);
lean_inc(v_fst_5912_);
v_snd_5913_ = lean_ctor_get(v_fst_5910_, 1);
lean_inc(v_snd_5913_);
lean_dec(v_fst_5910_);
v___x_5914_ = l_List_lengthTR___redArg(v_fst_5912_);
v___x_5915_ = lean_unsigned_to_nat(0u);
v___x_5916_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5917_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5911_, v_c_5879_, v___x_5903_, v___x_5914_, v_isRec_5881_, v_fst_5912_, v___x_5916_);
lean_dec_ref(v_c_5879_);
v___x_5918_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5919_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5886_, v_snd_5911_, v_stopAtFirstFailure_5882_, v___x_5917_, v___x_5918_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
lean_dec(v___x_5917_);
if (lean_obj_tag(v___x_5919_) == 0)
{
lean_object* v_a_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_6003_; 
v_a_5920_ = lean_ctor_get(v___x_5919_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5919_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5922_ = v___x_5919_;
v_isShared_5923_ = v_isSharedCheck_6003_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_a_5920_);
lean_dec(v___x_5919_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_6003_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v_fst_5924_; 
v_fst_5924_ = lean_ctor_get(v_a_5920_, 0);
if (lean_obj_tag(v_fst_5924_) == 0)
{
lean_object* v_snd_5925_; lean_object* v_fst_5926_; lean_object* v_snd_5927_; lean_object* v___y_5929_; lean_object* v___y_5930_; lean_object* v_mvarId_5977_; lean_object* v___x_5978_; 
v_snd_5925_ = lean_ctor_get(v_a_5920_, 1);
lean_inc(v_snd_5925_);
lean_dec(v_a_5920_);
v_fst_5926_ = lean_ctor_get(v_snd_5925_, 0);
lean_inc(v_fst_5926_);
v_snd_5927_ = lean_ctor_get(v_snd_5925_, 1);
lean_inc(v_snd_5927_);
lean_dec(v_snd_5925_);
v_mvarId_5977_ = lean_ctor_get(v_snd_5911_, 1);
lean_inc_n(v_mvarId_5977_, 2);
lean_dec(v_snd_5911_);
v___x_5978_ = l_Lean_MVarId_getType(v_mvarId_5977_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
if (lean_obj_tag(v___x_5978_) == 0)
{
lean_object* v_a_5979_; uint8_t v___x_5980_; 
v_a_5979_ = lean_ctor_get(v___x_5978_, 0);
lean_inc(v_a_5979_);
lean_dec_ref_known(v___x_5978_, 1);
v___x_5980_ = l_Lean_Expr_isFalse(v_a_5979_);
if (v___x_5980_ == 0)
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v_a_5983_; lean_object* v___x_5984_; 
v___x_5981_ = l_Lean_mkMVar(v_a_5901_);
v___x_5982_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5981_, v_a_5893_);
v_a_5983_ = lean_ctor_get(v___x_5982_, 0);
lean_inc(v_a_5983_);
lean_dec_ref(v___x_5982_);
v___x_5984_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5977_, v_a_5983_, v_a_5893_);
lean_dec_ref(v___x_5984_);
v___y_5929_ = v_a_5894_;
v___y_5930_ = v_a_5895_;
goto v___jp_5928_;
}
else
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v_a_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5985_ = l_Lean_mkMVar(v_a_5901_);
v___x_5986_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5985_, v_a_5893_);
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
lean_inc(v_a_5987_);
lean_dec_ref(v___x_5986_);
v___x_5988_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5989_ = l_Lean_Meta_mkExpectedPropHint(v_a_5987_, v___x_5988_);
v___x_5990_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5977_, v___x_5989_, v_a_5893_);
lean_dec_ref(v___x_5990_);
v___y_5929_ = v_a_5894_;
v___y_5930_ = v_a_5895_;
goto v___jp_5928_;
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec(v_mvarId_5977_);
lean_dec(v_snd_5927_);
lean_dec(v_fst_5926_);
lean_del_object(v___x_5922_);
lean_dec(v_snd_5913_);
lean_dec(v_a_5901_);
v_a_5991_ = lean_ctor_get(v___x_5978_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5978_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5978_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5978_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
}
}
}
v___jp_5928_:
{
lean_object* v___x_5931_; uint8_t v___x_5932_; 
v___x_5931_ = lean_array_get_size(v_snd_5927_);
v___x_5932_ = lean_nat_dec_eq(v___x_5931_, v___x_5915_);
if (v___x_5932_ == 0)
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5936_; 
lean_dec(v_fst_5926_);
lean_dec(v_snd_5913_);
v___x_5933_ = lean_array_to_list(v_snd_5927_);
v___x_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 0, v___x_5934_);
v___x_5936_ = v___x_5922_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5937_; 
v_reuseFailAlloc_5937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5937_, 0, v___x_5934_);
v___x_5936_ = v_reuseFailAlloc_5937_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
return v___x_5936_;
}
}
else
{
lean_dec(v_snd_5927_);
if (lean_obj_tag(v_snd_5913_) == 1)
{
lean_object* v_val_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5972_; 
lean_del_object(v___x_5922_);
v_val_5938_ = lean_ctor_get(v_snd_5913_, 0);
v_isSharedCheck_5972_ = !lean_is_exclusive(v_snd_5913_);
if (v_isSharedCheck_5972_ == 0)
{
v___x_5940_ = v_snd_5913_;
v_isShared_5941_ = v_isSharedCheck_5972_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_val_5938_);
lean_dec(v_snd_5913_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5972_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5942_; 
v___x_5942_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5938_, v___y_5929_);
lean_dec(v_val_5938_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; lean_object* v___x_5944_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref_known(v___x_5942_, 1);
v___x_5944_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5943_, v_fst_5926_, v_compress_5883_, v___y_5929_, v___y_5930_);
if (lean_obj_tag(v___x_5944_) == 0)
{
lean_object* v_a_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5955_; 
v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5947_ = v___x_5944_;
v_isShared_5948_ = v_isSharedCheck_5955_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_a_5945_);
lean_dec(v___x_5944_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5955_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5950_; 
if (v_isShared_5941_ == 0)
{
lean_ctor_set_tag(v___x_5940_, 0);
lean_ctor_set(v___x_5940_, 0, v_a_5945_);
v___x_5950_ = v___x_5940_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_a_5945_);
v___x_5950_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
lean_object* v___x_5952_; 
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 0, v___x_5950_);
v___x_5952_ = v___x_5947_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
}
}
}
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5963_; 
lean_del_object(v___x_5940_);
v_a_5956_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5958_ = v___x_5944_;
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5944_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
}
else
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5971_; 
lean_del_object(v___x_5940_);
lean_dec(v_fst_5926_);
v_a_5964_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5966_ = v___x_5942_;
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5942_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
if (v_isShared_5967_ == 0)
{
v___x_5969_ = v___x_5966_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
}
else
{
lean_object* v___x_5973_; lean_object* v___x_5975_; 
lean_dec(v_fst_5926_);
lean_dec(v_snd_5913_);
v___x_5973_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 0, v___x_5973_);
v___x_5975_ = v___x_5922_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5973_);
v___x_5975_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
return v___x_5975_;
}
}
}
}
}
else
{
lean_object* v_val_5999_; lean_object* v___x_6001_; 
lean_inc_ref(v_fst_5924_);
lean_dec(v_a_5920_);
lean_dec(v_snd_5913_);
lean_dec(v_snd_5911_);
lean_dec(v_a_5901_);
v_val_5999_ = lean_ctor_get(v_fst_5924_, 0);
lean_inc(v_val_5999_);
lean_dec_ref_known(v_fst_5924_, 1);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 0, v_val_5999_);
v___x_6001_ = v___x_5922_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_val_5999_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
}
}
}
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
lean_dec(v_snd_5913_);
lean_dec(v_snd_5911_);
lean_dec(v_a_5901_);
v_a_6004_ = lean_ctor_get(v___x_5919_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5919_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5919_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5919_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
return v___x_6009_;
}
}
}
}
else
{
lean_object* v_a_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6019_; 
lean_dec_ref(v___x_5903_);
lean_dec(v_a_5901_);
lean_dec_ref(v_kp_5886_);
lean_dec_ref(v_c_5879_);
v_a_6012_ = lean_ctor_get(v___x_5908_, 0);
v_isSharedCheck_6019_ = !lean_is_exclusive(v___x_5908_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_6014_ = v___x_5908_;
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_a_6012_);
lean_dec(v___x_5908_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6017_; 
if (v_isShared_6015_ == 0)
{
v___x_6017_ = v___x_6014_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
v___x_6017_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
return v___x_6017_;
}
}
}
}
else
{
lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec_ref(v_kp_5886_);
lean_dec_ref(v_goal_5885_);
lean_dec(v_candidates_x3f_5884_);
lean_dec(v_numCases_5880_);
lean_dec_ref(v_c_5879_);
v_a_6020_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_5900_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_5900_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
else
{
lean_object* v_a_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6035_; 
lean_dec_ref(v_kp_5886_);
lean_dec_ref(v_goal_5885_);
lean_dec(v_candidates_x3f_5884_);
lean_dec(v_numCases_5880_);
lean_dec_ref(v_c_5879_);
v_a_6028_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_6035_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_6030_ = v___x_5897_;
v_isShared_6031_ = v_isSharedCheck_6035_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_a_6028_);
lean_dec(v___x_5897_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6035_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6033_; 
if (v_isShared_6031_ == 0)
{
v___x_6033_ = v___x_6030_;
goto v_reusejp_6032_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
v___x_6033_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6032_;
}
v_reusejp_6032_:
{
return v___x_6033_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_5879_ = stack[0].m_obj;
lean_object* v_numCases_5880_ = stack[1].m_obj;
uint8_t v_isRec_5881_ = stack[2].m_num;
uint8_t v_stopAtFirstFailure_5882_ = stack[3].m_num;
uint8_t v_compress_5883_ = stack[4].m_num;
lean_object* v_candidates_x3f_5884_ = stack[5].m_obj;
lean_object* v_goal_5885_ = stack[6].m_obj;
lean_object* v_kp_5886_ = stack[7].m_obj;
lean_object* v_a_5887_ = stack[8].m_obj;
lean_object* v_a_5888_ = stack[9].m_obj;
lean_object* v_a_5889_ = stack[10].m_obj;
lean_object* v_a_5890_ = stack[11].m_obj;
lean_object* v_a_5891_ = stack[12].m_obj;
lean_object* v_a_5892_ = stack[13].m_obj;
lean_object* v_a_5893_ = stack[14].m_obj;
lean_object* v_a_5894_ = stack[15].m_obj;
lean_object* v_a_5895_ = stack[16].m_obj;
lean_object* v_res_6036_;
v_res_6036_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5879_, v_numCases_5880_, v_isRec_5881_, v_stopAtFirstFailure_5882_, v_compress_5883_, v_candidates_x3f_5884_, v_goal_5885_, v_kp_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_, v_a_5894_, v_a_5895_);
stack->m_obj
 = v_res_6036_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6037_ = _args[0];
lean_object* v_numCases_6038_ = _args[1];
lean_object* v_isRec_6039_ = _args[2];
lean_object* v_stopAtFirstFailure_6040_ = _args[3];
lean_object* v_compress_6041_ = _args[4];
lean_object* v_candidates_x3f_6042_ = _args[5];
lean_object* v_goal_6043_ = _args[6];
lean_object* v_kp_6044_ = _args[7];
lean_object* v_a_6045_ = _args[8];
lean_object* v_a_6046_ = _args[9];
lean_object* v_a_6047_ = _args[10];
lean_object* v_a_6048_ = _args[11];
lean_object* v_a_6049_ = _args[12];
lean_object* v_a_6050_ = _args[13];
lean_object* v_a_6051_ = _args[14];
lean_object* v_a_6052_ = _args[15];
lean_object* v_a_6053_ = _args[16];
lean_object* v_a_6054_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6055_; uint8_t v_stopAtFirstFailure_boxed_6056_; uint8_t v_compress_boxed_6057_; lean_object* v_res_6058_; 
v_isRec_boxed_6055_ = lean_unbox(v_isRec_6039_);
v_stopAtFirstFailure_boxed_6056_ = lean_unbox(v_stopAtFirstFailure_6040_);
v_compress_boxed_6057_ = lean_unbox(v_compress_6041_);
v_res_6058_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6037_, v_numCases_6038_, v_isRec_boxed_6055_, v_stopAtFirstFailure_boxed_6056_, v_compress_boxed_6057_, v_candidates_x3f_6042_, v_goal_6043_, v_kp_6044_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_, v_a_6053_);
lean_dec(v_a_6053_);
lean_dec_ref(v_a_6052_);
lean_dec(v_a_6051_);
lean_dec_ref(v_a_6050_);
lean_dec(v_a_6049_);
lean_dec_ref(v_a_6048_);
lean_dec(v_a_6047_);
lean_dec_ref(v_a_6046_);
lean_dec(v_a_6045_);
return v_res_6058_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6059_, lean_object* v_numCases_6060_, uint8_t v_isRec_6061_, uint8_t v_stopAtFirstFailure_6062_, uint8_t v_compress_6063_, lean_object* v_candidates_x3f_6064_, lean_object* v_goal_6065_, lean_object* v_x_6066_, lean_object* v_kp_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_){
_start:
{
lean_object* v___x_6078_; 
v___x_6078_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6059_, v_numCases_6060_, v_isRec_6061_, v_stopAtFirstFailure_6062_, v_compress_6063_, v_candidates_x3f_6064_, v_goal_6065_, v_kp_6067_, v_a_6068_, v_a_6069_, v_a_6070_, v_a_6071_, v_a_6072_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
return v___x_6078_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_6059_ = stack[0].m_obj;
lean_object* v_numCases_6060_ = stack[1].m_obj;
uint8_t v_isRec_6061_ = stack[2].m_num;
uint8_t v_stopAtFirstFailure_6062_ = stack[3].m_num;
uint8_t v_compress_6063_ = stack[4].m_num;
lean_object* v_candidates_x3f_6064_ = stack[5].m_obj;
lean_object* v_goal_6065_ = stack[6].m_obj;
lean_object* v_x_6066_ = stack[7].m_obj;
lean_object* v_kp_6067_ = stack[8].m_obj;
lean_object* v_a_6068_ = stack[9].m_obj;
lean_object* v_a_6069_ = stack[10].m_obj;
lean_object* v_a_6070_ = stack[11].m_obj;
lean_object* v_a_6071_ = stack[12].m_obj;
lean_object* v_a_6072_ = stack[13].m_obj;
lean_object* v_a_6073_ = stack[14].m_obj;
lean_object* v_a_6074_ = stack[15].m_obj;
lean_object* v_a_6075_ = stack[16].m_obj;
lean_object* v_a_6076_ = stack[17].m_obj;
lean_object* v_res_6079_;
v_res_6079_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6059_, v_numCases_6060_, v_isRec_6061_, v_stopAtFirstFailure_6062_, v_compress_6063_, v_candidates_x3f_6064_, v_goal_6065_, v_x_6066_, v_kp_6067_, v_a_6068_, v_a_6069_, v_a_6070_, v_a_6071_, v_a_6072_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
stack->m_obj
 = v_res_6079_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6080_ = _args[0];
lean_object* v_numCases_6081_ = _args[1];
lean_object* v_isRec_6082_ = _args[2];
lean_object* v_stopAtFirstFailure_6083_ = _args[3];
lean_object* v_compress_6084_ = _args[4];
lean_object* v_candidates_x3f_6085_ = _args[5];
lean_object* v_goal_6086_ = _args[6];
lean_object* v_x_6087_ = _args[7];
lean_object* v_kp_6088_ = _args[8];
lean_object* v_a_6089_ = _args[9];
lean_object* v_a_6090_ = _args[10];
lean_object* v_a_6091_ = _args[11];
lean_object* v_a_6092_ = _args[12];
lean_object* v_a_6093_ = _args[13];
lean_object* v_a_6094_ = _args[14];
lean_object* v_a_6095_ = _args[15];
lean_object* v_a_6096_ = _args[16];
lean_object* v_a_6097_ = _args[17];
lean_object* v_a_6098_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6099_; uint8_t v_stopAtFirstFailure_boxed_6100_; uint8_t v_compress_boxed_6101_; lean_object* v_res_6102_; 
v_isRec_boxed_6099_ = lean_unbox(v_isRec_6082_);
v_stopAtFirstFailure_boxed_6100_ = lean_unbox(v_stopAtFirstFailure_6083_);
v_compress_boxed_6101_ = lean_unbox(v_compress_6084_);
v_res_6102_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6080_, v_numCases_6081_, v_isRec_boxed_6099_, v_stopAtFirstFailure_boxed_6100_, v_compress_boxed_6101_, v_candidates_x3f_6085_, v_goal_6086_, v_x_6087_, v_kp_6088_, v_a_6089_, v_a_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_, v_a_6095_, v_a_6096_, v_a_6097_);
lean_dec(v_a_6097_);
lean_dec_ref(v_a_6096_);
lean_dec(v_a_6095_);
lean_dec_ref(v_a_6094_);
lean_dec(v_a_6093_);
lean_dec_ref(v_a_6092_);
lean_dec(v_a_6091_);
lean_dec_ref(v_a_6090_);
lean_dec(v_a_6089_);
lean_dec_ref(v_x_6087_);
return v_res_6102_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_6103_, lean_object* v_snd_6104_, uint8_t v_stopAtFirstFailure_6105_, lean_object* v_as_6106_, lean_object* v_as_x27_6107_, lean_object* v_b_6108_, lean_object* v_a_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_){
_start:
{
lean_object* v___x_6120_; 
v___x_6120_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_6103_, v_snd_6104_, v_stopAtFirstFailure_6105_, v_as_x27_6107_, v_b_6108_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_);
return v___x_6120_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_kp_6103_ = stack[0].m_obj;
lean_object* v_snd_6104_ = stack[1].m_obj;
uint8_t v_stopAtFirstFailure_6105_ = stack[2].m_num;
lean_object* v_as_6106_ = stack[3].m_obj;
lean_object* v_as_x27_6107_ = stack[4].m_obj;
lean_object* v_b_6108_ = stack[5].m_obj;
lean_object* v___y_6110_ = stack[7].m_obj;
lean_object* v___y_6111_ = stack[8].m_obj;
lean_object* v___y_6112_ = stack[9].m_obj;
lean_object* v___y_6113_ = stack[10].m_obj;
lean_object* v___y_6114_ = stack[11].m_obj;
lean_object* v___y_6115_ = stack[12].m_obj;
lean_object* v___y_6116_ = stack[13].m_obj;
lean_object* v___y_6117_ = stack[14].m_obj;
lean_object* v___y_6118_ = stack[15].m_obj;
lean_object* v_res_6121_;
v_res_6121_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6103_, v_snd_6104_, v_stopAtFirstFailure_6105_, v_as_6106_, v_as_x27_6107_, v_b_6108_, lean_box(0), v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_);
stack->m_obj
 = v_res_6121_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6122_ = _args[0];
lean_object* v_snd_6123_ = _args[1];
lean_object* v_stopAtFirstFailure_6124_ = _args[2];
lean_object* v_as_6125_ = _args[3];
lean_object* v_as_x27_6126_ = _args[4];
lean_object* v_b_6127_ = _args[5];
lean_object* v_a_6128_ = _args[6];
lean_object* v___y_6129_ = _args[7];
lean_object* v___y_6130_ = _args[8];
lean_object* v___y_6131_ = _args[9];
lean_object* v___y_6132_ = _args[10];
lean_object* v___y_6133_ = _args[11];
lean_object* v___y_6134_ = _args[12];
lean_object* v___y_6135_ = _args[13];
lean_object* v___y_6136_ = _args[14];
lean_object* v___y_6137_ = _args[15];
lean_object* v___y_6138_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6139_; lean_object* v_res_6140_; 
v_stopAtFirstFailure_boxed_6139_ = lean_unbox(v_stopAtFirstFailure_6124_);
v_res_6140_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6122_, v_snd_6123_, v_stopAtFirstFailure_boxed_6139_, v_as_6125_, v_as_x27_6126_, v_b_6127_, v_a_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_);
lean_dec(v___y_6137_);
lean_dec_ref(v___y_6136_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec(v_as_x27_6126_);
lean_dec(v_as_6125_);
return v_res_6140_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6141_, lean_object* v_val_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_){
_start:
{
lean_object* v___x_6153_; 
v___x_6153_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6141_, v_val_6142_, v___y_6149_);
return v___x_6153_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_6141_ = stack[0].m_obj;
lean_object* v_val_6142_ = stack[1].m_obj;
lean_object* v___y_6143_ = stack[2].m_obj;
lean_object* v___y_6144_ = stack[3].m_obj;
lean_object* v___y_6145_ = stack[4].m_obj;
lean_object* v___y_6146_ = stack[5].m_obj;
lean_object* v___y_6147_ = stack[6].m_obj;
lean_object* v___y_6148_ = stack[7].m_obj;
lean_object* v___y_6149_ = stack[8].m_obj;
lean_object* v___y_6150_ = stack[9].m_obj;
lean_object* v___y_6151_ = stack[10].m_obj;
lean_object* v_res_6154_;
v_res_6154_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6141_, v_val_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_);
stack->m_obj
 = v_res_6154_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6155_, lean_object* v_val_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6155_, v_val_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
lean_dec(v___y_6163_);
lean_dec_ref(v___y_6162_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec(v___y_6157_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6168_, lean_object* v_x_6169_, lean_object* v_x_6170_, lean_object* v_x_6171_){
_start:
{
lean_object* v___x_6172_; 
v___x_6172_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6169_, v_x_6170_, v_x_6171_);
return v___x_6172_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6173_, lean_object* v_x_6174_, size_t v_x_6175_, size_t v_x_6176_, lean_object* v_x_6177_, lean_object* v_x_6178_){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6174_, v_x_6175_, v_x_6176_, v_x_6177_, v_x_6178_);
return v___x_6179_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6174_ = stack[1].m_obj;
size_t v_x_6175_ = stack[2].m_num;
size_t v_x_6176_ = stack[3].m_num;
lean_object* v_x_6177_ = stack[4].m_obj;
lean_object* v_x_6178_ = stack[5].m_obj;
lean_object* v_res_6180_;
v_res_6180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_box(0), v_x_6174_, v_x_6175_, v_x_6176_, v_x_6177_, v_x_6178_);
stack->m_obj
 = v_res_6180_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6181_, lean_object* v_x_6182_, lean_object* v_x_6183_, lean_object* v_x_6184_, lean_object* v_x_6185_, lean_object* v_x_6186_){
_start:
{
size_t v_x_68739__boxed_6187_; size_t v_x_68740__boxed_6188_; lean_object* v_res_6189_; 
v_x_68739__boxed_6187_ = lean_unbox_usize(v_x_6183_);
lean_dec(v_x_6183_);
v_x_68740__boxed_6188_ = lean_unbox_usize(v_x_6184_);
lean_dec(v_x_6184_);
v_res_6189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6181_, v_x_6182_, v_x_68739__boxed_6187_, v_x_68740__boxed_6188_, v_x_6185_, v_x_6186_);
return v_res_6189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6190_, lean_object* v_n_6191_, lean_object* v_k_6192_, lean_object* v_v_6193_){
_start:
{
lean_object* v___x_6194_; 
v___x_6194_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6191_, v_k_6192_, v_v_6193_);
return v___x_6194_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6195_, size_t v_depth_6196_, lean_object* v_keys_6197_, lean_object* v_vals_6198_, lean_object* v_heq_6199_, lean_object* v_i_6200_, lean_object* v_entries_6201_){
_start:
{
lean_object* v___x_6202_; 
v___x_6202_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6196_, v_keys_6197_, v_vals_6198_, v_i_6200_, v_entries_6201_);
return v___x_6202_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_6196_ = stack[1].m_num;
lean_object* v_keys_6197_ = stack[2].m_obj;
lean_object* v_vals_6198_ = stack[3].m_obj;
lean_object* v_i_6200_ = stack[5].m_obj;
lean_object* v_entries_6201_ = stack[6].m_obj;
lean_object* v_res_6203_;
v_res_6203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_box(0), v_depth_6196_, v_keys_6197_, v_vals_6198_, lean_box(0), v_i_6200_, v_entries_6201_);
stack->m_obj
 = v_res_6203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6204_, lean_object* v_depth_6205_, lean_object* v_keys_6206_, lean_object* v_vals_6207_, lean_object* v_heq_6208_, lean_object* v_i_6209_, lean_object* v_entries_6210_){
_start:
{
size_t v_depth_boxed_6211_; lean_object* v_res_6212_; 
v_depth_boxed_6211_ = lean_unbox_usize(v_depth_6205_);
lean_dec(v_depth_6205_);
v_res_6212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6204_, v_depth_boxed_6211_, v_keys_6206_, v_vals_6207_, v_heq_6208_, v_i_6209_, v_entries_6210_);
lean_dec_ref(v_vals_6207_);
lean_dec_ref(v_keys_6206_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6213_, lean_object* v_x_6214_, lean_object* v_x_6215_, lean_object* v_x_6216_, lean_object* v_x_6217_){
_start:
{
lean_object* v___x_6218_; 
v___x_6218_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6214_, v_x_6215_, v_x_6216_, v_x_6217_);
return v___x_6218_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_){
_start:
{
lean_object* v___x_6232_; 
v___x_6232_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6219_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
return v___x_6232_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitNext___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6219_ = stack[0].m_obj;
lean_object* v___y_6220_ = stack[1].m_obj;
lean_object* v___y_6221_ = stack[2].m_obj;
lean_object* v___y_6222_ = stack[3].m_obj;
lean_object* v___y_6223_ = stack[4].m_obj;
lean_object* v___y_6224_ = stack[5].m_obj;
lean_object* v___y_6225_ = stack[6].m_obj;
lean_object* v___y_6226_ = stack[7].m_obj;
lean_object* v___y_6227_ = stack[8].m_obj;
lean_object* v___y_6228_ = stack[9].m_obj;
lean_object* v___y_6229_ = stack[10].m_obj;
lean_object* v___y_6230_ = stack[11].m_obj;
lean_object* v_res_6233_;
v_res_6233_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
stack->m_obj
 = v_res_6233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
lean_object* v_res_6247_; 
v_res_6247_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
lean_dec(v___y_6239_);
lean_dec_ref(v___y_6238_);
lean_dec(v___y_6237_);
lean_dec_ref(v___y_6235_);
return v_res_6247_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6259_ = lean_st_mk_ref(v_goal_6248_);
v___x_6260_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6259_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_);
if (lean_obj_tag(v___x_6260_) == 0)
{
lean_object* v_a_6261_; lean_object* v___x_6263_; uint8_t v_isShared_6264_; uint8_t v_isSharedCheck_6270_; 
v_a_6261_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6270_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6270_ == 0)
{
v___x_6263_ = v___x_6260_;
v_isShared_6264_ = v_isSharedCheck_6270_;
goto v_resetjp_6262_;
}
else
{
lean_inc(v_a_6261_);
lean_dec(v___x_6260_);
v___x_6263_ = lean_box(0);
v_isShared_6264_ = v_isSharedCheck_6270_;
goto v_resetjp_6262_;
}
v_resetjp_6262_:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6268_; 
v___x_6265_ = lean_st_ref_get(v___x_6259_);
lean_dec(v___x_6259_);
v___x_6266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6266_, 0, v_a_6261_);
lean_ctor_set(v___x_6266_, 1, v___x_6265_);
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 0, v___x_6266_);
v___x_6268_ = v___x_6263_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v___x_6266_);
v___x_6268_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
return v___x_6268_;
}
}
}
else
{
lean_object* v_a_6271_; lean_object* v___x_6273_; uint8_t v_isShared_6274_; uint8_t v_isSharedCheck_6278_; 
lean_dec(v___x_6259_);
v_a_6271_ = lean_ctor_get(v___x_6260_, 0);
v_isSharedCheck_6278_ = !lean_is_exclusive(v___x_6260_);
if (v_isSharedCheck_6278_ == 0)
{
v___x_6273_ = v___x_6260_;
v_isShared_6274_ = v_isSharedCheck_6278_;
goto v_resetjp_6272_;
}
else
{
lean_inc(v_a_6271_);
lean_dec(v___x_6260_);
v___x_6273_ = lean_box(0);
v_isShared_6274_ = v_isSharedCheck_6278_;
goto v_resetjp_6272_;
}
v_resetjp_6272_:
{
lean_object* v___x_6276_; 
if (v_isShared_6274_ == 0)
{
v___x_6276_ = v___x_6273_;
goto v_reusejp_6275_;
}
else
{
lean_object* v_reuseFailAlloc_6277_; 
v_reuseFailAlloc_6277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_a_6271_);
v___x_6276_ = v_reuseFailAlloc_6277_;
goto v_reusejp_6275_;
}
v_reusejp_6275_:
{
return v___x_6276_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitNext___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_6248_ = stack[0].m_obj;
lean_object* v___y_6249_ = stack[1].m_obj;
lean_object* v___y_6250_ = stack[2].m_obj;
lean_object* v___y_6251_ = stack[3].m_obj;
lean_object* v___y_6252_ = stack[4].m_obj;
lean_object* v___y_6253_ = stack[5].m_obj;
lean_object* v___y_6254_ = stack[6].m_obj;
lean_object* v___y_6255_ = stack[7].m_obj;
lean_object* v___y_6256_ = stack[8].m_obj;
lean_object* v___y_6257_ = stack[9].m_obj;
lean_object* v_res_6279_;
v_res_6279_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_);
stack->m_obj
 = v_res_6279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
return v_res_6291_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6292_, lean_object* v___f_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6307_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6307_, 0, v___y_6292_);
v___x_6308_ = l_Lean_Meta_Grind_Action_andThen(v___x_6307_, v___f_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
return v___x_6308_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitNext___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_6292_ = stack[0].m_obj;
lean_object* v___f_6293_ = stack[1].m_obj;
lean_object* v___y_6294_ = stack[2].m_obj;
lean_object* v___y_6295_ = stack[3].m_obj;
lean_object* v___y_6296_ = stack[4].m_obj;
lean_object* v___y_6297_ = stack[5].m_obj;
lean_object* v___y_6298_ = stack[6].m_obj;
lean_object* v___y_6299_ = stack[7].m_obj;
lean_object* v___y_6300_ = stack[8].m_obj;
lean_object* v___y_6301_ = stack[9].m_obj;
lean_object* v___y_6302_ = stack[10].m_obj;
lean_object* v___y_6303_ = stack[11].m_obj;
lean_object* v___y_6304_ = stack[12].m_obj;
lean_object* v___y_6305_ = stack[13].m_obj;
lean_object* v_res_6309_;
v_res_6309_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6292_, v___f_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
stack->m_obj
 = v_res_6309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6310_, lean_object* v___f_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_){
_start:
{
lean_object* v_res_6325_; 
v_res_6325_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6310_, v___f_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
lean_dec(v___y_6323_);
lean_dec_ref(v___y_6322_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec(v___y_6319_);
lean_dec_ref(v___y_6318_);
lean_dec(v___y_6317_);
lean_dec_ref(v___y_6316_);
lean_dec(v___y_6315_);
return v_res_6325_;
}
}
lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6327_, uint8_t v_compress_6328_, lean_object* v_goal_6329_, lean_object* v_kna_6330_, lean_object* v_kp_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_){
_start:
{
lean_object* v_toGoalState_6342_; lean_object* v_split_6343_; lean_object* v_mvarId_6344_; lean_object* v_candidates_6345_; lean_object* v___f_6346_; lean_object* v___f_6347_; lean_object* v___x_6348_; 
v_toGoalState_6342_ = lean_ctor_get(v_goal_6329_, 0);
v_split_6343_ = lean_ctor_get(v_toGoalState_6342_, 14);
v_mvarId_6344_ = lean_ctor_get(v_goal_6329_, 1);
lean_inc(v_mvarId_6344_);
v_candidates_6345_ = lean_ctor_get(v_split_6343_, 1);
lean_inc(v_candidates_6345_);
v___f_6346_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6347_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6347_, 0, v_goal_6329_);
v___x_6348_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6344_, v___f_6347_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_);
if (lean_obj_tag(v___x_6348_) == 0)
{
lean_object* v_a_6349_; lean_object* v_fst_6350_; 
v_a_6349_ = lean_ctor_get(v___x_6348_, 0);
lean_inc(v_a_6349_);
lean_dec_ref_known(v___x_6348_, 1);
v_fst_6350_ = lean_ctor_get(v_a_6349_, 0);
if (lean_obj_tag(v_fst_6350_) == 1)
{
lean_object* v_snd_6351_; lean_object* v_c_6352_; lean_object* v_numCases_6353_; uint8_t v_isRec_6354_; lean_object* v___y_6356_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; uint8_t v___x_6369_; 
lean_inc_ref(v_fst_6350_);
v_snd_6351_ = lean_ctor_get(v_a_6349_, 1);
lean_inc(v_snd_6351_);
lean_dec(v_a_6349_);
v_c_6352_ = lean_ctor_get(v_fst_6350_, 0);
lean_inc_ref(v_c_6352_);
v_numCases_6353_ = lean_ctor_get(v_fst_6350_, 1);
lean_inc(v_numCases_6353_);
v_isRec_6354_ = lean_ctor_get_uint8(v_fst_6350_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6350_, 2);
v___x_6364_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6352_);
v___x_6365_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6351_, v___x_6364_);
lean_dec_ref(v___x_6364_);
v___x_6366_ = lean_unsigned_to_nat(1u);
v___x_6369_ = lean_nat_dec_lt(v___x_6366_, v_numCases_6353_);
if (v___x_6369_ == 0)
{
if (v_isRec_6354_ == 0)
{
v___y_6356_ = v___x_6365_;
goto v___jp_6355_;
}
else
{
goto v___jp_6367_;
}
}
else
{
goto v___jp_6367_;
}
v___jp_6355_:
{
lean_object* v___f_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v___f_6357_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6357_, 0, v___y_6356_);
lean_closure_set(v___f_6357_, 1, v___f_6346_);
v___x_6358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6358_, 0, v_candidates_6345_);
v___x_6359_ = lean_box(v_isRec_6354_);
v___x_6360_ = lean_box(v_stopAtFirstFailure_6327_);
v___x_6361_ = lean_box(v_compress_6328_);
v___x_6362_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6362_, 0, v_c_6352_);
lean_closure_set(v___x_6362_, 1, v_numCases_6353_);
lean_closure_set(v___x_6362_, 2, v___x_6359_);
lean_closure_set(v___x_6362_, 3, v___x_6360_);
lean_closure_set(v___x_6362_, 4, v___x_6361_);
lean_closure_set(v___x_6362_, 5, v___x_6358_);
v___x_6363_ = l_Lean_Meta_Grind_Action_andThen(v___x_6362_, v___f_6357_, v_snd_6351_, v_kna_6330_, v_kp_6331_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_);
return v___x_6363_;
}
v___jp_6367_:
{
lean_object* v___x_6368_; 
v___x_6368_ = lean_nat_add(v___x_6365_, v___x_6366_);
lean_dec(v___x_6365_);
v___y_6356_ = v___x_6368_;
goto v___jp_6355_;
}
}
else
{
lean_object* v_snd_6370_; lean_object* v___x_6371_; 
lean_dec(v_candidates_6345_);
lean_dec_ref(v_kp_6331_);
v_snd_6370_ = lean_ctor_get(v_a_6349_, 1);
lean_inc(v_snd_6370_);
lean_dec(v_a_6349_);
lean_inc(v_a_6340_);
lean_inc_ref(v_a_6339_);
lean_inc(v_a_6338_);
lean_inc_ref(v_a_6337_);
lean_inc(v_a_6336_);
lean_inc_ref(v_a_6335_);
lean_inc(v_a_6334_);
lean_inc_ref(v_a_6333_);
lean_inc(v_a_6332_);
v___x_6371_ = lean_apply_11(v_kna_6330_, v_snd_6370_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, lean_box(0));
return v___x_6371_;
}
}
else
{
lean_object* v_a_6372_; lean_object* v___x_6374_; uint8_t v_isShared_6375_; uint8_t v_isSharedCheck_6379_; 
lean_dec(v_candidates_6345_);
lean_dec_ref(v_kp_6331_);
lean_dec_ref(v_kna_6330_);
v_a_6372_ = lean_ctor_get(v___x_6348_, 0);
v_isSharedCheck_6379_ = !lean_is_exclusive(v___x_6348_);
if (v_isSharedCheck_6379_ == 0)
{
v___x_6374_ = v___x_6348_;
v_isShared_6375_ = v_isSharedCheck_6379_;
goto v_resetjp_6373_;
}
else
{
lean_inc(v_a_6372_);
lean_dec(v___x_6348_);
v___x_6374_ = lean_box(0);
v_isShared_6375_ = v_isSharedCheck_6379_;
goto v_resetjp_6373_;
}
v_resetjp_6373_:
{
lean_object* v___x_6377_; 
if (v_isShared_6375_ == 0)
{
v___x_6377_ = v___x_6374_;
goto v_reusejp_6376_;
}
else
{
lean_object* v_reuseFailAlloc_6378_; 
v_reuseFailAlloc_6378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6378_, 0, v_a_6372_);
v___x_6377_ = v_reuseFailAlloc_6378_;
goto v_reusejp_6376_;
}
v_reusejp_6376_:
{
return v___x_6377_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_splitNext_0interp(lean_interpreter_value* stack)
{
uint8_t v_stopAtFirstFailure_6327_ = stack[0].m_num;
uint8_t v_compress_6328_ = stack[1].m_num;
lean_object* v_goal_6329_ = stack[2].m_obj;
lean_object* v_kna_6330_ = stack[3].m_obj;
lean_object* v_kp_6331_ = stack[4].m_obj;
lean_object* v_a_6332_ = stack[5].m_obj;
lean_object* v_a_6333_ = stack[6].m_obj;
lean_object* v_a_6334_ = stack[7].m_obj;
lean_object* v_a_6335_ = stack[8].m_obj;
lean_object* v_a_6336_ = stack[9].m_obj;
lean_object* v_a_6337_ = stack[10].m_obj;
lean_object* v_a_6338_ = stack[11].m_obj;
lean_object* v_a_6339_ = stack[12].m_obj;
lean_object* v_a_6340_ = stack[13].m_obj;
lean_object* v_res_6380_;
v_res_6380_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_6327_, v_compress_6328_, v_goal_6329_, v_kna_6330_, v_kp_6331_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_);
stack->m_obj
 = v_res_6380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6381_, lean_object* v_compress_6382_, lean_object* v_goal_6383_, lean_object* v_kna_6384_, lean_object* v_kp_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6396_; uint8_t v_compress_boxed_6397_; lean_object* v_res_6398_; 
v_stopAtFirstFailure_boxed_6396_ = lean_unbox(v_stopAtFirstFailure_6381_);
v_compress_boxed_6397_ = lean_unbox(v_compress_6382_);
v_res_6398_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6396_, v_compress_boxed_6397_, v_goal_6383_, v_kna_6384_, v_kp_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_);
lean_dec(v_a_6394_);
lean_dec_ref(v_a_6393_);
lean_dec(v_a_6392_);
lean_dec_ref(v_a_6391_);
lean_dec(v_a_6390_);
lean_dec_ref(v_a_6389_);
lean_dec(v_a_6388_);
lean_dec_ref(v_a_6387_);
lean_dec(v_a_6386_);
return v_res_6398_;
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
