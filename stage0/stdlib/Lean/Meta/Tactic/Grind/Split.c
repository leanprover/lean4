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
v_split_829_ = lean_ctor_get(v_toGoalState_828_, 15);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__22));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__24));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__26));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1084_, lean_object* v_declHint_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_env_1090_; uint8_t v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_st_ref_get(v___y_1086_);
v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1090_);
lean_dec(v___x_1089_);
v___x_1091_ = l_Lean_Name_isAnonymous(v_declHint_1085_);
if (v___x_1091_ == 0)
{
uint8_t v_isExporting_1092_; 
v_isExporting_1092_ = lean_ctor_get_uint8(v_env_1090_, sizeof(void*)*13);
if (v_isExporting_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref(v_env_1090_);
lean_dec(v_declHint_1085_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_msg_1084_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
lean_inc_ref(v_env_1090_);
v___x_1094_ = l_Lean_Environment_setExporting(v_env_1090_, v___x_1091_);
lean_inc(v_declHint_1085_);
lean_inc_ref(v___x_1094_);
v___x_1095_ = l_Lean_Environment_contains(v___x_1094_, v_declHint_1085_, v_isExporting_1092_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_env_1090_);
lean_dec(v_declHint_1085_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_msg_1084_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_c_1102_; lean_object* v___x_1103_; 
v___x_1097_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1099_ = l_Lean_Options_empty;
v___x_1100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1094_);
lean_ctor_set(v___x_1100_, 1, v___x_1097_);
lean_ctor_set(v___x_1100_, 2, v___x_1098_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
lean_inc(v_declHint_1085_);
v___x_1101_ = l_Lean_MessageData_ofConstName(v_declHint_1085_, v___x_1091_);
v_c_1102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1102_, 0, v___x_1100_);
lean_ctor_set(v_c_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1090_, v_declHint_1085_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec_ref(v_env_1090_);
lean_dec(v_declHint_1085_);
v___x_1104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_c_1102_);
v___x_1106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_MessageData_note(v___x_1107_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_msg_1084_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
else
{
lean_object* v_val_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1167_; 
v_val_1111_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1113_ = v___x_1103_;
v_isShared_1114_ = v_isSharedCheck_1167_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_val_1111_);
lean_dec(v___x_1103_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1167_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v_modules_1116_; lean_object* v_moduleNames_1117_; lean_object* v_mod_1118_; uint8_t v___y_1120_; uint8_t v___x_1150_; 
v___x_1115_ = l_Lean_Environment_header(v_env_1090_);
lean_dec_ref(v_env_1090_);
v_modules_1116_ = lean_ctor_get(v___x_1115_, 3);
lean_inc_ref(v_modules_1116_);
v_moduleNames_1117_ = lean_ctor_get(v___x_1115_, 4);
lean_inc_ref(v_moduleNames_1117_);
lean_dec_ref(v___x_1115_);
v_mod_1118_ = lean_array_get(v___x_1088_, v_moduleNames_1117_, v_val_1111_);
lean_dec_ref(v_moduleNames_1117_);
v___x_1150_ = l_Lean_isPrivateName(v_declHint_1085_);
lean_dec(v_declHint_1085_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_get_size(v_modules_1116_);
v___x_1152_ = lean_nat_dec_lt(v_val_1111_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_dec_ref(v_modules_1116_);
lean_dec(v_val_1111_);
v___y_1120_ = v___x_1150_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1153_; lean_object* v_toImport_1154_; uint8_t v_isExported_1155_; 
v___x_1153_ = lean_array_fget(v_modules_1116_, v_val_1111_);
lean_dec(v_val_1111_);
lean_dec_ref(v_modules_1116_);
v_toImport_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_toImport_1154_);
lean_dec(v___x_1153_);
v_isExported_1155_ = lean_ctor_get_uint8(v_toImport_1154_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1154_);
v___y_1120_ = v_isExported_1155_;
goto v___jp_1119_;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_modules_1116_);
lean_del_object(v___x_1113_);
lean_dec(v_val_1111_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_c_1102_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__25);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofName(v_mod_1118_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__27);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_note(v___x_1163_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_msg_1084_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
v___jp_1119_:
{
if (v___y_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_c_1102_);
v___x_1123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_MessageData_ofName(v_mod_1118_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_note(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_msg_1084_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1130_);
v___x_1132_ = v___x_1113_;
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
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_c_1102_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofName(v_mod_1118_);
lean_inc_ref(v___x_1138_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1138_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__23);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_note(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_msg_1084_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1146_);
v___x_1148_ = v___x_1113_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
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
lean_object* v___x_1168_; 
lean_dec_ref(v_env_1090_);
lean_dec(v_declHint_1085_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_msg_1084_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1169_, v_declHint_1170_, v___y_1171_);
lean_dec(v___y_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
v___x_1187_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1174_, v_declHint_1175_, v___y_1185_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = l_Lean_unknownIdentifierMessageTag;
v___x_1193_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_a_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1198_, lean_object* v_declHint_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1198_, v_declHint_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec(v___y_1200_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_env_1219_; uint8_t v___x_1220_; lean_object* v_env_1221_; lean_object* v___x_1222_; lean_object* v_toCold_1223_; lean_object* v_mctx_1224_; lean_object* v_lctx_1225_; lean_object* v_options_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1218_ = lean_st_ref_get(v___y_1216_);
v_env_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_env_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = 0;
v_env_1221_ = l_Lean_Environment_setRecordingDeps(v_env_1219_, v___x_1220_);
v___x_1222_ = lean_st_ref_get(v___y_1214_);
v_toCold_1223_ = lean_ctor_get(v___y_1215_, 0);
v_mctx_1224_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_mctx_1224_);
lean_dec(v___x_1222_);
v_lctx_1225_ = lean_ctor_get(v___y_1213_, 2);
v_options_1226_ = lean_ctor_get(v_toCold_1223_, 2);
lean_inc_ref(v_options_1226_);
lean_inc_ref(v_lctx_1225_);
v___x_1227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1227_, 0, v_env_1221_);
lean_ctor_set(v___x_1227_, 1, v_mctx_1224_);
lean_ctor_set(v___x_1227_, 2, v_lctx_1225_);
lean_ctor_set(v___x_1227_, 3, v_options_1226_);
v___x_1228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v_msgData_1212_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_ref_1243_; lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
v_ref_1243_ = lean_ctor_get(v___y_1240_, 2);
v___x_1244_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_inc(v_ref_1243_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_ref_1243_);
lean_ctor_set(v___x_1249_, 1, v_a_1245_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 1);
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1261_, lean_object* v_msg_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_toCold_1274_; lean_object* v_currRecDepth_1275_; lean_object* v_ref_1276_; uint16_t v_optionFlags_1277_; uint8_t v_suppressElabErrors_1278_; uint8_t v_isRecordingDeps_1279_; lean_object* v_ref_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_toCold_1274_ = lean_ctor_get(v___y_1271_, 0);
v_currRecDepth_1275_ = lean_ctor_get(v___y_1271_, 1);
v_ref_1276_ = lean_ctor_get(v___y_1271_, 2);
v_optionFlags_1277_ = lean_ctor_get_uint16(v___y_1271_, sizeof(void*)*3);
v_suppressElabErrors_1278_ = lean_ctor_get_uint8(v___y_1271_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1279_ = lean_ctor_get_uint8(v___y_1271_, sizeof(void*)*3 + 3);
v_ref_1280_ = l_Lean_replaceRef(v_ref_1261_, v_ref_1276_);
lean_inc(v_currRecDepth_1275_);
lean_inc_ref(v_toCold_1274_);
v___x_1281_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1281_, 0, v_toCold_1274_);
lean_ctor_set(v___x_1281_, 1, v_currRecDepth_1275_);
lean_ctor_set(v___x_1281_, 2, v_ref_1280_);
lean_ctor_set_uint16(v___x_1281_, sizeof(void*)*3, v_optionFlags_1277_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 2, v_suppressElabErrors_1278_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 3, v_isRecordingDeps_1279_);
v___x_1282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1262_, v___y_1269_, v___y_1270_, v___x_1281_, v___y_1272_);
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
uint8_t v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; uint8_t v___y_1671_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___x_1799_; 
lean_inc_ref(v_e_1533_);
v___x_1799_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1533_, v_a_1541_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1828_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1828_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1828_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = l_Lean_Expr_cleanupAnnotations(v_a_1800_);
v___x_1805_ = l_Lean_Expr_isApp(v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1802_);
v___y_1787_ = v_a_1534_;
v___y_1788_ = v_a_1535_;
v___y_1789_ = v_a_1536_;
v___y_1790_ = v_a_1537_;
v___y_1791_ = v_a_1538_;
v___y_1792_ = v_a_1539_;
v___y_1793_ = v_a_1540_;
v___y_1794_ = v_a_1541_;
v___y_1795_ = v_a_1542_;
v___y_1796_ = v_a_1543_;
goto v___jp_1786_;
}
else
{
lean_object* v_arg_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_arg_1806_ = lean_ctor_get(v___x_1804_, 1);
lean_inc_ref(v_arg_1806_);
v___x_1807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1804_);
v___x_1808_ = l_Lean_Expr_isApp(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_arg_1806_);
lean_del_object(v___x_1802_);
v___y_1787_ = v_a_1534_;
v___y_1788_ = v_a_1535_;
v___y_1789_ = v_a_1536_;
v___y_1790_ = v_a_1537_;
v___y_1791_ = v_a_1538_;
v___y_1792_ = v_a_1539_;
v___y_1793_ = v_a_1540_;
v___y_1794_ = v_a_1541_;
v___y_1795_ = v_a_1542_;
v___y_1796_ = v_a_1543_;
goto v___jp_1786_;
}
else
{
lean_object* v_arg_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_arg_1809_ = lean_ctor_get(v___x_1807_, 1);
lean_inc_ref(v_arg_1809_);
v___x_1810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1807_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1812_ = l_Lean_Expr_isConstOf(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1814_ = l_Lean_Expr_isConstOf(v___x_1810_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = l_Lean_Expr_isApp(v___x_1810_);
if (v___x_1815_ == 0)
{
lean_dec_ref(v___x_1810_);
lean_dec_ref(v_arg_1809_);
lean_dec_ref(v_arg_1806_);
lean_del_object(v___x_1802_);
v___y_1787_ = v_a_1534_;
v___y_1788_ = v_a_1535_;
v___y_1789_ = v_a_1536_;
v___y_1790_ = v_a_1537_;
v___y_1791_ = v_a_1538_;
v___y_1792_ = v_a_1539_;
v___y_1793_ = v_a_1540_;
v___y_1794_ = v_a_1541_;
v___y_1795_ = v_a_1542_;
v___y_1796_ = v_a_1543_;
goto v___jp_1786_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1810_);
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1818_ = l_Lean_Expr_isConstOf(v___x_1816_, v___x_1817_);
lean_dec_ref(v___x_1816_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v_arg_1809_);
lean_dec_ref(v_arg_1806_);
lean_del_object(v___x_1802_);
v___y_1787_ = v_a_1534_;
v___y_1788_ = v_a_1535_;
v___y_1789_ = v_a_1536_;
v___y_1790_ = v_a_1537_;
v___y_1791_ = v_a_1538_;
v___y_1792_ = v_a_1539_;
v___y_1793_ = v_a_1540_;
v___y_1794_ = v_a_1541_;
v___y_1795_ = v_a_1542_;
v___y_1796_ = v_a_1543_;
goto v___jp_1786_;
}
else
{
uint8_t v___x_1819_; 
lean_inc_ref(v_e_1533_);
v___x_1819_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1533_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec_ref(v_arg_1809_);
lean_dec_ref(v_arg_1806_);
lean_dec_ref(v_e_1533_);
v___x_1820_ = lean_unsigned_to_nat(2u);
v___x_1821_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*1, v___x_1819_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*1 + 1, v___x_1819_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1821_);
v___x_1823_ = v___x_1802_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
else
{
lean_object* v___x_1825_; 
lean_del_object(v___x_1802_);
v___x_1825_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1533_, v_arg_1809_, v_arg_1806_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1825_;
}
}
}
}
else
{
lean_object* v___x_1826_; 
lean_dec_ref(v___x_1810_);
lean_del_object(v___x_1802_);
v___x_1826_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1533_, v_arg_1809_, v_arg_1806_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1826_;
}
}
else
{
lean_object* v___x_1827_; 
lean_dec_ref(v___x_1810_);
lean_del_object(v___x_1802_);
v___x_1827_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1533_, v_arg_1809_, v_arg_1806_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1827_;
}
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_e_1533_);
v_a_1829_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1799_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1799_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
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
uint8_t v___x_1566_; 
v___x_1566_ = l_Lean_Expr_isFVar(v_e_1533_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v_e_1533_);
v___x_1567_ = lean_box(1);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
else
{
lean_object* v___x_1569_; 
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc_ref(v_e_1533_);
v___x_1569_ = lean_infer_type(v_e_1533_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_Meta_whnfD(v_a_1570_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_n(v_a_1572_, 2);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1574_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_indentExpr(v_a_1572_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_Expr_getAppFn(v_a_1572_);
lean_dec(v_a_1572_);
if (lean_obj_tag(v___x_1580_) == 4)
{
lean_object* v_declName_1581_; lean_object* v___x_1582_; 
v_declName_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_declName_1581_);
lean_dec_ref_known(v___x_1580_, 2);
v___x_1582_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1581_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1615_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1615_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1615_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
if (lean_obj_tag(v_a_1583_) == 5)
{
lean_object* v_val_1587_; lean_object* v_ctors_1588_; uint8_t v_isRec_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec_ref_known(v___x_1579_, 2);
v_val_1587_ = lean_ctor_get(v_a_1583_, 0);
lean_inc_ref(v_val_1587_);
lean_dec_ref_known(v_a_1583_, 1);
v_ctors_1588_ = lean_ctor_get(v_val_1587_, 4);
lean_inc(v_ctors_1588_);
v_isRec_1589_ = lean_ctor_get_uint8(v_val_1587_, sizeof(void*)*6);
lean_dec_ref(v_val_1587_);
v___x_1590_ = l_List_lengthTR___redArg(v_ctors_1588_);
lean_dec(v_ctors_1588_);
v___x_1591_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*1, v_isRec_1589_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*1 + 1, v___y_1555_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1591_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v___x_1595_; 
lean_del_object(v___x_1585_);
lean_dec(v_a_1583_);
v___x_1595_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1560_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v_verbose_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v_verbose_1597_ = lean_ctor_get_uint8(v_a_1596_, 0);
lean_dec(v_a_1596_);
if (v_verbose_1597_ == 0)
{
lean_dec_ref_known(v___x_1579_, 2);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Meta_Sym_reportIssue(v___x_1579_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_dec_ref_known(v___x_1598_, 1);
goto v___jp_1548_;
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref_known(v___x_1579_, 2);
v_a_1607_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1595_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1595_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref_known(v___x_1579_, 2);
v_a_1616_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1582_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1582_);
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
else
{
lean_object* v___x_1624_; 
lean_dec_ref(v___x_1580_);
v___x_1624_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1560_);
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
lean_dec_ref_known(v___x_1579_, 2);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Sym_reportIssue(v___x_1579_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
goto v___jp_1551_;
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
lean_dec_ref_known(v___x_1579_, 2);
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
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v_e_1533_);
v_a_1644_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1571_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1571_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_e_1533_);
v_a_1652_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1569_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1569_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
v___jp_1660_:
{
if (v___y_1671_ == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1533_, v___y_1663_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; uint8_t v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = lean_unbox(v_a_1673_);
lean_dec(v_a_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
lean_inc_ref(v_e_1533_);
v___x_1675_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1533_, v___y_1663_, v___y_1667_, v___y_1662_, v___y_1670_, v___y_1668_, v___y_1666_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1735_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1735_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1735_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_unbox(v_a_1676_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v_env_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_st_ref_get(v___y_1664_);
v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1681_);
v___x_1683_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1682_, v_e_1533_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1690_; 
lean_dec_ref(v_e_1533_);
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1684_);
lean_dec(v_val_1684_);
v___x_1686_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
v___x_1687_ = lean_unbox(v_a_1676_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*1, v___x_1687_);
v___x_1688_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*1 + 1, v___x_1688_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1686_);
v___x_1690_ = v___x_1678_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1686_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
else
{
lean_object* v___x_1692_; 
lean_dec(v___x_1683_);
lean_del_object(v___x_1678_);
v___x_1692_ = l_Lean_Expr_getAppFn(v_e_1533_);
if (lean_obj_tag(v___x_1692_) == 4)
{
lean_object* v_declName_1693_; lean_object* v___x_1694_; 
v_declName_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_declName_1693_);
lean_dec_ref_known(v___x_1692_, 2);
v___x_1694_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1693_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
if (lean_obj_tag(v_a_1695_) == 1)
{
lean_object* v_val_1696_; lean_object* v___x_1697_; 
v_val_1696_ = lean_ctor_get(v_a_1695_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_a_1695_, 1);
lean_inc_ref(v_e_1533_);
v___x_1697_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1533_, v___y_1663_, v___y_1668_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1712_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1712_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1712_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_unbox(v_a_1698_);
lean_dec(v_a_1698_);
if (v___x_1702_ == 0)
{
uint8_t v___x_1703_; 
lean_del_object(v___x_1700_);
lean_dec(v_val_1696_);
v___x_1703_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
v___y_1555_ = v___x_1703_;
v___y_1556_ = v___y_1663_;
v___y_1557_ = v___y_1667_;
v___y_1558_ = v___y_1662_;
v___y_1559_ = v___y_1670_;
v___y_1560_ = v___y_1668_;
v___y_1561_ = v___y_1666_;
v___y_1562_ = v___y_1661_;
v___y_1563_ = v___y_1665_;
v___y_1564_ = v___y_1669_;
v___y_1565_ = v___y_1664_;
goto v___jp_1554_;
}
else
{
lean_object* v_ctors_1704_; uint8_t v_isRec_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1710_; 
lean_dec_ref(v_e_1533_);
v_ctors_1704_ = lean_ctor_get(v_val_1696_, 4);
lean_inc(v_ctors_1704_);
v_isRec_1705_ = lean_ctor_get_uint8(v_val_1696_, sizeof(void*)*6);
lean_dec(v_val_1696_);
v___x_1706_ = l_List_lengthTR___redArg(v_ctors_1704_);
lean_dec(v_ctors_1704_);
v___x_1707_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1, v_isRec_1705_);
v___x_1708_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1 + 1, v___x_1708_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1710_ = v___x_1700_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1707_);
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
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_val_1696_);
lean_dec(v_a_1676_);
lean_dec_ref(v_e_1533_);
v_a_1713_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1697_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1697_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
uint8_t v___x_1721_; 
lean_dec(v_a_1695_);
v___x_1721_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
v___y_1555_ = v___x_1721_;
v___y_1556_ = v___y_1663_;
v___y_1557_ = v___y_1667_;
v___y_1558_ = v___y_1662_;
v___y_1559_ = v___y_1670_;
v___y_1560_ = v___y_1668_;
v___y_1561_ = v___y_1666_;
v___y_1562_ = v___y_1661_;
v___y_1563_ = v___y_1665_;
v___y_1564_ = v___y_1669_;
v___y_1565_ = v___y_1664_;
goto v___jp_1554_;
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1676_);
lean_dec_ref(v_e_1533_);
v_a_1722_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1694_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1694_);
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
uint8_t v___x_1730_; 
lean_dec_ref(v___x_1692_);
v___x_1730_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
v___y_1555_ = v___x_1730_;
v___y_1556_ = v___y_1663_;
v___y_1557_ = v___y_1667_;
v___y_1558_ = v___y_1662_;
v___y_1559_ = v___y_1670_;
v___y_1560_ = v___y_1668_;
v___y_1561_ = v___y_1666_;
v___y_1562_ = v___y_1661_;
v___y_1563_ = v___y_1665_;
v___y_1564_ = v___y_1669_;
v___y_1565_ = v___y_1664_;
goto v___jp_1554_;
}
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_dec(v_a_1676_);
lean_dec_ref(v_e_1533_);
v___x_1731_ = lean_box(0);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1731_);
v___x_1733_ = v___x_1678_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
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
lean_dec_ref(v_e_1533_);
v_a_1736_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1675_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1675_);
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
lean_object* v_toCold_1744_; lean_object* v_options_1745_; uint8_t v_hasTrace_1746_; 
v_toCold_1744_ = lean_ctor_get(v___y_1669_, 0);
v_options_1745_ = lean_ctor_get(v_toCold_1744_, 2);
v_hasTrace_1746_ = lean_ctor_get_uint8(v_options_1745_, sizeof(void*)*1);
if (v_hasTrace_1746_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v_inheritedTraceOptions_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_inheritedTraceOptions_1747_ = lean_ctor_get(v_toCold_1744_, 11);
v___x_1748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1747_, v_options_1745_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Meta_Grind_updateLastTag(v___y_1663_, v___y_1667_, v___y_1662_, v___y_1670_, v___y_1668_, v___y_1666_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec_ref_known(v___x_1751_, 1);
v___x_1752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1753_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1748_, v___x_1754_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref_known(v___x_1755_, 1);
goto v___jp_1545_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_e_1533_);
v_a_1764_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1751_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1751_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_e_1533_);
v_a_1772_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1672_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1672_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = l_Lean_Expr_getAppNumArgs(v_e_1533_);
v___x_1782_ = lean_nat_sub(v___x_1781_, v___x_1780_);
lean_dec(v___x_1781_);
v___x_1783_ = lean_nat_sub(v___x_1782_, v___x_1780_);
lean_dec(v___x_1782_);
v___x_1784_ = l_Lean_Expr_getRevArg_x21(v_e_1533_, v___x_1783_);
lean_dec_ref(v_e_1533_);
v___x_1785_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1784_, v___y_1663_, v___y_1668_, v___y_1661_, v___y_1665_, v___y_1669_, v___y_1664_);
return v___x_1785_;
}
}
v___jp_1786_:
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Meta_Grind_isIte(v_e_1533_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Meta_Grind_isDIte(v_e_1533_);
v___y_1661_ = v___y_1793_;
v___y_1662_ = v___y_1789_;
v___y_1663_ = v___y_1787_;
v___y_1664_ = v___y_1796_;
v___y_1665_ = v___y_1794_;
v___y_1666_ = v___y_1792_;
v___y_1667_ = v___y_1788_;
v___y_1668_ = v___y_1791_;
v___y_1669_ = v___y_1795_;
v___y_1670_ = v___y_1790_;
v___y_1671_ = v___x_1798_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___y_1793_;
v___y_1662_ = v___y_1789_;
v___y_1663_ = v___y_1787_;
v___y_1664_ = v___y_1796_;
v___y_1665_ = v___y_1794_;
v___y_1666_ = v___y_1792_;
v___y_1667_ = v___y_1788_;
v___y_1668_ = v___y_1791_;
v___y_1669_ = v___y_1795_;
v___y_1670_ = v___y_1790_;
v___y_1671_ = v___x_1797_;
goto v___jp_1660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec(v_a_1838_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1850_, v_msg_1851_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1864_, v_msg_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1878_, lean_object* v_constName_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_constName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1892_, v_constName_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec(v___y_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1906_, lean_object* v_ref_1907_, lean_object* v_constName_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1907_, v_constName_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_ref_1922_, lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1921_, v_ref_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec(v_ref_1922_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1936_, lean_object* v_ref_1937_, lean_object* v_msg_1938_, lean_object* v_declHint_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1937_, v_msg_1938_, v_declHint_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_ref_1953_, lean_object* v_msg_1954_, lean_object* v_declHint_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1952_, v_ref_1953_, v_msg_1954_, v_declHint_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
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
lean_dec(v_ref_1953_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1968_, lean_object* v_declHint_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1968_, v_declHint_1969_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1982_, lean_object* v_declHint_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1982_, v_declHint_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1996_, lean_object* v_ref_1997_, lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1997_, v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_ref_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2011_, v_ref_2012_, v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
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
lean_dec(v_ref_2012_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2027_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_msg_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2040_, v_msg_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec(v___y_2042_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2054_, lean_object* v_x_2055_){
_start:
{
if (lean_obj_tag(v_x_2055_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_box(0);
return v___x_2056_;
}
else
{
lean_object* v_key_2057_; lean_object* v_value_2058_; lean_object* v_tail_2059_; uint8_t v___y_2061_; lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v_fst_2066_; lean_object* v_snd_2067_; uint8_t v___x_2068_; 
v_key_2057_ = lean_ctor_get(v_x_2055_, 0);
v_value_2058_ = lean_ctor_get(v_x_2055_, 1);
v_tail_2059_ = lean_ctor_get(v_x_2055_, 2);
v_fst_2064_ = lean_ctor_get(v_key_2057_, 0);
v_snd_2065_ = lean_ctor_get(v_key_2057_, 1);
v_fst_2066_ = lean_ctor_get(v_a_2054_, 0);
v_snd_2067_ = lean_ctor_get(v_a_2054_, 1);
v___x_2068_ = lean_expr_eqv(v_fst_2064_, v_fst_2066_);
if (v___x_2068_ == 0)
{
v___y_2061_ = v___x_2068_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_expr_eqv(v_snd_2065_, v_snd_2067_);
v___y_2061_ = v___x_2069_;
goto v___jp_2060_;
}
v___jp_2060_:
{
if (v___y_2061_ == 0)
{
v_x_2055_ = v_tail_2059_;
goto _start;
}
else
{
lean_object* v___x_2063_; 
lean_inc(v_value_2058_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_value_2058_);
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2070_, v_x_2071_);
lean_dec(v_x_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_buckets_2075_; lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v_fold_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_buckets_2075_ = lean_ctor_get(v_m_2073_, 1);
v_fst_2076_ = lean_ctor_get(v_a_2074_, 0);
v_snd_2077_ = lean_ctor_get(v_a_2074_, 1);
v___x_2078_ = lean_array_get_size(v_buckets_2075_);
v___x_2079_ = l_Lean_Expr_hash(v_fst_2076_);
v___x_2080_ = l_Lean_Expr_hash(v_snd_2077_);
v___x_2081_ = lean_uint64_mix_hash(v___x_2079_, v___x_2080_);
v___x_2082_ = 32ULL;
v___x_2083_ = lean_uint64_shift_right(v___x_2081_, v___x_2082_);
v_fold_2084_ = lean_uint64_xor(v___x_2081_, v___x_2083_);
v___x_2085_ = 16ULL;
v___x_2086_ = lean_uint64_shift_right(v_fold_2084_, v___x_2085_);
v___x_2087_ = lean_uint64_xor(v_fold_2084_, v___x_2086_);
v___x_2088_ = lean_uint64_to_usize(v___x_2087_);
v___x_2089_ = lean_usize_of_nat(v___x_2078_);
v___x_2090_ = ((size_t)1ULL);
v___x_2091_ = lean_usize_sub(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_usize_land(v___x_2088_, v___x_2091_);
v___x_2093_ = lean_array_uget_borrowed(v_buckets_2075_, v___x_2092_);
v___x_2094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2074_, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2095_, v_a_2096_);
lean_dec_ref(v_a_2096_);
lean_dec_ref(v_m_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2098_, uint8_t v___x_2099_, lean_object* v_fst_2100_, lean_object* v_snd_2101_, lean_object* v___x_2102_, lean_object* v_____r_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2115_ = lean_unsigned_to_nat(2u);
v___x_2116_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*1, v_a_2098_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*1 + 1, v___x_2099_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_fst_2100_);
lean_ctor_set(v___x_2118_, 1, v_snd_2101_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2102_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2117_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2123_ = _args[0];
lean_object* v___x_2124_ = _args[1];
lean_object* v_fst_2125_ = _args[2];
lean_object* v_snd_2126_ = _args[3];
lean_object* v___x_2127_ = _args[4];
lean_object* v_____r_2128_ = _args[5];
lean_object* v___y_2129_ = _args[6];
lean_object* v___y_2130_ = _args[7];
lean_object* v___y_2131_ = _args[8];
lean_object* v___y_2132_ = _args[9];
lean_object* v___y_2133_ = _args[10];
lean_object* v___y_2134_ = _args[11];
lean_object* v___y_2135_ = _args[12];
lean_object* v___y_2136_ = _args[13];
lean_object* v___y_2137_ = _args[14];
lean_object* v___y_2138_ = _args[15];
lean_object* v___y_2139_ = _args[16];
_start:
{
uint8_t v_a_33765__boxed_2140_; uint8_t v___x_33766__boxed_2141_; lean_object* v_res_2142_; 
v_a_33765__boxed_2140_ = lean_unbox(v_a_2123_);
v___x_33766__boxed_2141_ = lean_unbox(v___x_2124_);
v_res_2142_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_33765__boxed_2140_, v___x_33766__boxed_2141_, v_fst_2125_, v_snd_2126_, v___x_2127_, v_____r_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v___y_2129_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2143_, lean_object* v_snd_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_____r_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2159_ = l_Lean_Expr_appFn_x21(v_fst_2143_);
v___x_2160_ = l_Lean_Expr_appFn_x21(v_snd_2144_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2145_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2146_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2166_, lean_object* v_snd_2167_, lean_object* v___x_2168_, lean_object* v___x_2169_, lean_object* v_____r_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2166_, v_snd_2167_, v___x_2168_, v___x_2169_, v_____r_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v_snd_2167_);
lean_dec(v_fst_2166_);
return v_res_2182_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___f_2184_; 
v___x_2183_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2184_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2184_, 0, v___x_2183_);
return v___f_2184_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2190_ = l_Lean_Name_append(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2209_, lean_object* v___y_2210_, lean_object* v_eq_2211_, lean_object* v_a_2212_, lean_object* v_b_2213_, lean_object* v_a_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___y_2227_; lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2370_; 
v_snd_2247_ = lean_ctor_get(v_a_2214_, 1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_a_2214_, 0);
lean_dec(v_unused_2371_);
v___x_2249_ = v_a_2214_;
v_isShared_2250_ = v_isSharedCheck_2370_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_dec(v_a_2214_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2370_;
goto v_resetjp_2248_;
}
v___jp_2226_:
{
if (lean_obj_tag(v___y_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2238_; 
v_a_2228_ = lean_ctor_get(v___y_2227_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___y_2227_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2230_ = v___y_2227_;
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___y_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
if (lean_obj_tag(v_a_2228_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; 
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2232_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v_a_2228_, 1);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v_a_2232_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v_a_2236_; 
lean_del_object(v___x_2230_);
v_a_2236_ = lean_ctor_get(v_a_2228_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_a_2228_, 1);
v_a_2214_ = v_a_2236_;
goto _start;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2239_ = lean_ctor_get(v___y_2227_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___y_2227_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___y_2227_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___y_2227_);
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
v_resetjp_2248_:
{
lean_object* v_snd_2251_; lean_object* v_fst_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2369_; 
v_snd_2251_ = lean_ctor_get(v_snd_2247_, 1);
v_fst_2252_ = lean_ctor_get(v_snd_2247_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_snd_2247_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2254_ = v_snd_2247_;
v_isShared_2255_ = v_isSharedCheck_2369_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2252_);
lean_dec(v_snd_2247_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2369_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2368_; 
v_fst_2256_ = lean_ctor_get(v_snd_2251_, 0);
v_snd_2257_ = lean_ctor_get(v_snd_2251_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_snd_2251_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2259_ = v_snd_2251_;
v_isShared_2260_ = v_isSharedCheck_2368_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_inc(v_fst_2256_);
lean_dec(v_snd_2251_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2368_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
uint8_t v___y_2262_; uint8_t v___x_2276_; 
v___x_2276_ = l_Lean_Expr_isApp(v_fst_2256_);
if (v___x_2276_ == 0)
{
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v___y_2262_ = v_a_2209_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2277_; 
v___x_2277_ = l_Lean_Expr_isApp(v_snd_2257_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v___y_2262_ = v___x_2277_;
goto v___jp_2261_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2284_; uint8_t v___x_2285_; 
lean_del_object(v___x_2259_);
lean_del_object(v___x_2254_);
lean_del_object(v___x_2249_);
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = lean_nat_sub(v_fst_2252_, v___x_2279_);
lean_dec(v_fst_2252_);
v___f_2284_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2210_);
lean_inc(v___x_2280_);
v___x_2285_ = l_List_elem___redArg(v___f_2284_, v___x_2280_, v___y_2210_);
if (v___x_2285_ == 0)
{
if (v___x_2277_ == 0)
{
goto v___jp_2281_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = l_Lean_Expr_appArg_x21(v_fst_2256_);
v___x_2287_ = l_Lean_Expr_appArg_x21(v_snd_2257_);
v___x_2288_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2286_, v___x_2287_, v___y_2215_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = lean_unbox(v_a_2289_);
if (v___x_2290_ == 0)
{
lean_object* v_toCold_2291_; lean_object* v_options_2292_; lean_object* v_inheritedTraceOptions_2293_; uint8_t v_hasTrace_2294_; 
v_toCold_2291_ = lean_ctor_get(v___y_2223_, 0);
v_options_2292_ = lean_ctor_get(v_toCold_2291_, 2);
v_inheritedTraceOptions_2293_ = lean_ctor_get(v_toCold_2291_, 11);
v_hasTrace_2294_ = lean_ctor_get_uint8(v_options_2292_, sizeof(void*)*1);
if (v_hasTrace_2294_ == 0)
{
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
goto v___jp_2295_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2299_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2300_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2293_, v_options_2292_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
goto v___jp_2295_;
}
else
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Meta_Grind_updateLastTag(v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2211_, v___y_2215_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2212_);
v___x_2306_ = l_Lean_MessageData_ofExpr(v_a_2212_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_inc_ref(v_b_2213_);
v___x_2310_ = l_Lean_MessageData_ofExpr(v_b_2213_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_inc_ref(v_eq_2211_);
v___x_2314_ = l_Lean_MessageData_ofExpr(v_eq_2211_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_ofExpr(v___x_2286_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_MessageData_ofExpr(v___x_2287_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = l_Nat_reprFast(v_a_2304_);
v___x_2327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = l_Lean_MessageData_ofFormat(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2325_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2299_, v___x_2329_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
v___x_2333_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2332_, v___x_2277_, v_fst_2256_, v_snd_2257_, v___x_2280_, v_a_2331_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
v___y_2227_ = v___x_2333_;
goto v___jp_2226_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2289_);
lean_dec(v___x_2280_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2334_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2330_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2330_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2289_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
lean_dec(v___x_2280_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2342_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2303_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2303_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2289_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
lean_dec(v___x_2280_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2350_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2302_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2302_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
v___jp_2295_:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
v___x_2298_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2297_, v___x_2277_, v_fst_2256_, v_snd_2257_, v___x_2280_, v___x_2296_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
v___y_2227_ = v___x_2298_;
goto v___jp_2226_;
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_a_2289_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
v___x_2358_ = lean_box(0);
v___x_2359_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2256_, v_snd_2257_, v___x_2280_, v___x_2278_, v___x_2358_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
v___y_2227_ = v___x_2359_;
goto v___jp_2226_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2286_);
lean_dec(v___x_2280_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
lean_dec_ref(v_b_2213_);
lean_dec_ref(v_a_2212_);
lean_dec_ref(v_eq_2211_);
lean_dec(v___y_2210_);
v_a_2360_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2288_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2288_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
goto v___jp_2281_;
}
v___jp_2281_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2256_, v_snd_2257_, v___x_2280_, v___x_2278_, v___x_2282_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v_snd_2257_);
lean_dec(v_fst_2256_);
v___y_2227_ = v___x_2283_;
goto v___jp_2226_;
}
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2263_ = lean_unsigned_to_nat(2u);
v___x_2264_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1, v___y_2262_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*1 + 1, v___y_2262_);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
if (v_isShared_2260_ == 0)
{
v___x_2267_ = v___x_2259_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_fst_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_snd_2257_);
v___x_2267_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___x_2267_);
v___x_2269_ = v___x_2254_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_fst_2252_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2269_);
lean_ctor_set(v___x_2249_, 0, v___x_2265_);
v___x_2271_ = v___x_2249_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
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
lean_object* v_a_2372_ = _args[0];
lean_object* v___y_2373_ = _args[1];
lean_object* v_eq_2374_ = _args[2];
lean_object* v_a_2375_ = _args[3];
lean_object* v_b_2376_ = _args[4];
lean_object* v_a_2377_ = _args[5];
lean_object* v___y_2378_ = _args[6];
lean_object* v___y_2379_ = _args[7];
lean_object* v___y_2380_ = _args[8];
lean_object* v___y_2381_ = _args[9];
lean_object* v___y_2382_ = _args[10];
lean_object* v___y_2383_ = _args[11];
lean_object* v___y_2384_ = _args[12];
lean_object* v___y_2385_ = _args[13];
lean_object* v___y_2386_ = _args[14];
lean_object* v___y_2387_ = _args[15];
lean_object* v___y_2388_ = _args[16];
_start:
{
uint8_t v_a_33939__boxed_2389_; lean_object* v_res_2390_; 
v_a_33939__boxed_2389_ = lean_unbox(v_a_2372_);
v_res_2390_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_33939__boxed_2389_, v___y_2373_, v_eq_2374_, v_a_2375_, v_b_2376_, v_a_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2391_, lean_object* v_b_2392_, lean_object* v_eq_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
uint8_t v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2438_; lean_object* v___x_2474_; 
lean_inc_ref(v_eq_2393_);
v___x_2474_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2393_, v_a_2394_, v_a_2398_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; uint8_t v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v___x_2476_ = lean_unbox(v_a_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref_known(v___x_2474_, 1);
lean_inc_ref(v_eq_2393_);
v___x_2477_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2393_, v_a_2394_, v_a_2398_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
v___y_2438_ = v___x_2477_;
goto v___jp_2437_;
}
else
{
v___y_2438_ = v___x_2474_;
goto v___jp_2437_;
}
}
else
{
v___y_2438_ = v___x_2474_;
goto v___jp_2437_;
}
v___jp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2408_ = l_Lean_Expr_getAppNumArgs(v_a_2391_);
v___x_2409_ = lean_box(0);
lean_inc_ref(v_b_2392_);
lean_inc_ref(v_a_2391_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_a_2391_);
lean_ctor_set(v___x_2410_, 1, v_b_2392_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2408_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2409_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___y_2406_, v___y_2407_, v_eq_2393_, v_a_2391_, v_b_2392_, v___x_2412_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2428_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2428_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2428_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_fst_2418_; 
v_fst_2418_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_fst_2418_);
lean_dec(v_a_2414_);
if (lean_obj_tag(v_fst_2418_) == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2419_ = lean_unsigned_to_nat(2u);
v___x_2420_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*1, v___y_2406_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*1 + 1, v___y_2406_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2420_);
v___x_2422_ = v___x_2416_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
else
{
lean_object* v_val_2424_; lean_object* v___x_2426_; 
v_val_2424_ = lean_ctor_get(v_fst_2418_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v_fst_2418_, 1);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_val_2424_);
v___x_2426_ = v___x_2416_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_val_2424_);
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
v_a_2429_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2413_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2413_);
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
v___jp_2437_:
{
if (lean_obj_tag(v___y_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2465_; 
v_a_2439_ = lean_ctor_get(v___y_2438_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___y_2438_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2441_ = v___y_2438_;
v_isShared_2442_ = v_isSharedCheck_2465_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___y_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2465_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_unbox(v_a_2439_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v_toGoalState_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2459_; 
lean_del_object(v___x_2441_);
v___x_2444_ = lean_st_ref_get(v_a_2394_);
v_toGoalState_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2444_, 1);
lean_dec(v_unused_2460_);
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2459_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_toGoalState_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2459_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v_split_2449_; lean_object* v_argPosMap_2450_; lean_object* v___x_2452_; 
v_split_2449_ = lean_ctor_get(v_toGoalState_2445_, 15);
lean_inc_ref(v_split_2449_);
lean_dec_ref(v_toGoalState_2445_);
v_argPosMap_2450_ = lean_ctor_get(v_split_2449_, 6);
lean_inc_ref(v_argPosMap_2450_);
lean_dec_ref(v_split_2449_);
lean_inc_ref(v_b_2392_);
lean_inc_ref(v_a_2391_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_b_2392_);
lean_ctor_set(v___x_2447_, 0, v_a_2391_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2391_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_b_2392_);
v___x_2452_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2450_, v___x_2452_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v_argPosMap_2450_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_unbox(v_a_2439_);
lean_dec(v_a_2439_);
v___y_2406_ = v___x_2455_;
v___y_2407_ = v___x_2454_;
goto v___jp_2405_;
}
else
{
lean_object* v_val_2456_; uint8_t v___x_2457_; 
v_val_2456_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2457_ = lean_unbox(v_a_2439_);
lean_dec(v_a_2439_);
v___y_2406_ = v___x_2457_;
v___y_2407_ = v_val_2456_;
goto v___jp_2405_;
}
}
}
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_dec(v_a_2439_);
lean_dec_ref(v_eq_2393_);
lean_dec_ref(v_b_2392_);
lean_dec_ref(v_a_2391_);
v___x_2461_ = lean_box(0);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2461_);
v___x_2463_ = v___x_2441_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_eq_2393_);
lean_dec_ref(v_b_2392_);
lean_dec_ref(v_a_2391_);
v_a_2466_ = lean_ctor_get(v___y_2438_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___y_2438_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___y_2438_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___y_2438_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2478_, lean_object* v_b_2479_, lean_object* v_eq_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2478_, v_b_2479_, v_eq_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec(v_a_2481_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2493_, lean_object* v___y_2494_, lean_object* v_eq_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_, lean_object* v_inst_2498_, lean_object* v_a_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2493_, v___y_2494_, v_eq_2495_, v_a_2496_, v_b_2497_, v_a_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2512_ = _args[0];
lean_object* v___y_2513_ = _args[1];
lean_object* v_eq_2514_ = _args[2];
lean_object* v_a_2515_ = _args[3];
lean_object* v_b_2516_ = _args[4];
lean_object* v_inst_2517_ = _args[5];
lean_object* v_a_2518_ = _args[6];
lean_object* v___y_2519_ = _args[7];
lean_object* v___y_2520_ = _args[8];
lean_object* v___y_2521_ = _args[9];
lean_object* v___y_2522_ = _args[10];
lean_object* v___y_2523_ = _args[11];
lean_object* v___y_2524_ = _args[12];
lean_object* v___y_2525_ = _args[13];
lean_object* v___y_2526_ = _args[14];
lean_object* v___y_2527_ = _args[15];
lean_object* v___y_2528_ = _args[16];
lean_object* v___y_2529_ = _args[17];
_start:
{
uint8_t v_a_34421__boxed_2530_; lean_object* v_res_2531_; 
v_a_34421__boxed_2530_ = lean_unbox(v_a_2512_);
v_res_2531_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34421__boxed_2530_, v___y_2513_, v_eq_2514_, v_a_2515_, v_b_2516_, v_inst_2517_, v_a_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2519_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2532_, lean_object* v_m_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2533_, v_a_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2536_, lean_object* v_m_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2536_, v_m_2537_, v_a_2538_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_m_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2540_, lean_object* v_a_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2541_, v_x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2544_, lean_object* v_a_2545_, lean_object* v_x_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2544_, v_a_2545_, v_x_2546_);
lean_dec(v_x_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
uint8_t v___y_2557_; uint8_t v___y_2562_; lean_object* v___y_2563_; lean_object* v___x_2582_; 
lean_inc_ref(v_imp_2548_);
v___x_2582_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint8_t v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2599_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2599_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2599_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_box(1);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2591_);
v___x_2593_ = v___x_2588_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_box(0);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2595_);
v___x_2597_ = v___x_2588_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_a_2600_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2585_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2585_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
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
lean_object* v_binderType_2608_; lean_object* v_body_2609_; lean_object* v___y_2611_; lean_object* v___x_2639_; 
v_binderType_2608_ = lean_ctor_get(v_imp_2548_, 1);
lean_inc_ref_n(v_binderType_2608_, 2);
v_body_2609_ = lean_ctor_get(v_imp_2548_, 2);
lean_inc_ref(v_body_2609_);
lean_dec_ref(v_imp_2548_);
v___x_2639_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2608_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; uint8_t v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v___x_2641_ = lean_unbox(v_a_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; 
lean_dec_ref_known(v___x_2639_, 1);
v___x_2642_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2608_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
v___y_2611_ = v___x_2642_;
goto v___jp_2610_;
}
else
{
lean_dec_ref(v_binderType_2608_);
v___y_2611_ = v___x_2639_;
goto v___jp_2610_;
}
}
else
{
lean_dec_ref(v_binderType_2608_);
v___y_2611_ = v___x_2639_;
goto v___jp_2610_;
}
v___jp_2610_:
{
if (lean_obj_tag(v___y_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2630_; 
v_a_2612_ = lean_ctor_get(v___y_2611_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2611_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2614_ = v___y_2611_;
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___y_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_unbox(v_a_2612_);
if (v___x_2616_ == 0)
{
uint8_t v___x_2617_; 
lean_del_object(v___x_2614_);
v___x_2617_ = l_Lean_Expr_hasLooseBVars(v_body_2609_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_inc_ref(v_body_2609_);
v___x_2618_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2609_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; uint8_t v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v___x_2620_ = lean_unbox(v_a_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_dec_ref_known(v___x_2618_, 1);
v___x_2621_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2609_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
v___x_2622_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
v___y_2562_ = v___x_2622_;
v___y_2563_ = v___x_2621_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2623_; 
lean_dec_ref(v_body_2609_);
v___x_2623_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
v___y_2562_ = v___x_2623_;
v___y_2563_ = v___x_2618_;
goto v___jp_2561_;
}
}
else
{
uint8_t v___x_2624_; 
lean_dec_ref(v_body_2609_);
v___x_2624_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
v___y_2562_ = v___x_2624_;
v___y_2563_ = v___x_2618_;
goto v___jp_2561_;
}
}
else
{
uint8_t v___x_2625_; 
lean_dec_ref(v_body_2609_);
v___x_2625_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
v___y_2557_ = v___x_2625_;
goto v___jp_2556_;
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec(v_a_2612_);
lean_dec_ref(v_body_2609_);
v___x_2626_ = lean_box(0);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2626_);
v___x_2628_ = v___x_2614_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v_body_2609_);
v_a_2631_ = lean_ctor_get(v___y_2611_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___y_2611_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___y_2611_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___y_2611_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_imp_2548_);
v_a_2643_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2582_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2582_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = lean_unsigned_to_nat(2u);
v___x_2559_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*1, v___y_2557_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*1 + 1, v___y_2557_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
v___jp_2561_:
{
if (lean_obj_tag(v___y_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2573_; 
v_a_2564_ = lean_ctor_get(v___y_2563_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___y_2563_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2566_ = v___y_2563_;
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___y_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_unbox(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2568_ == 0)
{
lean_del_object(v___x_2566_);
v___y_2557_ = v___y_2562_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_box(0);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2569_);
v___x_2571_ = v___x_2566_;
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
v_a_2574_ = lean_ctor_get(v___y_2563_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___y_2563_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___y_2563_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___y_2563_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2660_, lean_object* v_h_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2660_, v_a_2662_, v_a_2666_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2674_, lean_object* v_h_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2674_, v_h_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
switch(lean_obj_tag(v_s_2688_))
{
case 0:
{
lean_object* v_e_2700_; lean_object* v___x_2701_; 
v_e_2700_ = lean_ctor_get(v_s_2688_, 0);
lean_inc_ref(v_e_2700_);
lean_dec_ref_known(v_s_2688_, 2);
v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2700_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2701_;
}
case 1:
{
lean_object* v_e_2702_; lean_object* v___x_2703_; 
v_e_2702_ = lean_ctor_get(v_s_2688_, 0);
lean_inc_ref(v_e_2702_);
lean_dec_ref_known(v_s_2688_, 2);
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2702_, v_a_2689_, v_a_2693_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2703_;
}
default: 
{
lean_object* v_a_2704_; lean_object* v_b_2705_; lean_object* v_eq_2706_; lean_object* v___x_2707_; 
v_a_2704_ = lean_ctor_get(v_s_2688_, 0);
lean_inc_ref(v_a_2704_);
v_b_2705_ = lean_ctor_get(v_s_2688_, 1);
lean_inc_ref(v_b_2705_);
v_eq_2706_ = lean_ctor_get(v_s_2688_, 3);
lean_inc_ref(v_eq_2706_);
lean_dec_ref_known(v_s_2688_, 5);
v___x_2707_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2704_, v_b_2705_, v_eq_2706_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec(v_a_2709_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_obj_tag_nat(v_x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2723_);
lean_dec(v_x_2723_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2725_, lean_object* v_k_2726_){
_start:
{
if (lean_obj_tag(v_t_2725_) == 0)
{
return v_k_2726_;
}
else
{
lean_object* v_c_2727_; lean_object* v_numCases_2728_; uint8_t v_isRec_2729_; uint8_t v_tryPostpone_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_c_2727_ = lean_ctor_get(v_t_2725_, 0);
lean_inc_ref(v_c_2727_);
v_numCases_2728_ = lean_ctor_get(v_t_2725_, 1);
lean_inc(v_numCases_2728_);
v_isRec_2729_ = lean_ctor_get_uint8(v_t_2725_, sizeof(void*)*2);
v_tryPostpone_2730_ = lean_ctor_get_uint8(v_t_2725_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2725_, 2);
v___x_2731_ = lean_box(v_isRec_2729_);
v___x_2732_ = lean_box(v_tryPostpone_2730_);
v___x_2733_ = lean_apply_4(v_k_2726_, v_c_2727_, v_numCases_2728_, v___x_2731_, v___x_2732_);
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2734_, lean_object* v_ctorIdx_2735_, lean_object* v_t_2736_, lean_object* v_h_2737_, lean_object* v_k_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2736_, v_k_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2740_, lean_object* v_ctorIdx_2741_, lean_object* v_t_2742_, lean_object* v_h_2743_, lean_object* v_k_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2740_, v_ctorIdx_2741_, v_t_2742_, v_h_2743_, v_k_2744_);
lean_dec(v_ctorIdx_2741_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2746_, lean_object* v_none_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2746_, v_none_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2749_, lean_object* v_t_2750_, lean_object* v_h_2751_, lean_object* v_none_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2750_, v_none_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2754_, lean_object* v_some_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2754_, v_some_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2757_, lean_object* v_t_2758_, lean_object* v_h_2759_, lean_object* v_some_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2758_, v_some_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2762_, lean_object* v_as_2763_, size_t v_i_2764_, size_t v_stop_2765_){
_start:
{
uint8_t v___x_2766_; 
v___x_2766_ = lean_usize_dec_eq(v_i_2764_, v_stop_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_array_uget_borrowed(v_as_2763_, v_i_2764_);
v___x_2768_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2767_, v_a_2762_);
if (v___x_2768_ == 0)
{
size_t v___x_2769_; size_t v___x_2770_; 
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2764_, v___x_2769_);
v_i_2764_ = v___x_2770_;
goto _start;
}
else
{
return v___x_2768_;
}
}
else
{
uint8_t v___x_2772_; 
v___x_2772_ = 0;
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2773_, lean_object* v_as_2774_, lean_object* v_i_2775_, lean_object* v_stop_2776_){
_start:
{
uint64_t v_a_2507__boxed_2777_; size_t v_i_boxed_2778_; size_t v_stop_boxed_2779_; uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_a_2507__boxed_2777_ = lean_unbox_uint64(v_a_2773_);
lean_dec_ref(v_a_2773_);
v_i_boxed_2778_ = lean_unbox_usize(v_i_2775_);
lean_dec(v_i_2775_);
v_stop_boxed_2779_ = lean_unbox_usize(v_stop_2776_);
lean_dec(v_stop_2776_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2777_, v_as_2774_, v_i_boxed_2778_, v_stop_boxed_2779_);
lean_dec_ref(v_as_2774_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2784_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2837_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2837_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2837_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
if (lean_obj_tag(v_a_2794_) == 1)
{
lean_object* v_val_2798_; lean_object* v___x_2799_; 
lean_del_object(v___x_2796_);
v_val_2798_ = lean_ctor_get(v_a_2794_, 0);
lean_inc(v_val_2798_);
lean_dec_ref_known(v_a_2794_, 1);
v___x_2799_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2823_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2823_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2823_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_array_get_size(v_val_2798_);
v___x_2806_ = lean_nat_dec_lt(v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
lean_dec(v_a_2800_);
lean_dec(v_val_2798_);
v___x_2807_ = lean_box(v___x_2806_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2807_);
v___x_2809_ = v___x_2802_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
if (v___x_2806_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec(v_a_2800_);
lean_dec(v_val_2798_);
v___x_2811_ = lean_box(v___x_2806_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2811_);
v___x_2813_ = v___x_2802_;
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
else
{
size_t v___x_2815_; size_t v___x_2816_; uint64_t v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2815_ = ((size_t)0ULL);
v___x_2816_ = lean_usize_of_nat(v___x_2805_);
v___x_2817_ = lean_unbox_uint64(v_a_2800_);
lean_dec(v_a_2800_);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2817_, v_val_2798_, v___x_2815_, v___x_2816_);
lean_dec(v_val_2798_);
v___x_2819_ = lean_box(v___x_2818_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2819_);
v___x_2821_ = v___x_2802_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
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
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_val_2798_);
v_a_2824_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2799_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2799_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
lean_dec(v_a_2794_);
v___x_2832_ = 1;
v___x_2833_ = lean_box(v___x_2832_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2833_);
v___x_2835_ = v___x_2796_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_a_2838_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2793_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2793_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_c_2846_);
return v_res_2857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2860_ = l_Lean_stringToMessageData(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2861_, lean_object* v_c_x3f_2862_, lean_object* v_cs_x27_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
if (lean_obj_tag(v_cs_2861_) == 0)
{
lean_object* v___x_2875_; lean_object* v_toGoalState_2876_; lean_object* v_split_2877_; lean_object* v_mvarId_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2988_; 
v___x_2875_ = lean_st_ref_take(v_a_2864_);
v_toGoalState_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc_ref(v_toGoalState_2876_);
v_split_2877_ = lean_ctor_get(v_toGoalState_2876_, 15);
lean_inc_ref(v_split_2877_);
v_mvarId_2878_ = lean_ctor_get(v___x_2875_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2875_, 0);
lean_dec(v_unused_2989_);
v___x_2880_ = v___x_2875_;
v_isShared_2881_ = v_isSharedCheck_2988_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_mvarId_2878_);
lean_dec(v___x_2875_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2988_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_nextDeclIdx_2882_; lean_object* v_enodeMap_2883_; lean_object* v_exprs_2884_; lean_object* v_parents_2885_; lean_object* v_congrTable_2886_; lean_object* v_appMap_2887_; lean_object* v_indicesFound_2888_; lean_object* v_toProcess_2889_; lean_object* v_internalizing_2890_; uint8_t v_inconsistent_2891_; lean_object* v_nextIdx_2892_; lean_object* v_newRawFacts_2893_; lean_object* v_facts_2894_; lean_object* v_extThms_2895_; lean_object* v_ematch_2896_; lean_object* v_inj_2897_; lean_object* v_clean_2898_; lean_object* v_sstates_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2986_; 
v_nextDeclIdx_2882_ = lean_ctor_get(v_toGoalState_2876_, 0);
v_enodeMap_2883_ = lean_ctor_get(v_toGoalState_2876_, 1);
v_exprs_2884_ = lean_ctor_get(v_toGoalState_2876_, 2);
v_parents_2885_ = lean_ctor_get(v_toGoalState_2876_, 3);
v_congrTable_2886_ = lean_ctor_get(v_toGoalState_2876_, 4);
v_appMap_2887_ = lean_ctor_get(v_toGoalState_2876_, 5);
v_indicesFound_2888_ = lean_ctor_get(v_toGoalState_2876_, 6);
v_toProcess_2889_ = lean_ctor_get(v_toGoalState_2876_, 7);
v_internalizing_2890_ = lean_ctor_get(v_toGoalState_2876_, 8);
v_inconsistent_2891_ = lean_ctor_get_uint8(v_toGoalState_2876_, sizeof(void*)*18);
v_nextIdx_2892_ = lean_ctor_get(v_toGoalState_2876_, 9);
v_newRawFacts_2893_ = lean_ctor_get(v_toGoalState_2876_, 10);
v_facts_2894_ = lean_ctor_get(v_toGoalState_2876_, 11);
v_extThms_2895_ = lean_ctor_get(v_toGoalState_2876_, 12);
v_ematch_2896_ = lean_ctor_get(v_toGoalState_2876_, 13);
v_inj_2897_ = lean_ctor_get(v_toGoalState_2876_, 14);
v_clean_2898_ = lean_ctor_get(v_toGoalState_2876_, 16);
v_sstates_2899_ = lean_ctor_get(v_toGoalState_2876_, 17);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_toGoalState_2876_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_toGoalState_2876_, 15);
lean_dec(v_unused_2987_);
v___x_2901_ = v_toGoalState_2876_;
v_isShared_2902_ = v_isSharedCheck_2986_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_sstates_2899_);
lean_inc(v_clean_2898_);
lean_inc(v_inj_2897_);
lean_inc(v_ematch_2896_);
lean_inc(v_extThms_2895_);
lean_inc(v_facts_2894_);
lean_inc(v_newRawFacts_2893_);
lean_inc(v_nextIdx_2892_);
lean_inc(v_internalizing_2890_);
lean_inc(v_toProcess_2889_);
lean_inc(v_indicesFound_2888_);
lean_inc(v_appMap_2887_);
lean_inc(v_congrTable_2886_);
lean_inc(v_parents_2885_);
lean_inc(v_exprs_2884_);
lean_inc(v_enodeMap_2883_);
lean_inc(v_nextDeclIdx_2882_);
lean_dec(v_toGoalState_2876_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2986_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v_num_2903_; lean_object* v_added_2904_; lean_object* v_resolved_2905_; lean_object* v_trace_2906_; lean_object* v_lookaheads_2907_; lean_object* v_argPosMap_2908_; lean_object* v_argsAt_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2984_; 
v_num_2903_ = lean_ctor_get(v_split_2877_, 0);
v_added_2904_ = lean_ctor_get(v_split_2877_, 2);
v_resolved_2905_ = lean_ctor_get(v_split_2877_, 3);
v_trace_2906_ = lean_ctor_get(v_split_2877_, 4);
v_lookaheads_2907_ = lean_ctor_get(v_split_2877_, 5);
v_argPosMap_2908_ = lean_ctor_get(v_split_2877_, 6);
v_argsAt_2909_ = lean_ctor_get(v_split_2877_, 7);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_split_2877_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_split_2877_, 1);
lean_dec(v_unused_2985_);
v___x_2911_ = v_split_2877_;
v_isShared_2912_ = v_isSharedCheck_2984_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_argsAt_2909_);
lean_inc(v_argPosMap_2908_);
lean_inc(v_lookaheads_2907_);
lean_inc(v_trace_2906_);
lean_inc(v_resolved_2905_);
lean_inc(v_added_2904_);
lean_inc(v_num_2903_);
lean_dec(v_split_2877_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2984_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2913_ = l_List_reverse___redArg(v_cs_x27_2863_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2913_);
v___x_2915_ = v___x_2911_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_num_2903_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_added_2904_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_resolved_2905_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v_trace_2906_);
lean_ctor_set(v_reuseFailAlloc_2983_, 5, v_lookaheads_2907_);
lean_ctor_set(v_reuseFailAlloc_2983_, 6, v_argPosMap_2908_);
lean_ctor_set(v_reuseFailAlloc_2983_, 7, v_argsAt_2909_);
v___x_2915_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2917_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 15, v___x_2915_);
v___x_2917_ = v___x_2901_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_nextDeclIdx_2882_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_enodeMap_2883_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_exprs_2884_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_parents_2885_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_congrTable_2886_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_appMap_2887_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_indicesFound_2888_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_toProcess_2889_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_internalizing_2890_);
lean_ctor_set(v_reuseFailAlloc_2982_, 9, v_nextIdx_2892_);
lean_ctor_set(v_reuseFailAlloc_2982_, 10, v_newRawFacts_2893_);
lean_ctor_set(v_reuseFailAlloc_2982_, 11, v_facts_2894_);
lean_ctor_set(v_reuseFailAlloc_2982_, 12, v_extThms_2895_);
lean_ctor_set(v_reuseFailAlloc_2982_, 13, v_ematch_2896_);
lean_ctor_set(v_reuseFailAlloc_2982_, 14, v_inj_2897_);
lean_ctor_set(v_reuseFailAlloc_2982_, 15, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2982_, 16, v_clean_2898_);
lean_ctor_set(v_reuseFailAlloc_2982_, 17, v_sstates_2899_);
lean_ctor_set_uint8(v_reuseFailAlloc_2982_, sizeof(void*)*18, v_inconsistent_2891_);
v___x_2917_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2917_);
v___x_2919_ = v___x_2880_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_mvarId_2878_);
v___x_2919_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_st_ref_put(v_a_2864_, v___x_2919_);
if (lean_obj_tag(v_c_x3f_2862_) == 1)
{
lean_object* v___x_2921_; lean_object* v_toGoalState_2922_; lean_object* v_ematch_2923_; lean_object* v_mvarId_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2978_; 
v___x_2921_ = lean_st_ref_take(v_a_2864_);
v_toGoalState_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_ref(v_toGoalState_2922_);
v_ematch_2923_ = lean_ctor_get(v_toGoalState_2922_, 13);
lean_inc_ref(v_ematch_2923_);
v_mvarId_2924_ = lean_ctor_get(v___x_2921_, 1);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v___x_2921_, 0);
lean_dec(v_unused_2979_);
v___x_2926_ = v___x_2921_;
v_isShared_2927_ = v_isSharedCheck_2978_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_mvarId_2924_);
lean_dec(v___x_2921_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2978_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v_nextDeclIdx_2928_; lean_object* v_enodeMap_2929_; lean_object* v_exprs_2930_; lean_object* v_parents_2931_; lean_object* v_congrTable_2932_; lean_object* v_appMap_2933_; lean_object* v_indicesFound_2934_; lean_object* v_toProcess_2935_; lean_object* v_internalizing_2936_; uint8_t v_inconsistent_2937_; lean_object* v_nextIdx_2938_; lean_object* v_newRawFacts_2939_; lean_object* v_facts_2940_; lean_object* v_extThms_2941_; lean_object* v_inj_2942_; lean_object* v_split_2943_; lean_object* v_clean_2944_; lean_object* v_sstates_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2976_; 
v_nextDeclIdx_2928_ = lean_ctor_get(v_toGoalState_2922_, 0);
v_enodeMap_2929_ = lean_ctor_get(v_toGoalState_2922_, 1);
v_exprs_2930_ = lean_ctor_get(v_toGoalState_2922_, 2);
v_parents_2931_ = lean_ctor_get(v_toGoalState_2922_, 3);
v_congrTable_2932_ = lean_ctor_get(v_toGoalState_2922_, 4);
v_appMap_2933_ = lean_ctor_get(v_toGoalState_2922_, 5);
v_indicesFound_2934_ = lean_ctor_get(v_toGoalState_2922_, 6);
v_toProcess_2935_ = lean_ctor_get(v_toGoalState_2922_, 7);
v_internalizing_2936_ = lean_ctor_get(v_toGoalState_2922_, 8);
v_inconsistent_2937_ = lean_ctor_get_uint8(v_toGoalState_2922_, sizeof(void*)*18);
v_nextIdx_2938_ = lean_ctor_get(v_toGoalState_2922_, 9);
v_newRawFacts_2939_ = lean_ctor_get(v_toGoalState_2922_, 10);
v_facts_2940_ = lean_ctor_get(v_toGoalState_2922_, 11);
v_extThms_2941_ = lean_ctor_get(v_toGoalState_2922_, 12);
v_inj_2942_ = lean_ctor_get(v_toGoalState_2922_, 14);
v_split_2943_ = lean_ctor_get(v_toGoalState_2922_, 15);
v_clean_2944_ = lean_ctor_get(v_toGoalState_2922_, 16);
v_sstates_2945_ = lean_ctor_get(v_toGoalState_2922_, 17);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_toGoalState_2922_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_toGoalState_2922_, 13);
lean_dec(v_unused_2977_);
v___x_2947_ = v_toGoalState_2922_;
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_sstates_2945_);
lean_inc(v_clean_2944_);
lean_inc(v_split_2943_);
lean_inc(v_inj_2942_);
lean_inc(v_extThms_2941_);
lean_inc(v_facts_2940_);
lean_inc(v_newRawFacts_2939_);
lean_inc(v_nextIdx_2938_);
lean_inc(v_internalizing_2936_);
lean_inc(v_toProcess_2935_);
lean_inc(v_indicesFound_2934_);
lean_inc(v_appMap_2933_);
lean_inc(v_congrTable_2932_);
lean_inc(v_parents_2931_);
lean_inc(v_exprs_2930_);
lean_inc(v_enodeMap_2929_);
lean_inc(v_nextDeclIdx_2928_);
lean_dec(v_toGoalState_2922_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_thmMap_2949_; lean_object* v_gmt_2950_; lean_object* v_thms_2951_; lean_object* v_newThms_2952_; lean_object* v_numInstances_2953_; lean_object* v_numDelayedInstances_2954_; lean_object* v_preInstances_2955_; lean_object* v_nextThmIdx_2956_; lean_object* v_matchEqNames_2957_; lean_object* v_delayedThmInsts_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2974_; 
v_thmMap_2949_ = lean_ctor_get(v_ematch_2923_, 0);
v_gmt_2950_ = lean_ctor_get(v_ematch_2923_, 1);
v_thms_2951_ = lean_ctor_get(v_ematch_2923_, 2);
v_newThms_2952_ = lean_ctor_get(v_ematch_2923_, 3);
v_numInstances_2953_ = lean_ctor_get(v_ematch_2923_, 4);
v_numDelayedInstances_2954_ = lean_ctor_get(v_ematch_2923_, 5);
v_preInstances_2955_ = lean_ctor_get(v_ematch_2923_, 7);
v_nextThmIdx_2956_ = lean_ctor_get(v_ematch_2923_, 8);
v_matchEqNames_2957_ = lean_ctor_get(v_ematch_2923_, 9);
v_delayedThmInsts_2958_ = lean_ctor_get(v_ematch_2923_, 10);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_ematch_2923_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v_ematch_2923_, 6);
lean_dec(v_unused_2975_);
v___x_2960_ = v_ematch_2923_;
v_isShared_2961_ = v_isSharedCheck_2974_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_delayedThmInsts_2958_);
lean_inc(v_matchEqNames_2957_);
lean_inc(v_nextThmIdx_2956_);
lean_inc(v_preInstances_2955_);
lean_inc(v_numDelayedInstances_2954_);
lean_inc(v_numInstances_2953_);
lean_inc(v_newThms_2952_);
lean_inc(v_thms_2951_);
lean_inc(v_gmt_2950_);
lean_inc(v_thmMap_2949_);
lean_dec(v_ematch_2923_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2974_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = lean_unsigned_to_nat(0u);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 6, v___x_2962_);
v___x_2964_ = v___x_2960_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_thmMap_2949_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_gmt_2950_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_thms_2951_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_newThms_2952_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v_numInstances_2953_);
lean_ctor_set(v_reuseFailAlloc_2973_, 5, v_numDelayedInstances_2954_);
lean_ctor_set(v_reuseFailAlloc_2973_, 6, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2973_, 7, v_preInstances_2955_);
lean_ctor_set(v_reuseFailAlloc_2973_, 8, v_nextThmIdx_2956_);
lean_ctor_set(v_reuseFailAlloc_2973_, 9, v_matchEqNames_2957_);
lean_ctor_set(v_reuseFailAlloc_2973_, 10, v_delayedThmInsts_2958_);
v___x_2964_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 13, v___x_2964_);
v___x_2966_ = v___x_2947_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_nextDeclIdx_2928_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_enodeMap_2929_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_exprs_2930_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v_parents_2931_);
lean_ctor_set(v_reuseFailAlloc_2972_, 4, v_congrTable_2932_);
lean_ctor_set(v_reuseFailAlloc_2972_, 5, v_appMap_2933_);
lean_ctor_set(v_reuseFailAlloc_2972_, 6, v_indicesFound_2934_);
lean_ctor_set(v_reuseFailAlloc_2972_, 7, v_toProcess_2935_);
lean_ctor_set(v_reuseFailAlloc_2972_, 8, v_internalizing_2936_);
lean_ctor_set(v_reuseFailAlloc_2972_, 9, v_nextIdx_2938_);
lean_ctor_set(v_reuseFailAlloc_2972_, 10, v_newRawFacts_2939_);
lean_ctor_set(v_reuseFailAlloc_2972_, 11, v_facts_2940_);
lean_ctor_set(v_reuseFailAlloc_2972_, 12, v_extThms_2941_);
lean_ctor_set(v_reuseFailAlloc_2972_, 13, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2972_, 14, v_inj_2942_);
lean_ctor_set(v_reuseFailAlloc_2972_, 15, v_split_2943_);
lean_ctor_set(v_reuseFailAlloc_2972_, 16, v_clean_2944_);
lean_ctor_set(v_reuseFailAlloc_2972_, 17, v_sstates_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_2972_, sizeof(void*)*18, v_inconsistent_2937_);
v___x_2966_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2966_);
v___x_2968_ = v___x_2926_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_mvarId_2924_);
v___x_2968_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_st_ref_put(v_a_2864_, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_c_x3f_2862_);
return v___x_2970_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_c_x3f_2862_);
return v___x_2980_;
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
lean_object* v_head_2990_; lean_object* v_tail_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3211_; 
v_head_2990_ = lean_ctor_get(v_cs_2861_, 0);
v_tail_2991_ = lean_ctor_get(v_cs_2861_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_cs_2861_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_2993_ = v_cs_2861_;
v_isShared_2994_ = v_isSharedCheck_3211_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_tail_2991_);
lean_inc(v_head_2990_);
lean_dec(v_cs_2861_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3211_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; uint8_t v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; uint8_t v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; uint8_t v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___x_3103_; 
v___x_3103_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2990_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; uint8_t v___x_3105_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3105_ == 0)
{
lean_del_object(v___x_2993_);
lean_dec(v_head_2990_);
v_cs_2861_ = v_tail_2991_;
goto _start;
}
else
{
lean_object* v_toCold_3107_; lean_object* v_options_3108_; lean_object* v_inheritedTraceOptions_3109_; uint8_t v_hasTrace_3110_; uint8_t v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; 
v_toCold_3107_ = lean_ctor_get(v_a_2872_, 0);
v_options_3108_ = lean_ctor_get(v_toCold_3107_, 2);
v_inheritedTraceOptions_3109_ = lean_ctor_get(v_toCold_3107_, 11);
v_hasTrace_3110_ = lean_ctor_get_uint8(v_options_3108_, sizeof(void*)*1);
v___x_3111_ = 0;
if (v_hasTrace_3110_ == 0)
{
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
v___y_3144_ = v_a_2871_;
v___y_3145_ = v_a_2872_;
v___y_3146_ = v_a_2873_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3109_, v_options_3108_, v___x_3179_);
if (v___x_3180_ == 0)
{
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
v___y_3144_ = v_a_2871_;
v___y_3145_ = v_a_2872_;
v___y_3146_ = v_a_2873_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Meta_Grind_updateLastTag(v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec_ref_known(v___x_3181_, 1);
v___x_3182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3183_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2990_);
v___x_3184_ = l_Lean_MessageData_ofExpr(v___x_3183_);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3178_, v___x_3185_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
v___y_3144_ = v_a_2871_;
v___y_3145_ = v_a_2872_;
v___y_3146_ = v_a_2873_;
goto v___jp_3136_;
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3195_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3181_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3181_);
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
}
}
v___jp_3112_:
{
if (lean_obj_tag(v_c_x3f_2862_) == 0)
{
lean_object* v___x_3127_; 
lean_del_object(v___x_2993_);
v___x_3127_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3127_, 0, v_head_2990_);
lean_ctor_set(v___x_3127_, 1, v___y_3121_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*2, v___y_3116_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*2 + 1, v___y_3123_);
v_cs_2861_ = v_tail_2991_;
v_c_x3f_2862_ = v___x_3127_;
v_a_2864_ = v___y_3120_;
v_a_2865_ = v___y_3125_;
v_a_2866_ = v___y_3115_;
v_a_2867_ = v___y_3113_;
v_a_2868_ = v___y_3119_;
v_a_2869_ = v___y_3124_;
v_a_2870_ = v___y_3122_;
v_a_2871_ = v___y_3117_;
v_a_2872_ = v___y_3114_;
v_a_2873_ = v___y_3118_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3129_; 
v_tryPostpone_3129_ = lean_ctor_get_uint8(v_c_x3f_2862_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3129_ == 0)
{
if (v___y_3123_ == 0)
{
lean_object* v_c_3130_; lean_object* v_numCases_3131_; 
v_c_3130_ = lean_ctor_get(v_c_x3f_2862_, 0);
v_numCases_3131_ = lean_ctor_get(v_c_x3f_2862_, 1);
lean_inc(v_numCases_3131_);
lean_inc_ref(v_c_3130_);
v___y_3085_ = v___y_3113_;
v___y_3086_ = v_c_3130_;
v___y_3087_ = v___y_3114_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v_numCases_3131_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___x_3111_;
goto v___jp_3084_;
}
else
{
lean_dec(v___y_3121_);
v___y_2996_ = v___y_3113_;
v___y_2997_ = v___y_3122_;
v___y_2998_ = v___y_3114_;
v___y_2999_ = v___y_3115_;
v___y_3000_ = v___y_3117_;
v___y_3001_ = v___y_3118_;
v___y_3002_ = v___y_3124_;
v___y_3003_ = v___y_3119_;
v___y_3004_ = v___y_3120_;
v___y_3005_ = v___y_3125_;
goto v___jp_2995_;
}
}
else
{
if (v___y_3123_ == 0)
{
lean_object* v_c_3132_; 
lean_del_object(v___x_2993_);
v_c_3132_ = lean_ctor_get(v_c_x3f_2862_, 0);
lean_inc_ref(v_c_3132_);
lean_dec_ref_known(v_c_x3f_2862_, 2);
v___y_3011_ = v___y_3113_;
v___y_3012_ = v_c_3132_;
v___y_3013_ = v___y_3114_;
v___y_3014_ = v___y_3115_;
v___y_3015_ = v___y_3116_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3124_;
v___y_3024_ = v___y_3125_;
goto v___jp_3010_;
}
else
{
if (v___y_3126_ == 0)
{
lean_object* v_c_3133_; lean_object* v_numCases_3134_; 
v_c_3133_ = lean_ctor_get(v_c_x3f_2862_, 0);
v_numCases_3134_ = lean_ctor_get(v_c_x3f_2862_, 1);
lean_inc(v_numCases_3134_);
lean_inc_ref(v_c_3133_);
v___y_3085_ = v___y_3113_;
v___y_3086_ = v_c_3133_;
v___y_3087_ = v___y_3114_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v_numCases_3134_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3123_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
goto v___jp_3084_;
}
else
{
lean_object* v_c_3135_; 
lean_del_object(v___x_2993_);
v_c_3135_ = lean_ctor_get(v_c_x3f_2862_, 0);
lean_inc_ref(v_c_3135_);
lean_dec_ref_known(v_c_x3f_2862_, 2);
v___y_3011_ = v___y_3113_;
v___y_3012_ = v_c_3135_;
v___y_3013_ = v___y_3114_;
v___y_3014_ = v___y_3115_;
v___y_3015_ = v___y_3116_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3124_;
v___y_3024_ = v___y_3125_;
goto v___jp_3010_;
}
}
}
}
}
v___jp_3136_:
{
lean_object* v___x_3147_; 
lean_inc(v_head_2990_);
v___x_3147_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2990_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
switch(lean_obj_tag(v_a_3148_))
{
case 0:
{
lean_del_object(v___x_2993_);
lean_dec(v_head_2990_);
v_cs_2861_ = v_tail_2991_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
v_a_2871_ = v___y_3144_;
v_a_2872_ = v___y_3145_;
v_a_2873_ = v___y_3146_;
goto _start;
}
case 1:
{
lean_object* v___x_3150_; 
lean_del_object(v___x_2993_);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_head_2990_);
lean_ctor_set(v___x_3150_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2991_;
v_cs_x27_2863_ = v___x_3150_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
v_a_2871_ = v___y_3144_;
v_a_2872_ = v___y_3145_;
v_a_2873_ = v___y_3146_;
goto _start;
}
default: 
{
lean_object* v_numCases_3152_; uint8_t v_isRec_3153_; uint8_t v_tryPostpone_3154_; lean_object* v___x_3155_; 
v_numCases_3152_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_numCases_3152_);
v_isRec_3153_ = lean_ctor_get_uint8(v_a_3148_, sizeof(void*)*1);
v_tryPostpone_3154_ = lean_ctor_get_uint8(v_a_3148_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3148_, 1);
v___x_3155_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3139_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; uint8_t v___x_3157_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = lean_unbox(v_a_3156_);
lean_dec(v_a_3156_);
if (v___x_3157_ == 0)
{
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3145_;
v___y_3115_ = v___y_3139_;
v___y_3116_ = v_isRec_3153_;
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3146_;
v___y_3119_ = v___y_3141_;
v___y_3120_ = v___y_3137_;
v___y_3121_ = v_numCases_3152_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v_tryPostpone_3154_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3138_;
v___y_3126_ = v___x_3111_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_dec_lt(v___x_3158_, v_numCases_3152_);
if (v___x_3159_ == 0)
{
v___y_3113_ = v___y_3140_;
v___y_3114_ = v___y_3145_;
v___y_3115_ = v___y_3139_;
v___y_3116_ = v_isRec_3153_;
v___y_3117_ = v___y_3144_;
v___y_3118_ = v___y_3146_;
v___y_3119_ = v___y_3141_;
v___y_3120_ = v___y_3137_;
v___y_3121_ = v_numCases_3152_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v_tryPostpone_3154_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3138_;
v___y_3126_ = v___x_3159_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3160_; 
lean_dec(v_numCases_3152_);
lean_del_object(v___x_2993_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_head_2990_);
lean_ctor_set(v___x_3160_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2991_;
v_cs_x27_2863_ = v___x_3160_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
v_a_2871_ = v___y_3144_;
v_a_2872_ = v___y_3145_;
v_a_2873_ = v___y_3146_;
goto _start;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_numCases_3152_);
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3162_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3155_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3155_);
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
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3170_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3147_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3147_);
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
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3203_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3103_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3103_);
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
v___jp_2995_:
{
lean_object* v___x_3007_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_cs_x27_2863_);
v___x_3007_ = v___x_2993_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_head_2990_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_cs_x27_2863_);
v___x_3007_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
v_cs_2861_ = v_tail_2991_;
v_cs_x27_2863_ = v___x_3007_;
v_a_2864_ = v___y_3004_;
v_a_2865_ = v___y_3005_;
v_a_2866_ = v___y_2999_;
v_a_2867_ = v___y_2996_;
v_a_2868_ = v___y_3003_;
v_a_2869_ = v___y_3002_;
v_a_2870_ = v___y_2997_;
v_a_2871_ = v___y_3000_;
v_a_2872_ = v___y_2998_;
v_a_2873_ = v___y_3001_;
goto _start;
}
}
v___jp_3010_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3025_, 0, v_head_2990_);
lean_ctor_set(v___x_3025_, 1, v___y_3020_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*2, v___y_3015_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*2 + 1, v___y_3022_);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___y_3012_);
lean_ctor_set(v___x_3026_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2991_;
v_c_x3f_2862_ = v___x_3025_;
v_cs_x27_2863_ = v___x_3026_;
v_a_2864_ = v___y_3019_;
v_a_2865_ = v___y_3024_;
v_a_2866_ = v___y_3014_;
v_a_2867_ = v___y_3011_;
v_a_2868_ = v___y_3018_;
v_a_2869_ = v___y_3023_;
v_a_2870_ = v___y_3021_;
v_a_2871_ = v___y_3016_;
v_a_2872_ = v___y_3013_;
v_a_2873_ = v___y_3017_;
goto _start;
}
v___jp_3028_:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2990_, v___y_3038_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3030_, v___y_3038_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; uint8_t v___x_3048_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3048_ = lean_nat_dec_lt(v_a_3045_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec(v_a_3045_);
if (v___x_3048_ == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_nat_dec_lt(v___y_3039_, v___y_3037_);
lean_dec(v___y_3037_);
if (v___x_3049_ == 0)
{
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3030_);
v___y_2996_ = v___y_3029_;
v___y_2997_ = v___y_3040_;
v___y_2998_ = v___y_3031_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3034_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___y_3042_;
v___y_3003_ = v___y_3036_;
v___y_3004_ = v___y_3038_;
v___y_3005_ = v___y_3043_;
goto v___jp_2995_;
}
else
{
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2862_);
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3041_;
v___y_3023_ = v___y_3042_;
v___y_3024_ = v___y_3043_;
goto v___jp_3010_;
}
}
else
{
lean_dec(v___y_3037_);
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2862_);
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3035_;
v___y_3018_ = v___y_3036_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3041_;
v___y_3023_ = v___y_3042_;
v___y_3024_ = v___y_3043_;
goto v___jp_3010_;
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_3045_);
lean_dec(v___y_3039_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3030_);
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3050_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3046_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3046_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v___y_3039_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3030_);
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3058_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3044_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3044_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
v___jp_3066_:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(1u);
v___x_3083_ = lean_nat_dec_lt(v___x_3082_, v___y_3075_);
if (v___x_3083_ == 0)
{
v___y_3029_ = v___y_3067_;
v___y_3030_ = v___y_3068_;
v___y_3031_ = v___y_3069_;
v___y_3032_ = v___y_3070_;
v___y_3033_ = v___y_3071_;
v___y_3034_ = v___y_3072_;
v___y_3035_ = v___y_3073_;
v___y_3036_ = v___y_3074_;
v___y_3037_ = v___y_3075_;
v___y_3038_ = v___y_3076_;
v___y_3039_ = v___y_3077_;
v___y_3040_ = v___y_3078_;
v___y_3041_ = v___y_3080_;
v___y_3042_ = v___y_3079_;
v___y_3043_ = v___y_3081_;
goto v___jp_3028_;
}
else
{
lean_dec(v___y_3075_);
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2862_);
v___y_3011_ = v___y_3067_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3069_;
v___y_3014_ = v___y_3070_;
v___y_3015_ = v___y_3071_;
v___y_3016_ = v___y_3072_;
v___y_3017_ = v___y_3073_;
v___y_3018_ = v___y_3074_;
v___y_3019_ = v___y_3076_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3078_;
v___y_3022_ = v___y_3080_;
v___y_3023_ = v___y_3079_;
v___y_3024_ = v___y_3081_;
goto v___jp_3010_;
}
}
v___jp_3084_:
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_dec_eq(v___y_3095_, v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3029_ = v___y_3085_;
v___y_3030_ = v___y_3086_;
v___y_3031_ = v___y_3087_;
v___y_3032_ = v___y_3088_;
v___y_3033_ = v___y_3089_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3092_;
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3098_;
v___y_3042_ = v___y_3097_;
v___y_3043_ = v___y_3099_;
goto v___jp_3028_;
}
else
{
if (v___y_3089_ == 0)
{
v___y_3067_ = v___y_3085_;
v___y_3068_ = v___y_3086_;
v___y_3069_ = v___y_3087_;
v___y_3070_ = v___y_3088_;
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
goto v___jp_3066_;
}
else
{
if (v___y_3100_ == 0)
{
v___y_3029_ = v___y_3085_;
v___y_3030_ = v___y_3086_;
v___y_3031_ = v___y_3087_;
v___y_3032_ = v___y_3088_;
v___y_3033_ = v___y_3089_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3092_;
v___y_3037_ = v___y_3093_;
v___y_3038_ = v___y_3094_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3098_;
v___y_3042_ = v___y_3097_;
v___y_3043_ = v___y_3099_;
goto v___jp_3028_;
}
else
{
v___y_3067_ = v___y_3085_;
v___y_3068_ = v___y_3086_;
v___y_3069_ = v___y_3087_;
v___y_3070_ = v___y_3088_;
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
goto v___jp_3066_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3212_, lean_object* v_c_x3f_3213_, lean_object* v_cs_x27_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3212_, v_c_x3f_3213_, v_cs_x27_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec(v_a_3215_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3227_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3274_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_unbox(v_a_3239_);
lean_dec(v_a_3239_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_del_object(v___x_3241_);
v___x_3244_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3227_, v_a_3229_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3261_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3261_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3261_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_unbox(v_a_3245_);
lean_dec(v_a_3245_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v_toGoalState_3251_; lean_object* v_split_3252_; lean_object* v_candidates_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_del_object(v___x_3247_);
v___x_3250_ = lean_st_ref_get(v_a_3227_);
v_toGoalState_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc_ref(v_toGoalState_3251_);
lean_dec(v___x_3250_);
v_split_3252_ = lean_ctor_get(v_toGoalState_3251_, 15);
lean_inc_ref(v_split_3252_);
lean_dec_ref(v_toGoalState_3251_);
v_candidates_3253_ = lean_ctor_get(v_split_3252_, 1);
lean_inc(v_candidates_3253_);
lean_dec_ref(v_split_3252_);
v___x_3254_ = lean_box(0);
v___x_3255_ = lean_box(0);
v___x_3256_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3253_, v___x_3254_, v___x_3255_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3257_ = lean_box(0);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3257_);
v___x_3259_ = v___x_3247_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
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
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
v_a_3262_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3244_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3244_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_box(0);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3270_);
v___x_3272_ = v___x_3241_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
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
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
v_a_3275_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3238_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3238_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
return v_res_3294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_box(0);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3304_ = l_Lean_mkConst(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3305_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3307_ = l_Lean_Expr_app___override(v___x_3306_, v_c_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3318_ = l_Lean_mkConst(v___x_3317_, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3326_ = l_Lean_mkConst(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = lean_box(0);
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3334_ = l_Lean_mkConst(v___x_3333_, v___x_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___x_3407_; 
lean_inc_ref(v_c_3335_);
v___x_3407_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3335_, v_a_3343_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3480_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3480_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3480_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = l_Lean_Expr_cleanupAnnotations(v_a_3408_);
v___x_3413_ = l_Lean_Expr_isApp(v___x_3412_);
if (v___x_3413_ == 0)
{
lean_dec_ref(v___x_3412_);
lean_del_object(v___x_3410_);
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
v___y_3403_ = v_a_3344_;
v___y_3404_ = v_a_3345_;
goto v___jp_3394_;
}
else
{
lean_object* v_arg_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_arg_3414_ = lean_ctor_get(v___x_3412_, 1);
lean_inc_ref(v_arg_3414_);
v___x_3415_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3412_);
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3417_ = l_Lean_Expr_isConstOf(v___x_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
uint8_t v___x_3418_; 
v___x_3418_ = l_Lean_Expr_isApp(v___x_3415_);
if (v___x_3418_ == 0)
{
lean_dec_ref(v___x_3415_);
lean_dec_ref(v_arg_3414_);
lean_del_object(v___x_3410_);
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
v___y_3403_ = v_a_3344_;
v___y_3404_ = v_a_3345_;
goto v___jp_3394_;
}
else
{
lean_object* v_arg_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v_arg_3419_ = lean_ctor_get(v___x_3415_, 1);
lean_inc_ref(v_arg_3419_);
v___x_3420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3415_);
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3422_ = l_Lean_Expr_isConstOf(v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
uint8_t v___x_3423_; 
v___x_3423_ = l_Lean_Expr_isApp(v___x_3420_);
if (v___x_3423_ == 0)
{
lean_dec_ref(v___x_3420_);
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
lean_del_object(v___x_3410_);
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
v___y_3403_ = v_a_3344_;
v___y_3404_ = v_a_3345_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3424_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3420_);
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3426_ = l_Lean_Expr_isConstOf(v___x_3424_, v___x_3425_);
lean_dec_ref(v___x_3424_);
if (v___x_3426_ == 0)
{
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
lean_del_object(v___x_3410_);
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
v___y_3403_ = v_a_3344_;
v___y_3404_ = v_a_3345_;
goto v___jp_3394_;
}
else
{
uint8_t v___x_3427_; 
lean_inc_ref(v_c_3335_);
v___x_3427_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3335_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
v___x_3428_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3335_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3428_);
v___x_3430_ = v___x_3410_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
lean_object* v___x_3432_; 
lean_del_object(v___x_3410_);
lean_inc_ref(v_c_3335_);
v___x_3432_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3335_, v_a_3336_, v_a_3340_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; uint8_t v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = lean_unbox(v_a_3433_);
lean_dec(v_a_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3441_ = l_Lean_mkApp3(v___x_3440_, v_arg_3419_, v_arg_3414_, v_a_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
return v___x_3435_;
}
}
else
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3456_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3456_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3456_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3452_ = l_Lean_mkApp3(v___x_3451_, v_arg_3419_, v_arg_3414_, v_a_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3452_);
v___x_3454_ = v___x_3449_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
return v___x_3446_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
lean_dec_ref(v_c_3335_);
v_a_3457_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3432_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3432_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3465_; 
lean_dec_ref(v___x_3420_);
lean_del_object(v___x_3410_);
v___x_3465_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3471_ = l_Lean_mkApp3(v___x_3470_, v_arg_3419_, v_arg_3414_, v_a_3466_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3471_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_dec_ref(v_arg_3419_);
lean_dec_ref(v_arg_3414_);
return v___x_3465_;
}
}
}
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_dec_ref(v___x_3415_);
lean_dec_ref(v_c_3335_);
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3414_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3476_);
v___x_3478_ = v___x_3410_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3335_);
return v___x_3407_;
}
v___jp_3347_:
{
if (v___y_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_inc_ref(v_c_3335_);
v___x_3359_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3335_, v___y_3350_, v___y_3354_, v___y_3357_, v___y_3349_, v___y_3353_, v___y_3356_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3378_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3378_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3378_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_unbox(v_a_3360_);
lean_dec(v_a_3360_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3366_; 
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v_c_3335_);
v___x_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_c_3335_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
else
{
lean_object* v___x_3368_; 
lean_del_object(v___x_3362_);
lean_inc_ref(v_c_3335_);
v___x_3368_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3335_, v___y_3350_, v___y_3355_, v___y_3352_, v___y_3348_, v___y_3354_, v___y_3351_, v___y_3357_, v___y_3349_, v___y_3353_, v___y_3356_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3335_, v_a_3369_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_dec_ref(v_c_3335_);
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec_ref(v_c_3335_);
v_a_3379_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3359_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3359_);
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
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = l_Lean_Expr_getAppNumArgs(v_c_3335_);
v___x_3389_ = lean_nat_sub(v___x_3388_, v___x_3387_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_nat_sub(v___x_3389_, v___x_3387_);
lean_dec(v___x_3389_);
v___x_3391_ = l_Lean_Expr_getRevArg_x21(v_c_3335_, v___x_3390_);
lean_dec_ref(v_c_3335_);
v___x_3392_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
return v___x_3393_;
}
}
v___jp_3394_:
{
uint8_t v___x_3405_; 
v___x_3405_ = l_Lean_Meta_Grind_isIte(v_c_3335_);
if (v___x_3405_ == 0)
{
uint8_t v___x_3406_; 
v___x_3406_ = l_Lean_Meta_Grind_isDIte(v_c_3335_);
v___y_3348_ = v___y_3398_;
v___y_3349_ = v___y_3402_;
v___y_3350_ = v___y_3395_;
v___y_3351_ = v___y_3400_;
v___y_3352_ = v___y_3397_;
v___y_3353_ = v___y_3403_;
v___y_3354_ = v___y_3399_;
v___y_3355_ = v___y_3396_;
v___y_3356_ = v___y_3404_;
v___y_3357_ = v___y_3401_;
v___y_3358_ = v___x_3406_;
goto v___jp_3347_;
}
else
{
v___y_3348_ = v___y_3398_;
v___y_3349_ = v___y_3402_;
v___y_3350_ = v___y_3395_;
v___y_3351_ = v___y_3400_;
v___y_3352_ = v___y_3397_;
v___y_3353_ = v___y_3403_;
v___y_3354_ = v___y_3399_;
v___y_3355_ = v___y_3396_;
v___y_3356_ = v___y_3404_;
v___y_3357_ = v___y_3401_;
v___y_3358_ = v___x_3405_;
goto v___jp_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec(v_a_3482_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3494_, lean_object* v_major_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3496_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; uint8_t v_trace_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_trace_3505_ = lean_ctor_get_uint8(v_a_3504_, sizeof(void*)*14);
lean_dec(v_a_3504_);
if (v_trace_3505_ == 0)
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Meta_Grind_cases(v_mvarId_3494_, v_major_3495_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; 
lean_inc(v_a_3501_);
lean_inc_ref(v_a_3500_);
lean_inc(v_a_3499_);
lean_inc_ref(v_a_3498_);
lean_inc_ref(v_major_3495_);
v___x_3507_ = lean_infer_type(v_major_3495_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l_Lean_Meta_whnfD(v_a_3508_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Expr_getAppFn(v_a_3510_);
lean_dec(v_a_3510_);
if (lean_obj_tag(v___x_3511_) == 4)
{
lean_object* v_declName_3512_; lean_object* v___x_3513_; 
v_declName_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_declName_3512_);
lean_dec_ref_known(v___x_3511_, 2);
v___x_3513_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3512_, v_a_3497_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; 
lean_dec_ref_known(v___x_3513_, 1);
v___x_3514_ = l_Lean_Meta_Grind_cases(v_mvarId_3494_, v_major_3495_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v___x_3514_;
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v_major_3495_);
lean_dec(v_mvarId_3494_);
v_a_3515_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3513_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v___x_3511_);
v___x_3523_ = l_Lean_Meta_Grind_cases(v_mvarId_3494_, v_major_3495_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v___x_3523_;
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v_major_3495_);
lean_dec(v_mvarId_3494_);
v_a_3524_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3509_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3509_);
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
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec_ref(v_major_3495_);
lean_dec(v_mvarId_3494_);
v_a_3532_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3507_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3507_);
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
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v_major_3495_);
lean_dec(v_mvarId_3494_);
v_a_3540_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3503_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3503_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3548_, lean_object* v_major_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3548_, v_major_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3558_, lean_object* v_major_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3558_, v_major_3559_, v_a_3562_, v_a_3563_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3572_, lean_object* v_major_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3572_, v_major_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
return v_res_3585_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3586_){
_start:
{
uint64_t v_anchor_3587_; 
v_anchor_3587_ = lean_ctor_get_uint64(v_e_3586_, sizeof(void*)*3);
return v_anchor_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3588_){
_start:
{
uint64_t v_res_3589_; lean_object* v_r_3590_; 
v_res_3589_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3588_);
lean_dec_ref(v_e_3588_);
v_r_3590_ = lean_box_uint64(v_res_3589_);
return v_r_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3593_, lean_object* v_x_3594_){
_start:
{
if (lean_obj_tag(v_x_3594_) == 0)
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_box(0);
return v___x_3595_;
}
else
{
lean_object* v_key_3596_; lean_object* v_value_3597_; lean_object* v_tail_3598_; uint64_t v___x_3599_; uint8_t v___x_3600_; 
v_key_3596_ = lean_ctor_get(v_x_3594_, 0);
v_value_3597_ = lean_ctor_get(v_x_3594_, 1);
v_tail_3598_ = lean_ctor_get(v_x_3594_, 2);
v___x_3599_ = lean_unbox_uint64(v_key_3596_);
v___x_3600_ = lean_uint64_dec_eq(v___x_3599_, v_a_3593_);
if (v___x_3600_ == 0)
{
v_x_3594_ = v_tail_3598_;
goto _start;
}
else
{
lean_object* v___x_3602_; 
lean_inc(v_value_3597_);
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_value_3597_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3603_, lean_object* v_x_3604_){
_start:
{
uint64_t v_a_boxed_3605_; lean_object* v_res_3606_; 
v_a_boxed_3605_ = lean_unbox_uint64(v_a_3603_);
lean_dec_ref(v_a_3603_);
v_res_3606_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3605_, v_x_3604_);
lean_dec(v_x_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3607_, uint64_t v_a_3608_){
_start:
{
lean_object* v_buckets_3609_; lean_object* v___x_3610_; uint64_t v___x_3611_; uint64_t v___x_3612_; uint64_t v_fold_3613_; uint64_t v___x_3614_; uint64_t v___x_3615_; uint64_t v___x_3616_; size_t v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_buckets_3609_ = lean_ctor_get(v_m_3607_, 1);
v___x_3610_ = lean_array_get_size(v_buckets_3609_);
v___x_3611_ = 32ULL;
v___x_3612_ = lean_uint64_shift_right(v_a_3608_, v___x_3611_);
v_fold_3613_ = lean_uint64_xor(v_a_3608_, v___x_3612_);
v___x_3614_ = 16ULL;
v___x_3615_ = lean_uint64_shift_right(v_fold_3613_, v___x_3614_);
v___x_3616_ = lean_uint64_xor(v_fold_3613_, v___x_3615_);
v___x_3617_ = lean_uint64_to_usize(v___x_3616_);
v___x_3618_ = lean_usize_of_nat(v___x_3610_);
v___x_3619_ = ((size_t)1ULL);
v___x_3620_ = lean_usize_sub(v___x_3618_, v___x_3619_);
v___x_3621_ = lean_usize_land(v___x_3617_, v___x_3620_);
v___x_3622_ = lean_array_uget_borrowed(v_buckets_3609_, v___x_3621_);
v___x_3623_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3608_, v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3624_, lean_object* v_a_3625_){
_start:
{
uint64_t v_a_boxed_3626_; lean_object* v_res_3627_; 
v_a_boxed_3626_ = lean_unbox_uint64(v_a_3625_);
lean_dec_ref(v_a_3625_);
v_res_3627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3624_, v_a_boxed_3626_);
lean_dec_ref(v_m_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
if (lean_obj_tag(v_x_3629_) == 0)
{
return v_x_3628_;
}
else
{
lean_object* v_key_3630_; lean_object* v_value_3631_; lean_object* v_tail_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3656_; 
v_key_3630_ = lean_ctor_get(v_x_3629_, 0);
v_value_3631_ = lean_ctor_get(v_x_3629_, 1);
v_tail_3632_ = lean_ctor_get(v_x_3629_, 2);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_x_3629_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3634_ = v_x_3629_;
v_isShared_3635_ = v_isSharedCheck_3656_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_tail_3632_);
lean_inc(v_value_3631_);
lean_inc(v_key_3630_);
lean_dec(v_x_3629_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3656_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; uint64_t v___x_3637_; uint64_t v___x_3638_; uint64_t v___x_3639_; uint64_t v___x_3640_; uint64_t v_fold_3641_; uint64_t v___x_3642_; uint64_t v___x_3643_; uint64_t v___x_3644_; size_t v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; size_t v___x_3648_; size_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3636_ = lean_array_get_size(v_x_3628_);
v___x_3637_ = 32ULL;
v___x_3638_ = lean_unbox_uint64(v_key_3630_);
v___x_3639_ = lean_uint64_shift_right(v___x_3638_, v___x_3637_);
v___x_3640_ = lean_unbox_uint64(v_key_3630_);
v_fold_3641_ = lean_uint64_xor(v___x_3640_, v___x_3639_);
v___x_3642_ = 16ULL;
v___x_3643_ = lean_uint64_shift_right(v_fold_3641_, v___x_3642_);
v___x_3644_ = lean_uint64_xor(v_fold_3641_, v___x_3643_);
v___x_3645_ = lean_uint64_to_usize(v___x_3644_);
v___x_3646_ = lean_usize_of_nat(v___x_3636_);
v___x_3647_ = ((size_t)1ULL);
v___x_3648_ = lean_usize_sub(v___x_3646_, v___x_3647_);
v___x_3649_ = lean_usize_land(v___x_3645_, v___x_3648_);
v___x_3650_ = lean_array_uget_borrowed(v_x_3628_, v___x_3649_);
lean_inc(v___x_3650_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 2, v___x_3650_);
v___x_3652_ = v___x_3634_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_key_3630_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_value_3631_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_array_uset(v_x_3628_, v___x_3649_, v___x_3652_);
v_x_3628_ = v___x_3653_;
v_x_3629_ = v_tail_3632_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3657_, lean_object* v_source_3658_, lean_object* v_target_3659_){
_start:
{
lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3660_ = lean_array_get_size(v_source_3658_);
v___x_3661_ = lean_nat_dec_lt(v_i_3657_, v___x_3660_);
if (v___x_3661_ == 0)
{
lean_dec_ref(v_source_3658_);
lean_dec(v_i_3657_);
return v_target_3659_;
}
else
{
lean_object* v_es_3662_; lean_object* v___x_3663_; lean_object* v_source_3664_; lean_object* v_target_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_es_3662_ = lean_array_fget(v_source_3658_, v_i_3657_);
v___x_3663_ = lean_box(0);
v_source_3664_ = lean_array_fset(v_source_3658_, v_i_3657_, v___x_3663_);
v_target_3665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3659_, v_es_3662_);
v___x_3666_ = lean_unsigned_to_nat(1u);
v___x_3667_ = lean_nat_add(v_i_3657_, v___x_3666_);
lean_dec(v_i_3657_);
v_i_3657_ = v___x_3667_;
v_source_3658_ = v_source_3664_;
v_target_3659_ = v_target_3665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3669_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_nbuckets_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3670_ = lean_array_get_size(v_data_3669_);
v___x_3671_ = lean_unsigned_to_nat(2u);
v_nbuckets_3672_ = lean_nat_mul(v___x_3670_, v___x_3671_);
v___x_3673_ = lean_unsigned_to_nat(0u);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_mk_array(v_nbuckets_3672_, v___x_3674_);
v___x_3676_ = lean_array_propagate_mark(v_data_3669_, v___x_3675_);
v___x_3677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3673_, v_data_3669_, v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3678_, lean_object* v_b_3679_, lean_object* v_x_3680_){
_start:
{
if (lean_obj_tag(v_x_3680_) == 0)
{
lean_dec(v_b_3679_);
return v_x_3680_;
}
else
{
lean_object* v_key_3681_; lean_object* v_value_3682_; lean_object* v_tail_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3697_; 
v_key_3681_ = lean_ctor_get(v_x_3680_, 0);
v_value_3682_ = lean_ctor_get(v_x_3680_, 1);
v_tail_3683_ = lean_ctor_get(v_x_3680_, 2);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_x_3680_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3685_ = v_x_3680_;
v_isShared_3686_ = v_isSharedCheck_3697_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_tail_3683_);
lean_inc(v_value_3682_);
lean_inc(v_key_3681_);
lean_dec(v_x_3680_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3697_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint64_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = lean_unbox_uint64(v_key_3681_);
v___x_3688_ = lean_uint64_dec_eq(v___x_3687_, v_a_3678_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3678_, v_b_3679_, v_tail_3683_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 2, v___x_3689_);
v___x_3691_ = v___x_3685_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_key_3681_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_value_3682_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3695_; 
lean_dec(v_value_3682_);
lean_dec(v_key_3681_);
v___x_3693_ = lean_box_uint64(v_a_3678_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 1, v_b_3679_);
lean_ctor_set(v___x_3685_, 0, v___x_3693_);
v___x_3695_ = v___x_3685_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_b_3679_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_tail_3683_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3698_, lean_object* v_b_3699_, lean_object* v_x_3700_){
_start:
{
uint64_t v_a_boxed_3701_; lean_object* v_res_3702_; 
v_a_boxed_3701_ = lean_unbox_uint64(v_a_3698_);
lean_dec_ref(v_a_3698_);
v_res_3702_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3701_, v_b_3699_, v_x_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3703_, lean_object* v_x_3704_){
_start:
{
if (lean_obj_tag(v_x_3704_) == 0)
{
uint8_t v___x_3705_; 
v___x_3705_ = 0;
return v___x_3705_;
}
else
{
lean_object* v_key_3706_; lean_object* v_tail_3707_; uint64_t v___x_3708_; uint8_t v___x_3709_; 
v_key_3706_ = lean_ctor_get(v_x_3704_, 0);
v_tail_3707_ = lean_ctor_get(v_x_3704_, 2);
v___x_3708_ = lean_unbox_uint64(v_key_3706_);
v___x_3709_ = lean_uint64_dec_eq(v___x_3708_, v_a_3703_);
if (v___x_3709_ == 0)
{
v_x_3704_ = v_tail_3707_;
goto _start;
}
else
{
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3711_, lean_object* v_x_3712_){
_start:
{
uint64_t v_a_boxed_3713_; uint8_t v_res_3714_; lean_object* v_r_3715_; 
v_a_boxed_3713_ = lean_unbox_uint64(v_a_3711_);
lean_dec_ref(v_a_3711_);
v_res_3714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3713_, v_x_3712_);
lean_dec(v_x_3712_);
v_r_3715_ = lean_box(v_res_3714_);
return v_r_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3716_, uint64_t v_a_3717_, lean_object* v_b_3718_){
_start:
{
lean_object* v_size_3719_; lean_object* v_buckets_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3763_; 
v_size_3719_ = lean_ctor_get(v_m_3716_, 0);
v_buckets_3720_ = lean_ctor_get(v_m_3716_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_m_3716_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3722_ = v_m_3716_;
v_isShared_3723_ = v_isSharedCheck_3763_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_buckets_3720_);
lean_inc(v_size_3719_);
lean_dec(v_m_3716_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3763_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; uint64_t v___x_3725_; uint64_t v___x_3726_; uint64_t v_fold_3727_; uint64_t v___x_3728_; uint64_t v___x_3729_; uint64_t v___x_3730_; size_t v___x_3731_; size_t v___x_3732_; size_t v___x_3733_; size_t v___x_3734_; size_t v___x_3735_; lean_object* v_bkt_3736_; uint8_t v___x_3737_; 
v___x_3724_ = lean_array_get_size(v_buckets_3720_);
v___x_3725_ = 32ULL;
v___x_3726_ = lean_uint64_shift_right(v_a_3717_, v___x_3725_);
v_fold_3727_ = lean_uint64_xor(v_a_3717_, v___x_3726_);
v___x_3728_ = 16ULL;
v___x_3729_ = lean_uint64_shift_right(v_fold_3727_, v___x_3728_);
v___x_3730_ = lean_uint64_xor(v_fold_3727_, v___x_3729_);
v___x_3731_ = lean_uint64_to_usize(v___x_3730_);
v___x_3732_ = lean_usize_of_nat(v___x_3724_);
v___x_3733_ = ((size_t)1ULL);
v___x_3734_ = lean_usize_sub(v___x_3732_, v___x_3733_);
v___x_3735_ = lean_usize_land(v___x_3731_, v___x_3734_);
v_bkt_3736_ = lean_array_uget_borrowed(v_buckets_3720_, v___x_3735_);
v___x_3737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3717_, v_bkt_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v_size_x27_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v_buckets_x27_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3738_ = lean_unsigned_to_nat(1u);
v_size_x27_3739_ = lean_nat_add(v_size_3719_, v___x_3738_);
lean_dec(v_size_3719_);
v___x_3740_ = lean_box_uint64(v_a_3717_);
lean_inc(v_bkt_3736_);
v___x_3741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set(v___x_3741_, 1, v_b_3718_);
lean_ctor_set(v___x_3741_, 2, v_bkt_3736_);
v_buckets_x27_3742_ = lean_array_uset(v_buckets_3720_, v___x_3735_, v___x_3741_);
v___x_3743_ = lean_unsigned_to_nat(4u);
v___x_3744_ = lean_nat_mul(v_size_x27_3739_, v___x_3743_);
v___x_3745_ = lean_unsigned_to_nat(3u);
v___x_3746_ = lean_nat_div(v___x_3744_, v___x_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_array_get_size(v_buckets_x27_3742_);
v___x_3748_ = lean_nat_dec_le(v___x_3746_, v___x_3747_);
lean_dec(v___x_3746_);
if (v___x_3748_ == 0)
{
lean_object* v_val_3749_; lean_object* v___x_3751_; 
v_val_3749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3742_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v_val_3749_);
lean_ctor_set(v___x_3722_, 0, v_size_x27_3739_);
v___x_3751_ = v___x_3722_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_size_x27_3739_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_val_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
else
{
lean_object* v___x_3754_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v_buckets_x27_3742_);
lean_ctor_set(v___x_3722_, 0, v_size_x27_3739_);
v___x_3754_ = v___x_3722_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_size_x27_3739_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_buckets_x27_3742_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
else
{
lean_object* v___x_3756_; lean_object* v_buckets_x27_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_inc(v_bkt_3736_);
v___x_3756_ = lean_box(0);
v_buckets_x27_3757_ = lean_array_uset(v_buckets_3720_, v___x_3735_, v___x_3756_);
v___x_3758_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3717_, v_b_3718_, v_bkt_3736_);
v___x_3759_ = lean_array_uset(v_buckets_x27_3757_, v___x_3735_, v___x_3758_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v___x_3759_);
v___x_3761_ = v___x_3722_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_size_3719_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3764_, lean_object* v_a_3765_, lean_object* v_b_3766_){
_start:
{
uint64_t v_a_boxed_3767_; lean_object* v_res_3768_; 
v_a_boxed_3767_ = lean_unbox_uint64(v_a_3765_);
lean_dec_ref(v_a_3765_);
v_res_3768_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3764_, v_a_boxed_3767_, v_b_3766_);
return v_res_3768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_unsigned_to_nat(16u);
v___x_3771_ = lean_mk_array(v___x_3770_, v___x_3769_);
return v___x_3771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v_found_3774_; 
v___x_3772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3773_ = lean_unsigned_to_nat(0u);
v_found_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3774_, 0, v___x_3773_);
lean_ctor_set(v_found_3774_, 1, v___x_3772_);
return v_found_3774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_found_3775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3776_ = lean_box(0);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v_found_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3778_, lean_object* v_numDigits_3779_, lean_object* v_es_3780_, lean_object* v_as_3781_, size_t v_sz_3782_, size_t v_i_3783_, lean_object* v_b_3784_){
_start:
{
lean_object* v_a_3786_; uint8_t v___x_3790_; 
v___x_3790_ = lean_usize_dec_lt(v_i_3783_, v_sz_3782_);
if (v___x_3790_ == 0)
{
return v_b_3784_;
}
else
{
lean_object* v_snd_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3825_; 
v_snd_3791_ = lean_ctor_get(v_b_3784_, 1);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_b_3784_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_b_3784_, 0);
lean_dec(v_unused_3826_);
v___x_3793_ = v_b_3784_;
v_isShared_3794_ = v_isSharedCheck_3825_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_snd_3791_);
lean_dec(v_b_3784_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3825_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v_a_3795_; uint64_t v_anchor_3796_; lean_object* v___x_3797_; uint64_t v___x_3798_; uint64_t v___x_3799_; lean_object* v___x_3800_; 
v_a_3795_ = lean_array_uget_borrowed(v_as_3781_, v_i_3783_);
v_anchor_3796_ = lean_ctor_get_uint64(v_a_3795_, sizeof(void*)*3);
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_uint64_of_nat(v_shift_3778_);
v___x_3799_ = lean_uint64_shift_right(v_anchor_3796_, v___x_3798_);
v___x_3800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3791_, v___x_3799_);
if (lean_obj_tag(v___x_3800_) == 1)
{
lean_object* v_val_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3819_; 
v_val_3801_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3803_ = v___x_3800_;
v_isShared_3804_ = v_isSharedCheck_3819_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_val_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3819_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
uint64_t v___x_3805_; uint8_t v___x_3806_; 
v___x_3805_ = lean_unbox_uint64(v_val_3801_);
lean_dec(v_val_3801_);
v___x_3806_ = lean_uint64_dec_eq(v___x_3805_, v_anchor_3796_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3807_ = lean_unsigned_to_nat(1u);
v___x_3808_ = lean_nat_add(v_numDigits_3779_, v___x_3807_);
v___x_3809_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3780_, v___x_3808_);
lean_dec(v___x_3808_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3809_);
v___x_3811_ = v___x_3803_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3811_);
v___x_3813_ = v___x_3793_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_snd_3791_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
else
{
lean_object* v___x_3817_; 
lean_del_object(v___x_3803_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3797_);
v___x_3817_ = v___x_3793_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_snd_3791_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
v_a_3786_ = v___x_3817_;
goto v___jp_3785_;
}
}
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_dec(v___x_3800_);
v___x_3820_ = lean_box_uint64(v_anchor_3796_);
v___x_3821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3791_, v___x_3799_, v___x_3820_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___x_3821_);
lean_ctor_set(v___x_3793_, 0, v___x_3797_);
v___x_3823_ = v___x_3793_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
v_a_3786_ = v___x_3823_;
goto v___jp_3785_;
}
}
}
}
v___jp_3785_:
{
size_t v___x_3787_; size_t v___x_3788_; 
v___x_3787_ = ((size_t)1ULL);
v___x_3788_ = lean_usize_add(v_i_3783_, v___x_3787_);
v_i_3783_ = v___x_3788_;
v_b_3784_ = v_a_3786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3827_, lean_object* v_numDigits_3828_){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3829_ = lean_unsigned_to_nat(4u);
v___x_3830_ = lean_nat_mul(v___x_3829_, v_numDigits_3828_);
v___x_3831_ = lean_unsigned_to_nat(64u);
v___x_3832_ = lean_nat_dec_lt(v___x_3830_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_dec(v___x_3830_);
lean_inc(v_numDigits_3828_);
return v_numDigits_3828_;
}
else
{
lean_object* v_shift_3833_; lean_object* v___x_3834_; size_t v_sz_3835_; size_t v___x_3836_; lean_object* v___x_3837_; lean_object* v_fst_3838_; 
v_shift_3833_ = lean_nat_sub(v___x_3831_, v___x_3830_);
lean_dec(v___x_3830_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3835_ = lean_array_size(v_es_3827_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3833_, v_numDigits_3828_, v_es_3827_, v_es_3827_, v_sz_3835_, v___x_3836_, v___x_3834_);
lean_dec(v_shift_3833_);
v_fst_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_fst_3838_);
lean_dec_ref(v___x_3837_);
if (lean_obj_tag(v_fst_3838_) == 0)
{
lean_inc(v_numDigits_3828_);
return v_numDigits_3828_;
}
else
{
lean_object* v_val_3839_; 
v_val_3839_ = lean_ctor_get(v_fst_3838_, 0);
lean_inc(v_val_3839_);
lean_dec_ref_known(v_fst_3838_, 1);
return v_val_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3840_, lean_object* v_numDigits_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3840_, v_numDigits_3841_);
lean_dec(v_numDigits_3841_);
lean_dec_ref(v_es_3840_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3843_, lean_object* v_numDigits_3844_, lean_object* v_es_3845_, lean_object* v_as_3846_, lean_object* v_sz_3847_, lean_object* v_i_3848_, lean_object* v_b_3849_){
_start:
{
size_t v_sz_boxed_3850_; size_t v_i_boxed_3851_; lean_object* v_res_3852_; 
v_sz_boxed_3850_ = lean_unbox_usize(v_sz_3847_);
lean_dec(v_sz_3847_);
v_i_boxed_3851_ = lean_unbox_usize(v_i_3848_);
lean_dec(v_i_3848_);
v_res_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3843_, v_numDigits_3844_, v_es_3845_, v_as_3846_, v_sz_boxed_3850_, v_i_boxed_3851_, v_b_3849_);
lean_dec_ref(v_as_3846_);
lean_dec_ref(v_es_3845_);
lean_dec(v_numDigits_3844_);
lean_dec(v_shift_3843_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3853_){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_unsigned_to_nat(4u);
v___x_3855_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3853_, v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3856_);
lean_dec_ref(v_es_3856_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3858_, lean_object* v_as_3859_, size_t v_i_3860_, size_t v_stop_3861_, lean_object* v_b_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_a_3875_; uint8_t v___x_3879_; 
v___x_3879_ = lean_usize_dec_eq(v_i_3860_, v_stop_3861_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v_e_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_array_uget_borrowed(v_as_3859_, v_i_3860_);
v_e_3881_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3880_);
v___x_3882_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3880_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
lean_inc(v___x_3880_);
v___x_3884_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3880_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
if (lean_obj_tag(v_a_3885_) == 2)
{
lean_object* v_numCases_3886_; uint8_t v_isRec_3887_; lean_object* v___x_3888_; 
v_numCases_3886_ = lean_ctor_get(v_a_3885_, 0);
lean_inc(v_numCases_3886_);
v_isRec_3887_ = lean_ctor_get_uint8(v_a_3885_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3885_, 1);
lean_inc_ref(v_filter_3858_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
lean_inc(v___y_3870_);
lean_inc_ref(v___y_3869_);
lean_inc(v___y_3868_);
lean_inc_ref(v___y_3867_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc(v___y_3864_);
lean_inc(v___y_3863_);
lean_inc_ref(v_e_3881_);
v___x_3888_ = lean_apply_12(v_filter_3858_, v_e_3881_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, lean_box(0));
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; uint8_t v___x_3890_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = lean_unbox(v_a_3889_);
lean_dec(v_a_3889_);
if (v___x_3890_ == 0)
{
lean_dec(v_numCases_3886_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3881_);
v_a_3875_ = v_b_3862_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3891_; uint64_t v___x_3892_; lean_object* v___x_3893_; 
lean_inc(v___x_3880_);
v___x_3891_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3891_, 0, v___x_3880_);
lean_ctor_set(v___x_3891_, 1, v_numCases_3886_);
lean_ctor_set(v___x_3891_, 2, v_e_3881_);
lean_ctor_set_uint8(v___x_3891_, sizeof(void*)*3 + 8, v_isRec_3887_);
v___x_3892_ = lean_unbox_uint64(v_a_3883_);
lean_dec(v_a_3883_);
lean_ctor_set_uint64(v___x_3891_, sizeof(void*)*3, v___x_3892_);
v___x_3893_ = lean_array_push(v_b_3862_, v___x_3891_);
v_a_3875_ = v___x_3893_;
goto v___jp_3874_;
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec(v_numCases_3886_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3881_);
lean_dec_ref(v_b_3862_);
lean_dec_ref(v_filter_3858_);
v_a_3894_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3888_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3888_);
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
lean_dec(v_a_3885_);
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3881_);
v_a_3875_ = v_b_3862_;
goto v___jp_3874_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_a_3883_);
lean_dec_ref(v_e_3881_);
lean_dec_ref(v_b_3862_);
lean_dec_ref(v_filter_3858_);
v_a_3902_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3884_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3884_);
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
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v_e_3881_);
lean_dec_ref(v_b_3862_);
lean_dec_ref(v_filter_3858_);
v_a_3910_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3882_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3882_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v___x_3918_; 
lean_dec_ref(v_filter_3858_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3862_);
return v___x_3918_;
}
v___jp_3874_:
{
size_t v___x_3876_; size_t v___x_3877_; 
v___x_3876_ = ((size_t)1ULL);
v___x_3877_ = lean_usize_add(v_i_3860_, v___x_3876_);
v_i_3860_ = v___x_3877_;
v_b_3862_ = v_a_3875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3919_, lean_object* v_as_3920_, lean_object* v_i_3921_, lean_object* v_stop_3922_, lean_object* v_b_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
size_t v_i_boxed_3935_; size_t v_stop_boxed_3936_; lean_object* v_res_3937_; 
v_i_boxed_3935_ = lean_unbox_usize(v_i_3921_);
lean_dec(v_i_3921_);
v_stop_boxed_3936_ = lean_unbox_usize(v_stop_3922_);
lean_dec(v_stop_3922_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3919_, v_as_3920_, v_i_boxed_3935_, v_stop_boxed_3936_, v_b_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v_as_3920_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3940_, lean_object* v_as_3941_, lean_object* v_start_3942_, lean_object* v_stop_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3955_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3956_ = lean_nat_dec_lt(v_start_3942_, v_stop_3943_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref(v_filter_3940_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = lean_array_get_size(v_as_3941_);
v___x_3959_ = lean_nat_dec_le(v_stop_3943_, v___x_3958_);
if (v___x_3959_ == 0)
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_nat_dec_lt(v_start_3942_, v___x_3958_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec_ref(v_filter_3940_);
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3955_);
return v___x_3961_;
}
else
{
size_t v___x_3962_; size_t v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_usize_of_nat(v_start_3942_);
v___x_3963_ = lean_usize_of_nat(v___x_3958_);
v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3940_, v_as_3941_, v___x_3962_, v___x_3963_, v___x_3955_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_3964_;
}
}
else
{
size_t v___x_3965_; size_t v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = lean_usize_of_nat(v_start_3942_);
v___x_3966_ = lean_usize_of_nat(v_stop_3943_);
v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3940_, v_as_3941_, v___x_3965_, v___x_3966_, v___x_3955_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_3967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3968_, lean_object* v_as_3969_, lean_object* v_start_3970_, lean_object* v_stop_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3968_, v_as_3969_, v_start_3970_, v_stop_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec(v_stop_3971_);
lean_dec(v_start_3970_);
lean_dec_ref(v_as_3969_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3984_, lean_object* v_candidates_x3f_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_candidates_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; 
if (lean_obj_tag(v_candidates_x3f_3985_) == 0)
{
lean_object* v___x_4031_; lean_object* v_toGoalState_4032_; lean_object* v_split_4033_; lean_object* v_candidates_4034_; 
v___x_4031_ = lean_st_ref_get(v_a_3986_);
v_toGoalState_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc_ref(v_toGoalState_4032_);
lean_dec(v___x_4031_);
v_split_4033_ = lean_ctor_get(v_toGoalState_4032_, 15);
lean_inc_ref(v_split_4033_);
lean_dec_ref(v_toGoalState_4032_);
v_candidates_4034_ = lean_ctor_get(v_split_4033_, 1);
lean_inc(v_candidates_4034_);
lean_dec_ref(v_split_4033_);
v_candidates_3998_ = v_candidates_4034_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
v___y_4003_ = v_a_3990_;
v___y_4004_ = v_a_3991_;
v___y_4005_ = v_a_3992_;
v___y_4006_ = v_a_3993_;
v___y_4007_ = v_a_3994_;
v___y_4008_ = v_a_3995_;
goto v___jp_3997_;
}
else
{
lean_object* v_val_4035_; 
v_val_4035_ = lean_ctor_get(v_candidates_x3f_3985_, 0);
lean_inc(v_val_4035_);
lean_dec_ref_known(v_candidates_x3f_3985_, 1);
v_candidates_3998_ = v_val_4035_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
v___y_4003_ = v_a_3990_;
v___y_4004_ = v_a_3991_;
v___y_4005_ = v_a_3992_;
v___y_4006_ = v_a_3993_;
v___y_4007_ = v_a_3994_;
v___y_4008_ = v_a_3995_;
goto v___jp_3997_;
}
v___jp_3997_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = lean_array_mk(v_candidates_3998_);
v___x_4010_ = lean_unsigned_to_nat(0u);
v___x_4011_ = lean_array_get_size(v___x_4009_);
v___x_4012_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3984_, v___x_4009_, v___x_4010_, v___x_4011_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec_ref(v___x_4009_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4022_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4017_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4013_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v_a_4013_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4018_);
v___x_4020_ = v___x_4015_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
v_a_4023_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4012_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4012_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4036_, lean_object* v_candidates_x3f_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4036_, v_candidates_x3f_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec(v_a_4038_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, uint64_t v_a_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4051_, v_a_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4054_, lean_object* v_m_4055_, lean_object* v_a_4056_){
_start:
{
uint64_t v_a_boxed_4057_; lean_object* v_res_4058_; 
v_a_boxed_4057_ = lean_unbox_uint64(v_a_4056_);
lean_dec_ref(v_a_4056_);
v_res_4058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4054_, v_m_4055_, v_a_boxed_4057_);
lean_dec_ref(v_m_4055_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4059_, lean_object* v_m_4060_, uint64_t v_a_4061_, lean_object* v_b_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4060_, v_a_4061_, v_b_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4064_, lean_object* v_m_4065_, lean_object* v_a_4066_, lean_object* v_b_4067_){
_start:
{
uint64_t v_a_boxed_4068_; lean_object* v_res_4069_; 
v_a_boxed_4068_ = lean_unbox_uint64(v_a_4066_);
lean_dec_ref(v_a_4066_);
v_res_4069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4064_, v_m_4065_, v_a_boxed_4068_, v_b_4067_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4070_, uint64_t v_a_4071_, lean_object* v_x_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4071_, v_x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4074_, lean_object* v_a_4075_, lean_object* v_x_4076_){
_start:
{
uint64_t v_a_boxed_4077_; lean_object* v_res_4078_; 
v_a_boxed_4077_ = lean_unbox_uint64(v_a_4075_);
lean_dec_ref(v_a_4075_);
v_res_4078_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4074_, v_a_boxed_4077_, v_x_4076_);
lean_dec(v_x_4076_);
return v_res_4078_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4079_, uint64_t v_a_4080_, lean_object* v_x_4081_){
_start:
{
uint8_t v___x_4082_; 
v___x_4082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4080_, v_x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4083_, lean_object* v_a_4084_, lean_object* v_x_4085_){
_start:
{
uint64_t v_a_boxed_4086_; uint8_t v_res_4087_; lean_object* v_r_4088_; 
v_a_boxed_4086_ = lean_unbox_uint64(v_a_4084_);
lean_dec_ref(v_a_4084_);
v_res_4087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4083_, v_a_boxed_4086_, v_x_4085_);
lean_dec(v_x_4085_);
v_r_4088_ = lean_box(v_res_4087_);
return v_r_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4089_, lean_object* v_data_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4092_, uint64_t v_a_4093_, lean_object* v_b_4094_, lean_object* v_x_4095_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4093_, v_b_4094_, v_x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4097_, lean_object* v_a_4098_, lean_object* v_b_4099_, lean_object* v_x_4100_){
_start:
{
uint64_t v_a_boxed_4101_; lean_object* v_res_4102_; 
v_a_boxed_4101_ = lean_unbox_uint64(v_a_4098_);
lean_dec_ref(v_a_4098_);
v_res_4102_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4097_, v_a_boxed_4101_, v_b_4099_, v_x_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4103_, lean_object* v_i_4104_, lean_object* v_source_4105_, lean_object* v_target_4106_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4104_, v_source_4105_, v_target_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4109_, v_x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
uint8_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4124_ = 1;
v___x_4125_ = lean_box(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v_x_4127_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4140_, uint64_t v_a_4141_, lean_object* v_c_4142_, lean_object* v_numDigits_4143_, lean_object* v_as_4144_, size_t v_sz_4145_, size_t v_i_4146_, lean_object* v_b_4147_){
_start:
{
lean_object* v_a_4150_; uint8_t v___x_4154_; 
v___x_4154_ = lean_usize_dec_lt(v_i_4146_, v_sz_4145_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; 
lean_dec(v_numDigits_4143_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_b_4147_);
return v___x_4155_;
}
else
{
lean_object* v_snd_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4182_; 
v_snd_4156_ = lean_ctor_get(v_b_4147_, 1);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_b_4147_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v_b_4147_, 0);
lean_dec(v_unused_4183_);
v___x_4158_ = v_b_4147_;
v_isShared_4159_ = v_isSharedCheck_4182_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_snd_4156_);
lean_dec(v_b_4147_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4182_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_a_4160_; lean_object* v_c_4161_; uint64_t v_anchor_4162_; lean_object* v___x_4163_; uint64_t v___x_4164_; uint64_t v___x_4165_; uint8_t v___x_4166_; 
v_a_4160_ = lean_array_uget_borrowed(v_as_4144_, v_i_4146_);
v_c_4161_ = lean_ctor_get(v_a_4160_, 0);
v_anchor_4162_ = lean_ctor_get_uint64(v_a_4160_, sizeof(void*)*3);
v___x_4163_ = lean_box(0);
v___x_4164_ = lean_uint64_shift_right(v_anchor_4162_, v___x_4140_);
v___x_4165_ = lean_uint64_shift_right(v_a_4141_, v___x_4140_);
v___x_4166_ = lean_uint64_dec_eq(v___x_4164_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4168_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4163_);
v___x_4168_ = v___x_4158_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v_snd_4156_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
v_a_4150_ = v___x_4168_;
goto v___jp_4149_;
}
}
else
{
uint8_t v___x_4170_; 
v___x_4170_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4161_, v_c_4142_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v___x_4171_ = lean_unsigned_to_nat(1u);
v___x_4172_ = lean_nat_add(v_snd_4156_, v___x_4171_);
lean_dec(v_snd_4156_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 1, v___x_4172_);
lean_ctor_set(v___x_4158_, 0, v___x_4163_);
v___x_4174_ = v___x_4158_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
v_a_4150_ = v___x_4174_;
goto v___jp_4149_;
}
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
lean_inc(v_snd_4156_);
v___x_4176_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4176_, 0, v_numDigits_4143_);
lean_ctor_set(v___x_4176_, 1, v_snd_4156_);
lean_ctor_set_uint64(v___x_4176_, sizeof(void*)*2, v_a_4141_);
v___x_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4177_);
v___x_4179_ = v___x_4158_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_snd_4156_);
v___x_4179_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
}
}
}
v___jp_4149_:
{
size_t v___x_4151_; size_t v___x_4152_; 
v___x_4151_ = ((size_t)1ULL);
v___x_4152_ = lean_usize_add(v_i_4146_, v___x_4151_);
v_i_4146_ = v___x_4152_;
v_b_4147_ = v_a_4150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4184_, lean_object* v_a_4185_, lean_object* v_c_4186_, lean_object* v_numDigits_4187_, lean_object* v_as_4188_, lean_object* v_sz_4189_, lean_object* v_i_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_){
_start:
{
uint64_t v___x_7681__boxed_4193_; uint64_t v_a_7682__boxed_4194_; size_t v_sz_boxed_4195_; size_t v_i_boxed_4196_; lean_object* v_res_4197_; 
v___x_7681__boxed_4193_ = lean_unbox_uint64(v___x_4184_);
lean_dec_ref(v___x_4184_);
v_a_7682__boxed_4194_ = lean_unbox_uint64(v_a_4185_);
lean_dec_ref(v_a_4185_);
v_sz_boxed_4195_ = lean_unbox_usize(v_sz_4189_);
lean_dec(v_sz_4189_);
v_i_boxed_4196_ = lean_unbox_usize(v_i_4190_);
lean_dec(v_i_4190_);
v_res_4197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7681__boxed_4193_, v_a_7682__boxed_4194_, v_c_4186_, v_numDigits_4187_, v_as_4188_, v_sz_boxed_4195_, v_i_boxed_4196_, v_b_4191_);
lean_dec_ref(v_as_4188_);
lean_dec_ref(v_c_4186_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4202_, lean_object* v_candidates_x3f_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___f_4215_; lean_object* v___x_4216_; 
v___f_4215_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4216_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4215_, v_candidates_x3f_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v_candidates_4218_; lean_object* v_numDigits_4219_; lean_object* v___x_4220_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v_candidates_4218_ = lean_ctor_get(v_a_4217_, 0);
lean_inc_ref(v_candidates_4218_);
v_numDigits_4219_ = lean_ctor_get(v_a_4217_, 1);
lean_inc(v_numDigits_4219_);
lean_dec(v_a_4217_);
v___x_4220_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4202_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint64_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; size_t v_sz_4229_; size_t v___x_4230_; uint64_t v___x_4231_; lean_object* v___x_4232_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = lean_unsigned_to_nat(64u);
v___x_4223_ = lean_unsigned_to_nat(4u);
v___x_4224_ = lean_nat_mul(v___x_4223_, v_numDigits_4219_);
v___x_4225_ = lean_nat_sub(v___x_4222_, v___x_4224_);
lean_dec(v___x_4224_);
v___x_4226_ = lean_uint64_of_nat(v___x_4225_);
lean_dec(v___x_4225_);
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4229_ = lean_array_size(v_candidates_4218_);
v___x_4230_ = ((size_t)0ULL);
v___x_4231_ = lean_unbox_uint64(v_a_4221_);
lean_inc(v_numDigits_4219_);
v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4226_, v___x_4231_, v_c_4202_, v_numDigits_4219_, v_candidates_4218_, v_sz_4229_, v___x_4230_, v___x_4228_);
lean_dec_ref(v_candidates_4218_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4247_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4235_ = v___x_4232_;
v_isShared_4236_ = v_isSharedCheck_4247_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4232_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4247_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v_fst_4237_; 
v_fst_4237_ = lean_ctor_get(v_a_4233_, 0);
lean_inc(v_fst_4237_);
lean_dec(v_a_4233_);
if (lean_obj_tag(v_fst_4237_) == 0)
{
lean_object* v___x_4238_; uint64_t v___x_4239_; lean_object* v___x_4241_; 
v___x_4238_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4238_, 0, v_numDigits_4219_);
lean_ctor_set(v___x_4238_, 1, v___x_4227_);
v___x_4239_ = lean_unbox_uint64(v_a_4221_);
lean_dec(v_a_4221_);
lean_ctor_set_uint64(v___x_4238_, sizeof(void*)*2, v___x_4239_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4238_);
v___x_4241_ = v___x_4235_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4238_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
else
{
lean_object* v_val_4243_; lean_object* v___x_4245_; 
lean_dec(v_a_4221_);
lean_dec(v_numDigits_4219_);
v_val_4243_ = lean_ctor_get(v_fst_4237_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v_fst_4237_, 1);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v_val_4243_);
v___x_4245_ = v___x_4235_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_val_4243_);
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
lean_dec(v_a_4221_);
lean_dec(v_numDigits_4219_);
v_a_4248_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4232_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4232_);
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
lean_dec(v_numDigits_4219_);
lean_dec_ref(v_candidates_4218_);
v_a_4256_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4220_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4220_);
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
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
v_a_4264_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4216_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4216_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4272_, lean_object* v_candidates_x3f_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4272_, v_candidates_x3f_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_c_4272_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4286_, uint64_t v_a_4287_, lean_object* v_c_4288_, lean_object* v_numDigits_4289_, lean_object* v_as_4290_, size_t v_sz_4291_, size_t v_i_4292_, lean_object* v_b_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4286_, v_a_4287_, v_c_4288_, v_numDigits_4289_, v_as_4290_, v_sz_4291_, v_i_4292_, v_b_4293_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4306_ = _args[0];
lean_object* v_a_4307_ = _args[1];
lean_object* v_c_4308_ = _args[2];
lean_object* v_numDigits_4309_ = _args[3];
lean_object* v_as_4310_ = _args[4];
lean_object* v_sz_4311_ = _args[5];
lean_object* v_i_4312_ = _args[6];
lean_object* v_b_4313_ = _args[7];
lean_object* v___y_4314_ = _args[8];
lean_object* v___y_4315_ = _args[9];
lean_object* v___y_4316_ = _args[10];
lean_object* v___y_4317_ = _args[11];
lean_object* v___y_4318_ = _args[12];
lean_object* v___y_4319_ = _args[13];
lean_object* v___y_4320_ = _args[14];
lean_object* v___y_4321_ = _args[15];
lean_object* v___y_4322_ = _args[16];
lean_object* v___y_4323_ = _args[17];
lean_object* v___y_4324_ = _args[18];
_start:
{
uint64_t v___x_7880__boxed_4325_; uint64_t v_a_7881__boxed_4326_; size_t v_sz_boxed_4327_; size_t v_i_boxed_4328_; lean_object* v_res_4329_; 
v___x_7880__boxed_4325_ = lean_unbox_uint64(v___x_4306_);
lean_dec_ref(v___x_4306_);
v_a_7881__boxed_4326_ = lean_unbox_uint64(v_a_4307_);
lean_dec_ref(v_a_4307_);
v_sz_boxed_4327_ = lean_unbox_usize(v_sz_4311_);
lean_dec(v_sz_4311_);
v_i_boxed_4328_ = lean_unbox_usize(v_i_4312_);
lean_dec(v_i_4312_);
v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7880__boxed_4325_, v_a_7881__boxed_4326_, v_c_4308_, v_numDigits_4309_, v_as_4310_, v_sz_boxed_4327_, v_i_boxed_4328_, v_b_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v_as_4310_);
lean_dec_ref(v_c_4308_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_numDigits_4357_; uint64_t v_anchor_4358_; lean_object* v_ordinal_4359_; lean_object* v___x_4360_; 
v_numDigits_4357_ = lean_ctor_get(v_info_4354_, 0);
v_anchor_4358_ = lean_ctor_get_uint64(v_info_4354_, sizeof(void*)*2);
v_ordinal_4359_ = lean_ctor_get(v_info_4354_, 1);
v___x_4360_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4357_, v_anchor_4358_, v_a_4355_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4397_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4363_ = v___x_4360_;
v_isShared_4364_ = v_isSharedCheck_4397_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4360_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4397_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = lean_nat_dec_eq(v_ordinal_4359_, v___x_4365_);
if (v___x_4366_ == 0)
{
lean_object* v_ref_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v_ref_4367_ = lean_ctor_get(v_a_4355_, 2);
v___x_4368_ = l_Lean_SourceInfo_fromRef(v_ref_4367_, v___x_4366_);
v___x_4369_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4370_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4368_, 3);
v___x_4371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4368_);
lean_ctor_set(v___x_4371_, 1, v___x_4369_);
v___x_4372_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4373_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4368_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = lean_unsigned_to_nat(1u);
v___x_4376_ = lean_nat_add(v_ordinal_4359_, v___x_4375_);
v___x_4377_ = l_Nat_reprFast(v___x_4376_);
v___x_4378_ = lean_box(2);
v___x_4379_ = l_Lean_Syntax_mkNumLit(v___x_4377_, v___x_4378_);
v___x_4380_ = l_Lean_Syntax_node3(v___x_4368_, v___x_4372_, v_a_4361_, v___x_4374_, v___x_4379_);
v___x_4381_ = l_Lean_Syntax_node2(v___x_4368_, v___x_4370_, v___x_4371_, v___x_4380_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4381_);
v___x_4383_ = v___x_4363_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
else
{
lean_object* v_ref_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v_ref_4385_ = lean_ctor_get(v_a_4355_, 2);
v___x_4386_ = 0;
v___x_4387_ = l_Lean_SourceInfo_fromRef(v_ref_4385_, v___x_4386_);
v___x_4388_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4389_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4387_, 2);
v___x_4390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4387_);
lean_ctor_set(v___x_4390_, 1, v___x_4388_);
v___x_4391_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4392_ = l_Lean_Syntax_node1(v___x_4387_, v___x_4391_, v_a_4361_);
v___x_4393_ = l_Lean_Syntax_node2(v___x_4387_, v___x_4389_, v___x_4390_, v___x_4392_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4393_);
v___x_4395_ = v___x_4363_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
return v___x_4360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4398_, v_a_4399_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_info_4398_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4402_, v_a_4403_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4407_, v_a_4408_, v_a_4409_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec_ref(v_info_4407_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v_p_4443_; lean_object* v___x_4446_; 
lean_inc_ref(v_proof_4424_);
v___x_4446_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4424_, v_a_4426_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4473_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4473_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4473_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4451_; uint8_t v___x_4452_; 
v___x_4451_ = l_Lean_Expr_cleanupAnnotations(v_a_4447_);
v___x_4452_ = l_Lean_Expr_isApp(v___x_4451_);
if (v___x_4452_ == 0)
{
lean_dec_ref(v___x_4451_);
lean_del_object(v___x_4449_);
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
v___y_4433_ = v_a_4427_;
v___y_4434_ = v_a_4428_;
goto v___jp_4430_;
}
else
{
lean_object* v_arg_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v_arg_4453_ = lean_ctor_get(v___x_4451_, 1);
lean_inc_ref(v_arg_4453_);
v___x_4454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4451_);
v___x_4455_ = l_Lean_Expr_isApp(v___x_4454_);
if (v___x_4455_ == 0)
{
lean_dec_ref(v___x_4454_);
lean_dec_ref(v_arg_4453_);
lean_del_object(v___x_4449_);
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
v___y_4433_ = v_a_4427_;
v___y_4434_ = v_a_4428_;
goto v___jp_4430_;
}
else
{
lean_object* v_arg_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; uint8_t v___x_4459_; 
v_arg_4456_ = lean_ctor_get(v___x_4454_, 1);
lean_inc_ref(v_arg_4456_);
v___x_4457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4454_);
v___x_4458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4459_ = l_Lean_Expr_isConstOf(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; uint8_t v___x_4461_; 
lean_dec_ref(v_arg_4456_);
lean_del_object(v___x_4449_);
v___x_4460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4461_ = l_Lean_Expr_isConstOf(v___x_4457_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4463_ = l_Lean_Expr_isConstOf(v___x_4457_, v___x_4462_);
lean_dec_ref(v___x_4457_);
if (v___x_4463_ == 0)
{
lean_dec_ref(v_arg_4453_);
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
v___y_4433_ = v_a_4427_;
v___y_4434_ = v_a_4428_;
goto v___jp_4430_;
}
else
{
lean_dec_ref(v_proof_4424_);
v_p_4443_ = v_arg_4453_;
goto v___jp_4442_;
}
}
else
{
lean_dec_ref(v___x_4457_);
lean_dec_ref(v_proof_4424_);
v_p_4443_ = v_arg_4453_;
goto v___jp_4442_;
}
}
else
{
uint8_t v___x_4464_; 
lean_dec_ref(v___x_4457_);
lean_dec_ref(v_proof_4424_);
v___x_4464_ = l_Lean_Expr_isFalse(v_arg_4456_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
lean_dec_ref(v_arg_4453_);
v___x_4465_ = lean_box(0);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4465_);
v___x_4467_ = v___x_4449_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4469_, 0, v_arg_4453_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4469_);
v___x_4471_ = v___x_4449_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref(v_proof_4424_);
v_a_4474_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4446_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4446_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
v___jp_4430_:
{
if (lean_obj_tag(v_proof_4424_) == 6)
{
lean_object* v_body_4435_; uint8_t v___x_4436_; 
v_body_4435_ = lean_ctor_get(v_proof_4424_, 2);
lean_inc_ref(v_body_4435_);
lean_dec_ref_known(v_proof_4424_, 3);
v___x_4436_ = l_Lean_Expr_hasLooseBVars(v_body_4435_);
if (v___x_4436_ == 0)
{
v_proof_4424_ = v_body_4435_;
v_a_4425_ = v___y_4431_;
v_a_4426_ = v___y_4432_;
v_a_4427_ = v___y_4433_;
v_a_4428_ = v___y_4434_;
goto _start;
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec_ref(v_body_4435_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
return v___x_4439_;
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec_ref(v_proof_4424_);
v___x_4440_ = lean_box(0);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
return v___x_4441_;
}
}
v___jp_4442_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4444_, 0, v_p_4443_);
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
return v___x_4445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4489_, lean_object* v___y_4490_){
_start:
{
uint8_t v___x_4492_; 
v___x_4492_ = l_Lean_Expr_hasMVar(v_e_4489_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v_e_4489_);
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v_mctx_4495_; lean_object* v___x_4496_; lean_object* v_fst_4497_; lean_object* v_snd_4498_; lean_object* v___x_4499_; lean_object* v_cache_4500_; lean_object* v_zetaDeltaFVarIds_4501_; lean_object* v_postponed_4502_; lean_object* v_diag_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4512_; 
v___x_4494_ = lean_st_ref_get(v___y_4490_);
v_mctx_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc_ref(v_mctx_4495_);
lean_dec(v___x_4494_);
v___x_4496_ = l_Lean_instantiateMVarsCore(v_mctx_4495_, v_e_4489_);
v_fst_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_fst_4497_);
v_snd_4498_ = lean_ctor_get(v___x_4496_, 1);
lean_inc(v_snd_4498_);
lean_dec_ref(v___x_4496_);
v___x_4499_ = lean_st_ref_take(v___y_4490_);
v_cache_4500_ = lean_ctor_get(v___x_4499_, 1);
v_zetaDeltaFVarIds_4501_ = lean_ctor_get(v___x_4499_, 2);
v_postponed_4502_ = lean_ctor_get(v___x_4499_, 3);
v_diag_4503_ = lean_ctor_get(v___x_4499_, 4);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; 
v_unused_4513_ = lean_ctor_get(v___x_4499_, 0);
lean_dec(v_unused_4513_);
v___x_4505_ = v___x_4499_;
v_isShared_4506_ = v_isSharedCheck_4512_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_diag_4503_);
lean_inc(v_postponed_4502_);
lean_inc(v_zetaDeltaFVarIds_4501_);
lean_inc(v_cache_4500_);
lean_dec(v___x_4499_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4512_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 0, v_snd_4498_);
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_snd_4498_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_cache_4500_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_zetaDeltaFVarIds_4501_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v_postponed_4502_);
lean_ctor_set(v_reuseFailAlloc_4511_, 4, v_diag_4503_);
v___x_4508_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = lean_st_ref_put(v___y_4490_, v___x_4508_);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v_fst_4497_);
return v___x_4510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4514_, v___y_4515_);
lean_dec(v___y_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4518_, v___y_4520_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4532_, lean_object* v_x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4532_, v_x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
v_a_4548_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4539_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4539_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4556_, lean_object* v_x_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4556_, v_x_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4564_, lean_object* v_mvarId_4565_, lean_object* v_x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4565_, v_x_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4573_, lean_object* v_mvarId_4574_, lean_object* v_x_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4573_, v_mvarId_4574_, v_x_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4599_; 
v___x_4588_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4582_, v___y_4584_);
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4591_ = v___x_4588_;
v_isShared_4592_ = v_isSharedCheck_4599_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4588_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4599_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
uint8_t v___x_4593_; 
v___x_4593_ = l_Lean_Expr_hasSyntheticSorry(v_a_4589_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_del_object(v___x_4591_);
v___x_4594_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4589_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
return v___x_4594_;
}
else
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
lean_dec(v_a_4589_);
v___x_4595_ = lean_box(0);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 0, v___x_4595_);
v___x_4597_ = v___x_4591_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___x_4613_; lean_object* v___f_4614_; lean_object* v___x_4615_; 
lean_inc(v_mvarId_4607_);
v___x_4613_ = l_Lean_mkMVar(v_mvarId_4607_);
v___f_4614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4614_, 0, v___x_4613_);
v___x_4615_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4607_, v___f_4614_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
return v_res_4622_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4644_){
_start:
{
if (lean_obj_tag(v_x_4644_) == 0)
{
uint8_t v___x_4645_; 
v___x_4645_ = 1;
return v___x_4645_;
}
else
{
lean_object* v_head_4646_; lean_object* v_tail_4647_; uint8_t v___y_4649_; lean_object* v___x_4651_; uint8_t v___x_4652_; 
v_head_4646_ = lean_ctor_get(v_x_4644_, 0);
lean_inc_n(v_head_4646_, 2);
v_tail_4647_ = lean_ctor_get(v_x_4644_, 1);
lean_inc(v_tail_4647_);
lean_dec_ref_known(v_x_4644_, 2);
v___x_4651_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4652_ = l_Lean_Syntax_isOfKind(v_head_4646_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4653_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4646_);
v___x_4654_ = l_Lean_Syntax_isOfKind(v_head_4646_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_dec(v_head_4646_);
v_x_4644_ = v_tail_4647_;
goto _start;
}
else
{
if (v___x_4652_ == 0)
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4656_ = lean_unsigned_to_nat(1u);
v___x_4657_ = l_Lean_Syntax_getArg(v_head_4646_, v___x_4656_);
lean_dec(v_head_4646_);
v___x_4658_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4659_ = l_Lean_Syntax_isOfKind(v___x_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
v_x_4644_ = v_tail_4647_;
goto _start;
}
else
{
v___y_4649_ = v___x_4652_;
goto v___jp_4648_;
}
}
else
{
lean_dec(v_head_4646_);
v___y_4649_ = v___x_4652_;
goto v___jp_4648_;
}
}
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(3u);
v___x_4662_ = l_Lean_Syntax_getArg(v_head_4646_, v___x_4661_);
lean_dec(v_head_4646_);
v___x_4663_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4664_ = l_Lean_Syntax_isOfKind(v___x_4662_, v___x_4663_);
if (v___x_4664_ == 0)
{
v_x_4644_ = v_tail_4647_;
goto _start;
}
else
{
uint8_t v___x_4666_; 
lean_dec(v_tail_4647_);
v___x_4666_ = 0;
return v___x_4666_;
}
}
v___jp_4648_:
{
if (v___y_4649_ == 0)
{
lean_dec(v_tail_4647_);
return v___y_4649_;
}
else
{
v_x_4644_ = v_tail_4647_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4667_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4670_){
_start:
{
uint8_t v___x_4671_; 
v___x_4671_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4672_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4690_, lean_object* v_a_4691_){
_start:
{
if (lean_obj_tag(v_seq_4690_) == 0)
{
lean_object* v_ref_4693_; uint8_t v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_ref_4693_ = lean_ctor_get(v_a_4691_, 2);
v___x_4694_ = 0;
v___x_4695_ = l_Lean_SourceInfo_fromRef(v_ref_4693_, v___x_4694_);
v___x_4696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4695_);
v___x_4698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4695_);
lean_ctor_set(v___x_4698_, 1, v___x_4696_);
v___x_4699_ = l_Lean_Syntax_node1(v___x_4695_, v___x_4697_, v___x_4698_);
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
return v___x_4700_;
}
else
{
lean_object* v_tail_4701_; 
v_tail_4701_ = lean_ctor_get(v_seq_4690_, 1);
if (lean_obj_tag(v_tail_4701_) == 0)
{
lean_object* v_head_4702_; lean_object* v___x_4703_; 
v_head_4702_ = lean_ctor_get(v_seq_4690_, 0);
lean_inc(v_head_4702_);
lean_dec_ref_known(v_seq_4690_, 2);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v_head_4702_);
return v___x_4703_;
}
else
{
lean_object* v_head_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4726_; 
lean_inc(v_tail_4701_);
v_head_4704_ = lean_ctor_get(v_seq_4690_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_seq_4690_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; 
v_unused_4727_ = lean_ctor_get(v_seq_4690_, 1);
lean_dec(v_unused_4727_);
v___x_4706_ = v_seq_4690_;
v_isShared_4707_ = v_isSharedCheck_4726_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_head_4704_);
lean_dec(v_seq_4690_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4726_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4725_; 
v___x_4708_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4701_, v_a_4691_);
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4725_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4725_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v_ref_4713_; uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v_ref_4713_ = lean_ctor_get(v_a_4691_, 2);
v___x_4714_ = 0;
v___x_4715_ = l_Lean_SourceInfo_fromRef(v_ref_4713_, v___x_4714_);
v___x_4716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4715_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 2);
lean_ctor_set(v___x_4706_, 1, v___x_4717_);
lean_ctor_set(v___x_4706_, 0, v___x_4715_);
v___x_4719_ = v___x_4706_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4720_; lean_object* v___x_4722_; 
v___x_4720_ = l_Lean_Syntax_node3(v___x_4715_, v___x_4716_, v_head_4704_, v___x_4719_, v_a_4709_);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v___x_4720_);
v___x_4722_ = v___x_4711_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4720_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4728_, v_a_4729_);
lean_dec_ref(v_a_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4732_, v_a_4733_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4737_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4742_, lean_object* v_seq_4743_, lean_object* v_a_4744_){
_start:
{
if (lean_obj_tag(v_seq_4743_) == 0)
{
lean_object* v___x_4746_; 
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v_cases_4742_);
return v___x_4746_;
}
else
{
lean_object* v___x_4747_; lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4762_; 
v___x_4747_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4743_, v_a_4744_);
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4750_ = v___x_4747_;
v_isShared_4751_ = v_isSharedCheck_4762_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4747_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4762_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v_ref_4752_; uint8_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v_ref_4752_ = lean_ctor_get(v_a_4744_, 2);
v___x_4753_ = 0;
v___x_4754_ = l_Lean_SourceInfo_fromRef(v_ref_4752_, v___x_4753_);
v___x_4755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4754_);
v___x_4757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4754_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l_Lean_Syntax_node3(v___x_4754_, v___x_4755_, v_cases_4742_, v___x_4757_, v_a_4748_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 0, v___x_4758_);
v___x_4760_ = v___x_4750_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4763_, lean_object* v_seq_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4763_, v_seq_4764_, v_a_4765_);
lean_dec_ref(v_a_4765_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4768_, lean_object* v_seq_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4768_, v_seq_4769_, v_a_4770_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4774_, lean_object* v_seq_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4774_, v_seq_4775_, v_a_4776_, v_a_4777_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
return v_res_4779_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4780_, lean_object* v_x_4781_){
_start:
{
if (lean_obj_tag(v_x_4780_) == 0)
{
if (lean_obj_tag(v_x_4781_) == 0)
{
uint8_t v___x_4782_; 
v___x_4782_ = 1;
return v___x_4782_;
}
else
{
uint8_t v___x_4783_; 
v___x_4783_ = 0;
return v___x_4783_;
}
}
else
{
if (lean_obj_tag(v_x_4781_) == 0)
{
uint8_t v___x_4784_; 
v___x_4784_ = 0;
return v___x_4784_;
}
else
{
lean_object* v_head_4785_; lean_object* v_tail_4786_; lean_object* v_head_4787_; lean_object* v_tail_4788_; uint8_t v___x_4789_; 
v_head_4785_ = lean_ctor_get(v_x_4780_, 0);
v_tail_4786_ = lean_ctor_get(v_x_4780_, 1);
v_head_4787_ = lean_ctor_get(v_x_4781_, 0);
v_tail_4788_ = lean_ctor_get(v_x_4781_, 1);
v___x_4789_ = l_Lean_Syntax_structEq(v_head_4785_, v_head_4787_);
if (v___x_4789_ == 0)
{
return v___x_4789_;
}
else
{
v_x_4780_ = v_tail_4786_;
v_x_4781_ = v_tail_4788_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4791_, lean_object* v_x_4792_){
_start:
{
uint8_t v_res_4793_; lean_object* v_r_4794_; 
v_res_4793_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4791_, v_x_4792_);
lean_dec(v_x_4792_);
lean_dec(v_x_4791_);
v_r_4794_ = lean_box(v_res_4793_);
return v_r_4794_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4795_, lean_object* v___x_4796_, lean_object* v_as_4797_, size_t v_i_4798_, size_t v_stop_4799_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = lean_usize_dec_eq(v_i_4798_, v_stop_4799_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = lean_array_uget_borrowed(v_as_4797_, v_i_4798_);
v___x_4806_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4805_, v_alt_4795_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4807_ = lean_unsigned_to_nat(0u);
v___x_4808_ = lean_nat_dec_lt(v___x_4807_, v___x_4796_);
if (v___x_4808_ == 0)
{
goto v___jp_4800_;
}
else
{
return v___x_4808_;
}
}
else
{
goto v___jp_4800_;
}
}
else
{
uint8_t v___x_4809_; 
v___x_4809_ = 0;
return v___x_4809_;
}
v___jp_4800_:
{
size_t v___x_4801_; size_t v___x_4802_; 
v___x_4801_ = ((size_t)1ULL);
v___x_4802_ = lean_usize_add(v_i_4798_, v___x_4801_);
v_i_4798_ = v___x_4802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4810_, lean_object* v___x_4811_, lean_object* v_as_4812_, lean_object* v_i_4813_, lean_object* v_stop_4814_){
_start:
{
size_t v_i_boxed_4815_; size_t v_stop_boxed_4816_; uint8_t v_res_4817_; lean_object* v_r_4818_; 
v_i_boxed_4815_ = lean_unbox_usize(v_i_4813_);
lean_dec(v_i_4813_);
v_stop_boxed_4816_ = lean_unbox_usize(v_stop_4814_);
lean_dec(v_stop_4814_);
v_res_4817_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4810_, v___x_4811_, v_as_4812_, v_i_boxed_4815_, v_stop_boxed_4816_);
lean_dec_ref(v_as_4812_);
lean_dec(v___x_4811_);
lean_dec(v_alt_4810_);
v_r_4818_ = lean_box(v_res_4817_);
return v_r_4818_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4819_){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; uint8_t v___x_4822_; 
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = lean_array_get_size(v_alts_4819_);
v___x_4822_ = lean_nat_dec_lt(v___x_4820_, v___x_4821_);
if (v___x_4822_ == 0)
{
uint8_t v___x_4823_; 
v___x_4823_ = 1;
return v___x_4823_;
}
else
{
lean_object* v_alt_4824_; uint8_t v___x_4825_; 
v_alt_4824_ = lean_array_fget_borrowed(v_alts_4819_, v___x_4820_);
lean_inc(v_alt_4824_);
v___x_4825_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4824_);
if (v___x_4825_ == 0)
{
return v___x_4825_;
}
else
{
if (v___x_4822_ == 0)
{
return v___x_4822_;
}
else
{
if (v___x_4822_ == 0)
{
return v___x_4822_;
}
else
{
size_t v___x_4826_; size_t v___x_4827_; uint8_t v___x_4828_; 
v___x_4826_ = ((size_t)0ULL);
v___x_4827_ = lean_usize_of_nat(v___x_4821_);
v___x_4828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4824_, v___x_4821_, v_alts_4819_, v___x_4826_, v___x_4827_);
if (v___x_4828_ == 0)
{
return v___x_4822_;
}
else
{
uint8_t v___x_4829_; 
v___x_4829_ = 0;
return v___x_4829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4830_){
_start:
{
uint8_t v_res_4831_; lean_object* v_r_4832_; 
v_res_4831_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4830_);
lean_dec_ref(v_alts_4830_);
v_r_4832_ = lean_box(v_res_4831_);
return v_r_4832_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4840_){
_start:
{
if (lean_obj_tag(v_alt_4840_) == 1)
{
lean_object* v_tail_4841_; 
v_tail_4841_ = lean_ctor_get(v_alt_4840_, 1);
if (lean_obj_tag(v_tail_4841_) == 0)
{
lean_object* v_head_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v_head_4842_ = lean_ctor_get(v_alt_4840_, 0);
lean_inc(v_head_4842_);
lean_dec_ref_known(v_alt_4840_, 2);
v___x_4843_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4844_ = l_Lean_Syntax_isOfKind(v_head_4842_, v___x_4843_);
return v___x_4844_;
}
else
{
uint8_t v___x_4845_; 
lean_dec_ref_known(v_alt_4840_, 2);
v___x_4845_ = 0;
return v___x_4845_;
}
}
else
{
uint8_t v___x_4846_; 
lean_dec(v_alt_4840_);
v___x_4846_ = 0;
return v___x_4846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4847_){
_start:
{
uint8_t v_res_4848_; lean_object* v_r_4849_; 
v_res_4848_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4847_);
v_r_4849_ = lean_box(v_res_4848_);
return v_r_4849_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4850_, lean_object* v_x_4851_, lean_object* v___y_4852_){
_start:
{
if (lean_obj_tag(v_x_4850_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = l_List_reverse___redArg(v_x_4851_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
return v___x_4855_;
}
else
{
lean_object* v_head_4856_; lean_object* v_tail_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4875_; 
v_head_4856_ = lean_ctor_get(v_x_4850_, 0);
v_tail_4857_ = lean_ctor_get(v_x_4850_, 1);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_x_4850_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4859_ = v_x_4850_;
v_isShared_4860_ = v_isSharedCheck_4875_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_tail_4857_);
lean_inc(v_head_4856_);
lean_dec(v_x_4850_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4875_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4856_, v___y_4852_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4864_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
if (v_isShared_4860_ == 0)
{
lean_ctor_set(v___x_4859_, 1, v_x_4851_);
lean_ctor_set(v___x_4859_, 0, v_a_4862_);
v___x_4864_ = v___x_4859_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4862_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_x_4851_);
v___x_4864_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
v_x_4850_ = v_tail_4857_;
v_x_4851_ = v___x_4864_;
goto _start;
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_del_object(v___x_4859_);
lean_dec(v_tail_4857_);
lean_dec(v_x_4851_);
v_a_4867_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4861_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4861_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4876_, lean_object* v_x_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4876_, v_x_4877_, v___y_4878_);
lean_dec_ref(v___y_4878_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4881_, lean_object* v_alts_4882_, uint8_t v_compress_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_seq_4888_; 
if (v_compress_4883_ == 0)
{
goto v___jp_4891_;
}
else
{
uint8_t v___x_4901_; 
v___x_4901_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4882_);
if (v___x_4901_ == 0)
{
goto v___jp_4891_;
}
else
{
lean_object* v___x_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4902_ = lean_unsigned_to_nat(0u);
v___x_4903_ = lean_array_get_size(v_alts_4882_);
v___x_4904_ = lean_nat_dec_lt(v___x_4902_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_dec_ref(v_alts_4882_);
v___x_4905_ = lean_box(0);
v___x_4906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4906_, 0, v_cases_4881_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
else
{
lean_object* v___x_4908_; lean_object* v_firstAlt_4909_; uint8_t v___x_4910_; 
v___x_4908_ = lean_box(0);
v_firstAlt_4909_ = lean_array_get(v___x_4908_, v_alts_4882_, v___x_4902_);
lean_dec_ref(v_alts_4882_);
lean_inc(v_firstAlt_4909_);
v___x_4910_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4909_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4920_; 
v___x_4911_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4881_, v_firstAlt_4909_, v_a_4884_);
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4920_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4920_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4916_, 0, v_a_4912_);
lean_ctor_set(v___x_4916_, 1, v___x_4908_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4916_);
v___x_4918_ = v___x_4914_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
else
{
lean_object* v___x_4921_; 
lean_dec(v_cases_4881_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_firstAlt_4909_);
return v___x_4921_;
}
}
}
}
v___jp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_cases_4881_);
lean_ctor_set(v___x_4889_, 1, v_seq_4888_);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
v___jp_4891_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; uint8_t v___x_4894_; 
v___x_4892_ = lean_array_get_size(v_alts_4882_);
v___x_4893_ = lean_unsigned_to_nat(1u);
v___x_4894_ = lean_nat_dec_eq(v___x_4892_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4895_ = lean_array_to_list(v_alts_4882_);
v___x_4896_ = lean_box(0);
v___x_4897_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4895_, v___x_4896_, v_a_4884_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref_known(v___x_4897_, 1);
v_seq_4888_ = v_a_4898_;
goto v___jp_4887_;
}
else
{
lean_dec(v_cases_4881_);
return v___x_4897_;
}
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = lean_unsigned_to_nat(0u);
v___x_4900_ = lean_array_fget(v_alts_4882_, v___x_4899_);
lean_dec_ref(v_alts_4882_);
v_seq_4888_ = v___x_4900_;
goto v___jp_4887_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4922_, lean_object* v_alts_4923_, lean_object* v_compress_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
uint8_t v_compress_boxed_4928_; lean_object* v_res_4929_; 
v_compress_boxed_4928_ = lean_unbox(v_compress_4924_);
v_res_4929_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4922_, v_alts_4923_, v_compress_boxed_4928_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4930_, lean_object* v_x_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4930_, v_x_4931_, v___y_4932_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4936_, lean_object* v_x_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4936_, v_x_4937_, v___y_4938_, v___y_4939_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v___x_4945_; lean_object* v_env_4946_; uint8_t v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4945_ = lean_st_ref_get(v___y_4943_);
v_env_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc_ref(v_env_4946_);
lean_dec(v___x_4945_);
v___x_4947_ = l_Lean_Meta_isMatcherAppCore(v_env_4946_, v_e_4942_);
v___x_4948_ = lean_box(v___x_4947_);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4950_, v___y_4951_);
lean_dec(v___y_4951_);
lean_dec_ref(v_e_4950_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4954_, v___y_4964_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec(v___y_4969_);
lean_dec(v___y_4968_);
lean_dec_ref(v_e_4967_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v___x_4991_; 
lean_inc(v___y_4985_);
lean_inc_ref(v___y_4984_);
lean_inc(v___y_4983_);
lean_inc_ref(v___y_4982_);
lean_inc(v___y_4981_);
v___x_4991_ = lean_apply_10(v_x_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, lean_box(0));
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_5004_, lean_object* v_x_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v___f_5016_; lean_object* v___x_5017_; 
lean_inc(v___y_5010_);
lean_inc_ref(v___y_5009_);
lean_inc(v___y_5008_);
lean_inc_ref(v___y_5007_);
lean_inc(v___y_5006_);
v___f_5016_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5016_, 0, v_x_5005_);
lean_closure_set(v___f_5016_, 1, v___y_5006_);
lean_closure_set(v___f_5016_, 2, v___y_5007_);
lean_closure_set(v___f_5016_, 3, v___y_5008_);
lean_closure_set(v___f_5016_, 4, v___y_5009_);
lean_closure_set(v___f_5016_, 5, v___y_5010_);
v___x_5017_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5004_, v___f_5016_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
if (lean_obj_tag(v___x_5017_) == 0)
{
return v___x_5017_;
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5026_, lean_object* v_x_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5026_, v_x_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5039_, lean_object* v_mvarId_5040_, lean_object* v_x_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5040_, v_x_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5053_, lean_object* v_mvarId_5054_, lean_object* v_x_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5053_, v_mvarId_5054_, v_x_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5067_, lean_object* v___y_5068_){
_start:
{
uint8_t v___x_5070_; 
v___x_5070_ = l_Lean_Expr_hasMVar(v_e_5067_);
if (v___x_5070_ == 0)
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v_e_5067_);
return v___x_5071_;
}
else
{
lean_object* v___x_5072_; lean_object* v_mctx_5073_; lean_object* v___x_5074_; lean_object* v_fst_5075_; lean_object* v_snd_5076_; lean_object* v___x_5077_; lean_object* v_cache_5078_; lean_object* v_zetaDeltaFVarIds_5079_; lean_object* v_postponed_5080_; lean_object* v_diag_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5090_; 
v___x_5072_ = lean_st_ref_get(v___y_5068_);
v_mctx_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc_ref(v_mctx_5073_);
lean_dec(v___x_5072_);
v___x_5074_ = l_Lean_instantiateMVarsCore(v_mctx_5073_, v_e_5067_);
v_fst_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_fst_5075_);
v_snd_5076_ = lean_ctor_get(v___x_5074_, 1);
lean_inc(v_snd_5076_);
lean_dec_ref(v___x_5074_);
v___x_5077_ = lean_st_ref_take(v___y_5068_);
v_cache_5078_ = lean_ctor_get(v___x_5077_, 1);
v_zetaDeltaFVarIds_5079_ = lean_ctor_get(v___x_5077_, 2);
v_postponed_5080_ = lean_ctor_get(v___x_5077_, 3);
v_diag_5081_ = lean_ctor_get(v___x_5077_, 4);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5090_ == 0)
{
lean_object* v_unused_5091_; 
v_unused_5091_ = lean_ctor_get(v___x_5077_, 0);
lean_dec(v_unused_5091_);
v___x_5083_ = v___x_5077_;
v_isShared_5084_ = v_isSharedCheck_5090_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_diag_5081_);
lean_inc(v_postponed_5080_);
lean_inc(v_zetaDeltaFVarIds_5079_);
lean_inc(v_cache_5078_);
lean_dec(v___x_5077_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5090_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 0, v_snd_5076_);
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_snd_5076_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v_cache_5078_);
lean_ctor_set(v_reuseFailAlloc_5089_, 2, v_zetaDeltaFVarIds_5079_);
lean_ctor_set(v_reuseFailAlloc_5089_, 3, v_postponed_5080_);
lean_ctor_set(v_reuseFailAlloc_5089_, 4, v_diag_5081_);
v___x_5086_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = lean_st_ref_put(v___y_5068_, v___x_5086_);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_fst_5075_);
return v___x_5088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5092_, v___y_5093_);
lean_dec(v___y_5093_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5096_, v___y_5103_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___y_5109_);
return v_res_5119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5121_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5122_ = l_Lean_stringToMessageData(v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5123_, lean_object* v_c_5124_, lean_object* v_a_5125_, lean_object* v_numCases_5126_, uint8_t v_isRec_5127_, lean_object* v_anchorInfo_x3f_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v_mvarIds_5141_; lean_object* v___x_5191_; 
v___x_5191_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5123_, v___y_5129_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v___y_5194_; lean_object* v___x_5246_; uint8_t v___x_5249_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
lean_inc(v_a_5192_);
lean_dec_ref_known(v___x_5191_, 1);
v___x_5246_ = lean_unsigned_to_nat(1u);
v___x_5249_ = lean_nat_dec_lt(v___x_5246_, v_numCases_5126_);
if (v___x_5249_ == 0)
{
if (v_isRec_5127_ == 0)
{
lean_inc(v_a_5192_);
v___y_5194_ = v_a_5192_;
goto v___jp_5193_;
}
else
{
goto v___jp_5247_;
}
}
else
{
goto v___jp_5247_;
}
v___jp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5195_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5124_);
lean_inc_ref(v___x_5123_);
v___x_5196_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5123_, v___y_5194_, v_numCases_5126_, v___x_5195_, v___y_5132_, v___y_5135_, v___y_5137_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v___x_5197_; 
lean_dec_ref_known(v___x_5196_, 1);
lean_inc_ref(v___x_5123_);
v___x_5197_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5123_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_toCold_5198_; lean_object* v_options_5199_; uint8_t v_hasTrace_5200_; 
lean_dec_ref_known(v___x_5197_, 1);
v_toCold_5198_ = lean_ctor_get(v___y_5137_, 0);
v_options_5199_ = lean_ctor_get(v_toCold_5198_, 2);
v_hasTrace_5200_ = lean_ctor_get_uint8(v_options_5199_, sizeof(void*)*1);
if (v_hasTrace_5200_ == 0)
{
lean_dec(v_a_5192_);
goto v___jp_5144_;
}
else
{
lean_object* v_inheritedTraceOptions_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; 
v_inheritedTraceOptions_5201_ = lean_ctor_get(v_toCold_5198_, 11);
v___x_5202_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5203_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5204_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5201_, v_options_5199_, v___x_5203_);
if (v___x_5204_ == 0)
{
lean_dec(v_a_5192_);
goto v___jp_5144_;
}
else
{
lean_object* v___x_5205_; 
v___x_5205_ = l_Lean_Meta_Grind_updateLastTag(v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
lean_dec_ref_known(v___x_5205_, 1);
lean_inc_ref(v___x_5123_);
v___x_5206_ = l_Lean_MessageData_ofExpr(v___x_5123_);
v___x_5207_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5206_);
lean_ctor_set(v___x_5208_, 1, v___x_5207_);
v___x_5209_ = l_Nat_reprFast(v_a_5192_);
v___x_5210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
v___x_5211_ = l_Lean_MessageData_ofFormat(v___x_5210_);
v___x_5212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5208_);
lean_ctor_set(v___x_5212_, 1, v___x_5211_);
v___x_5213_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5202_, v___x_5212_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_dec_ref_known(v___x_5213_, 1);
goto v___jp_5144_;
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_a_5125_);
lean_dec_ref(v_c_5124_);
lean_dec_ref(v___x_5123_);
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5213_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5213_);
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
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_a_5125_);
lean_dec_ref(v_c_5124_);
lean_dec_ref(v___x_5123_);
v_a_5222_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5205_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5205_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_a_5125_);
lean_dec_ref(v_c_5124_);
lean_dec_ref(v___x_5123_);
v_a_5230_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5197_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5197_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec(v_a_5192_);
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_a_5125_);
lean_dec_ref(v_c_5124_);
lean_dec_ref(v___x_5123_);
v_a_5238_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5196_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5196_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
v___jp_5247_:
{
lean_object* v___x_5248_; 
v___x_5248_ = lean_nat_add(v_a_5192_, v___x_5246_);
v___y_5194_ = v___x_5248_;
goto v___jp_5193_;
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_numCases_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_c_5124_);
lean_dec_ref(v___x_5123_);
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
v___jp_5140_:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5142_, 0, v_mvarIds_5141_);
lean_ctor_set(v___x_5142_, 1, v_anchorInfo_x3f_5128_);
v___x_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5142_);
return v___x_5143_;
}
v___jp_5144_:
{
lean_object* v___x_5145_; 
v___x_5145_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5123_, v___y_5138_);
if (lean_obj_tag(v_c_5124_) == 1)
{
lean_object* v_e_5146_; lean_object* v_binderType_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
lean_dec_ref(v___x_5145_);
lean_dec_ref(v___x_5123_);
v_e_5146_ = lean_ctor_get(v_c_5124_, 0);
lean_inc_ref(v_e_5146_);
lean_dec_ref_known(v_c_5124_, 2);
v_binderType_5147_ = lean_ctor_get(v_e_5146_, 1);
lean_inc_ref(v_binderType_5147_);
lean_dec_ref(v_e_5146_);
v___x_5148_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5147_);
v___x_5149_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5125_, v___x_5148_, v___y_5131_, v___y_5132_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v_mvarIds_5141_ = v_a_5150_;
goto v___jp_5140_;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_anchorInfo_x3f_5128_);
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
lean_dec_ref(v_c_5124_);
v_a_5159_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5145_);
v___x_5160_ = lean_unbox(v_a_5159_);
lean_dec(v_a_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; 
v___x_5161_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5123_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v___x_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5163_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5125_, v_a_5162_, v___y_5131_, v___y_5132_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc(v_a_5164_);
lean_dec_ref_known(v___x_5163_, 1);
v_mvarIds_5141_ = v_a_5164_;
goto v___jp_5140_;
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec(v_anchorInfo_x3f_5128_);
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
lean_dec(v_anchorInfo_x3f_5128_);
lean_dec(v_a_5125_);
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
v___x_5181_ = l_Lean_Meta_Grind_casesMatch(v_a_5125_, v___x_5123_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5181_, 1);
v_mvarIds_5141_ = v_a_5182_;
goto v___jp_5140_;
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v_anchorInfo_x3f_5128_);
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
v___x_5379_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* v_ks_5431_; lean_object* v_vs_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5450_; 
v_ks_5431_ = lean_ctor_get(v_x_5380_, 0);
v_vs_5432_ = lean_ctor_get(v_x_5380_, 1);
v_isSharedCheck_5450_ = !lean_is_exclusive(v_x_5380_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5434_ = v_x_5380_;
v_isShared_5435_ = v_isSharedCheck_5450_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_vs_5432_);
lean_inc(v_ks_5431_);
lean_dec(v_x_5380_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5450_;
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
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_ks_5431_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_vs_5432_);
v___x_5437_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v_newNode_5438_; size_t v___x_5439_; uint8_t v___x_5440_; 
v_newNode_5438_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5437_, v_x_5383_, v_x_5384_);
v___x_5439_ = ((size_t)7ULL);
v___x_5440_ = lean_usize_dec_le(v___x_5439_, v_x_5382_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5441_; lean_object* v___x_5442_; uint8_t v___x_5443_; 
v___x_5441_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5438_);
v___x_5442_ = lean_unsigned_to_nat(4u);
v___x_5443_ = lean_nat_dec_lt(v___x_5441_, v___x_5442_);
lean_dec(v___x_5441_);
if (v___x_5443_ == 0)
{
lean_object* v_ks_5444_; lean_object* v_vs_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v_ks_5444_ = lean_ctor_get(v_newNode_5438_, 0);
lean_inc_ref(v_ks_5444_);
v_vs_5445_ = lean_ctor_get(v_newNode_5438_, 1);
lean_inc_ref(v_vs_5445_);
lean_dec_ref(v_newNode_5438_);
v___x_5446_ = lean_unsigned_to_nat(0u);
v___x_5447_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5448_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5382_, v_ks_5444_, v_vs_5445_, v___x_5446_, v___x_5447_);
lean_dec_ref(v_vs_5445_);
lean_dec_ref(v_ks_5444_);
return v___x_5448_;
}
else
{
return v_newNode_5438_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5451_, lean_object* v_keys_5452_, lean_object* v_vals_5453_, lean_object* v_i_5454_, lean_object* v_entries_5455_){
_start:
{
lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5456_ = lean_array_get_size(v_keys_5452_);
v___x_5457_ = lean_nat_dec_lt(v_i_5454_, v___x_5456_);
if (v___x_5457_ == 0)
{
lean_dec(v_i_5454_);
return v_entries_5455_;
}
else
{
lean_object* v_k_5458_; lean_object* v_v_5459_; uint64_t v___x_5460_; size_t v_h_5461_; size_t v___x_5462_; lean_object* v___x_5463_; size_t v___x_5464_; size_t v___x_5465_; size_t v___x_5466_; size_t v_h_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v_k_5458_ = lean_array_fget_borrowed(v_keys_5452_, v_i_5454_);
v_v_5459_ = lean_array_fget_borrowed(v_vals_5453_, v_i_5454_);
v___x_5460_ = l_Lean_instHashableMVarId_hash(v_k_5458_);
v_h_5461_ = lean_uint64_to_usize(v___x_5460_);
v___x_5462_ = ((size_t)5ULL);
v___x_5463_ = lean_unsigned_to_nat(1u);
v___x_5464_ = ((size_t)1ULL);
v___x_5465_ = lean_usize_sub(v_depth_5451_, v___x_5464_);
v___x_5466_ = lean_usize_mul(v___x_5462_, v___x_5465_);
v_h_5467_ = lean_usize_shift_right(v_h_5461_, v___x_5466_);
v___x_5468_ = lean_nat_add(v_i_5454_, v___x_5463_);
lean_dec(v_i_5454_);
lean_inc(v_v_5459_);
lean_inc(v_k_5458_);
v___x_5469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5455_, v_h_5467_, v_depth_5451_, v_k_5458_, v_v_5459_);
v_i_5454_ = v___x_5468_;
v_entries_5455_ = v___x_5469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5471_, lean_object* v_keys_5472_, lean_object* v_vals_5473_, lean_object* v_i_5474_, lean_object* v_entries_5475_){
_start:
{
size_t v_depth_boxed_5476_; lean_object* v_res_5477_; 
v_depth_boxed_5476_ = lean_unbox_usize(v_depth_5471_);
lean_dec(v_depth_5471_);
v_res_5477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5476_, v_keys_5472_, v_vals_5473_, v_i_5474_, v_entries_5475_);
lean_dec_ref(v_vals_5473_);
lean_dec_ref(v_keys_5472_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5478_, lean_object* v_x_5479_, lean_object* v_x_5480_, lean_object* v_x_5481_, lean_object* v_x_5482_){
_start:
{
size_t v_x_66986__boxed_5483_; size_t v_x_66987__boxed_5484_; lean_object* v_res_5485_; 
v_x_66986__boxed_5483_ = lean_unbox_usize(v_x_5479_);
lean_dec(v_x_5479_);
v_x_66987__boxed_5484_ = lean_unbox_usize(v_x_5480_);
lean_dec(v_x_5480_);
v_res_5485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5478_, v_x_66986__boxed_5483_, v_x_66987__boxed_5484_, v_x_5481_, v_x_5482_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5486_, lean_object* v_x_5487_, lean_object* v_x_5488_){
_start:
{
uint64_t v___x_5489_; size_t v___x_5490_; size_t v___x_5491_; lean_object* v___x_5492_; 
v___x_5489_ = l_Lean_instHashableMVarId_hash(v_x_5487_);
v___x_5490_ = lean_uint64_to_usize(v___x_5489_);
v___x_5491_ = ((size_t)1ULL);
v___x_5492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5486_, v___x_5490_, v___x_5491_, v_x_5487_, v_x_5488_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5493_, lean_object* v_val_5494_, lean_object* v___y_5495_){
_start:
{
lean_object* v___x_5497_; lean_object* v_mctx_5498_; lean_object* v_cache_5499_; lean_object* v_zetaDeltaFVarIds_5500_; lean_object* v_postponed_5501_; lean_object* v_diag_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5532_; 
v___x_5497_ = lean_st_ref_take(v___y_5495_);
v_mctx_5498_ = lean_ctor_get(v___x_5497_, 0);
v_cache_5499_ = lean_ctor_get(v___x_5497_, 1);
v_zetaDeltaFVarIds_5500_ = lean_ctor_get(v___x_5497_, 2);
v_postponed_5501_ = lean_ctor_get(v___x_5497_, 3);
v_diag_5502_ = lean_ctor_get(v___x_5497_, 4);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5504_ = v___x_5497_;
v_isShared_5505_ = v_isSharedCheck_5532_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_diag_5502_);
lean_inc(v_postponed_5501_);
lean_inc(v_zetaDeltaFVarIds_5500_);
lean_inc(v_cache_5499_);
lean_inc(v_mctx_5498_);
lean_dec(v___x_5497_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5532_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v_depth_5506_; lean_object* v_levelAssignDepth_5507_; lean_object* v_lmvarCounter_5508_; lean_object* v_mvarCounter_5509_; lean_object* v_lDecls_5510_; lean_object* v_decls_5511_; lean_object* v_userNames_5512_; lean_object* v_lAssignment_5513_; lean_object* v_eAssignment_5514_; lean_object* v_dAssignment_5515_; lean_object* v_instanceTypedMVars_5516_; lean_object* v_synthNormMemo_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5531_; 
v_depth_5506_ = lean_ctor_get(v_mctx_5498_, 0);
v_levelAssignDepth_5507_ = lean_ctor_get(v_mctx_5498_, 1);
v_lmvarCounter_5508_ = lean_ctor_get(v_mctx_5498_, 2);
v_mvarCounter_5509_ = lean_ctor_get(v_mctx_5498_, 3);
v_lDecls_5510_ = lean_ctor_get(v_mctx_5498_, 4);
v_decls_5511_ = lean_ctor_get(v_mctx_5498_, 5);
v_userNames_5512_ = lean_ctor_get(v_mctx_5498_, 6);
v_lAssignment_5513_ = lean_ctor_get(v_mctx_5498_, 7);
v_eAssignment_5514_ = lean_ctor_get(v_mctx_5498_, 8);
v_dAssignment_5515_ = lean_ctor_get(v_mctx_5498_, 9);
v_instanceTypedMVars_5516_ = lean_ctor_get(v_mctx_5498_, 10);
v_synthNormMemo_5517_ = lean_ctor_get(v_mctx_5498_, 11);
v_isSharedCheck_5531_ = !lean_is_exclusive(v_mctx_5498_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5519_ = v_mctx_5498_;
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_synthNormMemo_5517_);
lean_inc(v_instanceTypedMVars_5516_);
lean_inc(v_dAssignment_5515_);
lean_inc(v_eAssignment_5514_);
lean_inc(v_lAssignment_5513_);
lean_inc(v_userNames_5512_);
lean_inc(v_decls_5511_);
lean_inc(v_lDecls_5510_);
lean_inc(v_mvarCounter_5509_);
lean_inc(v_lmvarCounter_5508_);
lean_inc(v_levelAssignDepth_5507_);
lean_inc(v_depth_5506_);
lean_dec(v_mctx_5498_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5531_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5524_; 
v___x_5521_ = lean_box(0);
v___x_5522_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5514_, v_mvarId_5493_, v_val_5494_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 8, v___x_5522_);
v___x_5524_ = v___x_5519_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_depth_5506_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_levelAssignDepth_5507_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_lmvarCounter_5508_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_mvarCounter_5509_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_lDecls_5510_);
lean_ctor_set(v_reuseFailAlloc_5530_, 5, v_decls_5511_);
lean_ctor_set(v_reuseFailAlloc_5530_, 6, v_userNames_5512_);
lean_ctor_set(v_reuseFailAlloc_5530_, 7, v_lAssignment_5513_);
lean_ctor_set(v_reuseFailAlloc_5530_, 8, v___x_5522_);
lean_ctor_set(v_reuseFailAlloc_5530_, 9, v_dAssignment_5515_);
lean_ctor_set(v_reuseFailAlloc_5530_, 10, v_instanceTypedMVars_5516_);
lean_ctor_set(v_reuseFailAlloc_5530_, 11, v_synthNormMemo_5517_);
v___x_5524_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
lean_object* v___x_5526_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 0, v___x_5524_);
v___x_5526_ = v___x_5504_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_cache_5499_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_zetaDeltaFVarIds_5500_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v_postponed_5501_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_diag_5502_);
v___x_5526_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; 
v___x_5527_ = lean_st_ref_put(v___y_5495_, v___x_5526_);
v___x_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5521_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5538_, lean_object* v_snd_5539_, uint8_t v_stopAtFirstFailure_5540_, lean_object* v_as_x27_5541_, lean_object* v_b_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
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
lean_object* v_snd_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5660_; 
v_snd_5554_ = lean_ctor_get(v_b_5542_, 1);
v_isSharedCheck_5660_ = !lean_is_exclusive(v_b_5542_);
if (v_isSharedCheck_5660_ == 0)
{
lean_object* v_unused_5661_; 
v_unused_5661_ = lean_ctor_get(v_b_5542_, 0);
lean_dec(v_unused_5661_);
v___x_5556_ = v_b_5542_;
v_isShared_5557_ = v_isSharedCheck_5660_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_snd_5554_);
lean_dec(v_b_5542_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5660_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v_head_5558_; lean_object* v_tail_5559_; lean_object* v_fst_5560_; lean_object* v_snd_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5659_; 
v_head_5558_ = lean_ctor_get(v_as_x27_5541_, 0);
v_tail_5559_ = lean_ctor_get(v_as_x27_5541_, 1);
v_fst_5560_ = lean_ctor_get(v_snd_5554_, 0);
v_snd_5561_ = lean_ctor_get(v_snd_5554_, 1);
v_isSharedCheck_5659_ = !lean_is_exclusive(v_snd_5554_);
if (v_isSharedCheck_5659_ == 0)
{
v___x_5563_ = v_snd_5554_;
v_isShared_5564_ = v_isSharedCheck_5659_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_snd_5561_);
lean_inc(v_fst_5560_);
lean_dec(v_snd_5554_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5659_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5565_ = lean_box(0);
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
lean_inc(v_head_5558_);
v___x_5566_ = lean_apply_11(v_kp_5538_, v_head_5558_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, lean_box(0));
if (lean_obj_tag(v___x_5566_) == 0)
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5650_; 
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5569_ = v___x_5566_;
v_isShared_5570_ = v_isSharedCheck_5650_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5566_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5650_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
if (lean_obj_tag(v_a_5567_) == 0)
{
lean_object* v_seq_5571_; lean_object* v_mvarId_5572_; lean_object* v___x_5573_; 
lean_del_object(v___x_5569_);
v_seq_5571_ = lean_ctor_get(v_a_5567_, 0);
v_mvarId_5572_ = lean_ctor_get(v_head_5558_, 1);
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
lean_ctor_set(v___x_5577_, 0, v_a_5567_);
v___x_5585_ = v___x_5577_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5567_);
v___x_5585_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5587_; 
if (v_isShared_5564_ == 0)
{
v___x_5587_ = v___x_5563_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_fst_5560_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_snd_5561_);
v___x_5587_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5589_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5587_);
lean_ctor_set(v___x_5556_, 0, v___x_5585_);
v___x_5589_ = v___x_5556_;
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
lean_dec_ref_known(v_a_5567_, 1);
lean_del_object(v___x_5563_);
lean_dec(v_snd_5561_);
lean_dec(v_fst_5560_);
lean_del_object(v___x_5556_);
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
uint8_t v___x_5607_; 
lean_inc(v_seq_5571_);
lean_dec(v_a_5574_);
lean_dec_ref_known(v_a_5567_, 1);
v___x_5607_ = l_List_isEmpty___redArg(v_seq_5571_);
if (v___x_5607_ == 0)
{
lean_object* v___x_5608_; lean_object* v___x_5610_; 
v___x_5608_ = lean_array_push(v_fst_5560_, v_seq_5571_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5608_);
v___x_5610_ = v___x_5563_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5608_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_snd_5561_);
v___x_5610_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
lean_object* v___x_5612_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5610_);
lean_ctor_set(v___x_5556_, 0, v___x_5565_);
v___x_5612_ = v___x_5556_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v___x_5610_);
v___x_5612_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
v_as_x27_5541_ = v_tail_5559_;
v_b_5542_ = v___x_5612_;
goto _start;
}
}
}
else
{
lean_object* v___x_5617_; 
lean_dec(v_seq_5571_);
if (v_isShared_5564_ == 0)
{
v___x_5617_ = v___x_5563_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_fst_5560_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_snd_5561_);
v___x_5617_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
lean_object* v___x_5619_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5617_);
lean_ctor_set(v___x_5556_, 0, v___x_5565_);
v___x_5619_ = v___x_5556_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v___x_5617_);
v___x_5619_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
v_as_x27_5541_ = v_tail_5559_;
v_b_5542_ = v___x_5619_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
lean_dec_ref_known(v_a_5567_, 1);
lean_del_object(v___x_5563_);
lean_dec(v_snd_5561_);
lean_dec(v_fst_5560_);
lean_del_object(v___x_5556_);
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v_a_5623_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5625_ = v___x_5573_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5573_);
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
else
{
if (v_stopAtFirstFailure_5540_ == 0)
{
lean_object* v_gs_5631_; lean_object* v___x_5632_; lean_object* v___x_5634_; 
lean_del_object(v___x_5569_);
v_gs_5631_ = lean_ctor_get(v_a_5567_, 0);
lean_inc(v_gs_5631_);
lean_dec_ref_known(v_a_5567_, 1);
v___x_5632_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5561_, v_gs_5631_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 1, v___x_5632_);
v___x_5634_ = v___x_5563_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_fst_5560_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5632_);
v___x_5634_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5636_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5634_);
lean_ctor_set(v___x_5556_, 0, v___x_5565_);
v___x_5636_ = v___x_5556_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v___x_5634_);
v___x_5636_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
v_as_x27_5541_ = v_tail_5559_;
v_b_5542_ = v___x_5636_;
goto _start;
}
}
}
else
{
lean_object* v___x_5640_; lean_object* v___x_5642_; 
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v___x_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5640_, 0, v_a_5567_);
if (v_isShared_5564_ == 0)
{
v___x_5642_ = v___x_5563_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_fst_5560_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_snd_5561_);
v___x_5642_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5644_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 1, v___x_5642_);
lean_ctor_set(v___x_5556_, 0, v___x_5640_);
v___x_5644_ = v___x_5556_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5640_);
lean_ctor_set(v_reuseFailAlloc_5648_, 1, v___x_5642_);
v___x_5644_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5646_; 
if (v_isShared_5570_ == 0)
{
lean_ctor_set(v___x_5569_, 0, v___x_5644_);
v___x_5646_ = v___x_5569_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5644_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_del_object(v___x_5563_);
lean_dec(v_snd_5561_);
lean_dec(v_fst_5560_);
lean_del_object(v___x_5556_);
lean_dec_ref(v_snd_5539_);
lean_dec_ref(v_kp_5538_);
v_a_5651_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5566_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5566_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5662_, lean_object* v_snd_5663_, lean_object* v_stopAtFirstFailure_5664_, lean_object* v_as_x27_5665_, lean_object* v_b_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5677_; lean_object* v_res_5678_; 
v_stopAtFirstFailure_boxed_5677_ = lean_unbox(v_stopAtFirstFailure_5664_);
v_res_5678_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5662_, v_snd_5663_, v_stopAtFirstFailure_boxed_5677_, v_as_x27_5665_, v_b_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
lean_dec(v___y_5669_);
lean_dec_ref(v___y_5668_);
lean_dec(v___y_5667_);
lean_dec(v_as_x27_5665_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5679_, lean_object* v_c_5680_, lean_object* v___x_5681_, lean_object* v___x_5682_, uint8_t v_isRec_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_){
_start:
{
if (lean_obj_tag(v_a_5684_) == 0)
{
lean_object* v___x_5686_; 
lean_dec(v___x_5682_);
lean_dec_ref(v___x_5681_);
lean_dec_ref(v_snd_5679_);
v___x_5686_ = lean_array_to_list(v_a_5685_);
return v___x_5686_;
}
else
{
lean_object* v_toGoalState_5687_; lean_object* v_split_5688_; lean_object* v_head_5689_; lean_object* v_tail_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5751_; 
v_toGoalState_5687_ = lean_ctor_get(v_snd_5679_, 0);
lean_inc_ref(v_toGoalState_5687_);
v_split_5688_ = lean_ctor_get(v_toGoalState_5687_, 15);
lean_inc_ref(v_split_5688_);
v_head_5689_ = lean_ctor_get(v_a_5684_, 0);
v_tail_5690_ = lean_ctor_get(v_a_5684_, 1);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_a_5684_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5692_ = v_a_5684_;
v_isShared_5693_ = v_isSharedCheck_5751_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_tail_5690_);
lean_inc(v_head_5689_);
lean_dec(v_a_5684_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5751_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v_nextDeclIdx_5694_; lean_object* v_enodeMap_5695_; lean_object* v_exprs_5696_; lean_object* v_parents_5697_; lean_object* v_congrTable_5698_; lean_object* v_appMap_5699_; lean_object* v_indicesFound_5700_; lean_object* v_toProcess_5701_; lean_object* v_internalizing_5702_; uint8_t v_inconsistent_5703_; lean_object* v_nextIdx_5704_; lean_object* v_newRawFacts_5705_; lean_object* v_facts_5706_; lean_object* v_extThms_5707_; lean_object* v_ematch_5708_; lean_object* v_inj_5709_; lean_object* v_clean_5710_; lean_object* v_sstates_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5749_; 
v_nextDeclIdx_5694_ = lean_ctor_get(v_toGoalState_5687_, 0);
v_enodeMap_5695_ = lean_ctor_get(v_toGoalState_5687_, 1);
v_exprs_5696_ = lean_ctor_get(v_toGoalState_5687_, 2);
v_parents_5697_ = lean_ctor_get(v_toGoalState_5687_, 3);
v_congrTable_5698_ = lean_ctor_get(v_toGoalState_5687_, 4);
v_appMap_5699_ = lean_ctor_get(v_toGoalState_5687_, 5);
v_indicesFound_5700_ = lean_ctor_get(v_toGoalState_5687_, 6);
v_toProcess_5701_ = lean_ctor_get(v_toGoalState_5687_, 7);
v_internalizing_5702_ = lean_ctor_get(v_toGoalState_5687_, 8);
v_inconsistent_5703_ = lean_ctor_get_uint8(v_toGoalState_5687_, sizeof(void*)*18);
v_nextIdx_5704_ = lean_ctor_get(v_toGoalState_5687_, 9);
v_newRawFacts_5705_ = lean_ctor_get(v_toGoalState_5687_, 10);
v_facts_5706_ = lean_ctor_get(v_toGoalState_5687_, 11);
v_extThms_5707_ = lean_ctor_get(v_toGoalState_5687_, 12);
v_ematch_5708_ = lean_ctor_get(v_toGoalState_5687_, 13);
v_inj_5709_ = lean_ctor_get(v_toGoalState_5687_, 14);
v_clean_5710_ = lean_ctor_get(v_toGoalState_5687_, 16);
v_sstates_5711_ = lean_ctor_get(v_toGoalState_5687_, 17);
v_isSharedCheck_5749_ = !lean_is_exclusive(v_toGoalState_5687_);
if (v_isSharedCheck_5749_ == 0)
{
lean_object* v_unused_5750_; 
v_unused_5750_ = lean_ctor_get(v_toGoalState_5687_, 15);
lean_dec(v_unused_5750_);
v___x_5713_ = v_toGoalState_5687_;
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
lean_inc(v_internalizing_5702_);
lean_inc(v_toProcess_5701_);
lean_inc(v_indicesFound_5700_);
lean_inc(v_appMap_5699_);
lean_inc(v_congrTable_5698_);
lean_inc(v_parents_5697_);
lean_inc(v_exprs_5696_);
lean_inc(v_enodeMap_5695_);
lean_inc(v_nextDeclIdx_5694_);
lean_dec(v_toGoalState_5687_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5749_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v_num_5715_; lean_object* v_candidates_5716_; lean_object* v_added_5717_; lean_object* v_resolved_5718_; lean_object* v_trace_5719_; lean_object* v_lookaheads_5720_; lean_object* v_argPosMap_5721_; lean_object* v_argsAt_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5748_; 
v_num_5715_ = lean_ctor_get(v_split_5688_, 0);
v_candidates_5716_ = lean_ctor_get(v_split_5688_, 1);
v_added_5717_ = lean_ctor_get(v_split_5688_, 2);
v_resolved_5718_ = lean_ctor_get(v_split_5688_, 3);
v_trace_5719_ = lean_ctor_get(v_split_5688_, 4);
v_lookaheads_5720_ = lean_ctor_get(v_split_5688_, 5);
v_argPosMap_5721_ = lean_ctor_get(v_split_5688_, 6);
v_argsAt_5722_ = lean_ctor_get(v_split_5688_, 7);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_split_5688_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5724_ = v_split_5688_;
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
lean_dec(v_split_5688_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5748_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5726_; lean_object* v___y_5728_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5726_ = lean_array_get_size(v_a_5685_);
v___x_5746_ = lean_unsigned_to_nat(0u);
v___x_5747_ = lean_nat_dec_lt(v___x_5746_, v___x_5726_);
if (v___x_5747_ == 0)
{
if (v_isRec_5683_ == 0)
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
v___x_5729_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5680_);
lean_inc(v___x_5682_);
lean_inc_ref(v___x_5681_);
v___x_5730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5681_);
lean_ctor_set(v___x_5730_, 1, v___x_5726_);
lean_ctor_set(v___x_5730_, 2, v___x_5682_);
lean_ctor_set(v___x_5730_, 3, v___x_5729_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 1, v_trace_5719_);
lean_ctor_set(v___x_5692_, 0, v___x_5730_);
v___x_5732_ = v___x_5692_;
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
lean_ctor_set(v___x_5713_, 15, v___x_5734_);
v___x_5736_ = v___x_5713_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_nextDeclIdx_5694_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_enodeMap_5695_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_exprs_5696_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v_parents_5697_);
lean_ctor_set(v_reuseFailAlloc_5740_, 4, v_congrTable_5698_);
lean_ctor_set(v_reuseFailAlloc_5740_, 5, v_appMap_5699_);
lean_ctor_set(v_reuseFailAlloc_5740_, 6, v_indicesFound_5700_);
lean_ctor_set(v_reuseFailAlloc_5740_, 7, v_toProcess_5701_);
lean_ctor_set(v_reuseFailAlloc_5740_, 8, v_internalizing_5702_);
lean_ctor_set(v_reuseFailAlloc_5740_, 9, v_nextIdx_5704_);
lean_ctor_set(v_reuseFailAlloc_5740_, 10, v_newRawFacts_5705_);
lean_ctor_set(v_reuseFailAlloc_5740_, 11, v_facts_5706_);
lean_ctor_set(v_reuseFailAlloc_5740_, 12, v_extThms_5707_);
lean_ctor_set(v_reuseFailAlloc_5740_, 13, v_ematch_5708_);
lean_ctor_set(v_reuseFailAlloc_5740_, 14, v_inj_5709_);
lean_ctor_set(v_reuseFailAlloc_5740_, 15, v___x_5734_);
lean_ctor_set(v_reuseFailAlloc_5740_, 16, v_clean_5710_);
lean_ctor_set(v_reuseFailAlloc_5740_, 17, v_sstates_5711_);
lean_ctor_set_uint8(v_reuseFailAlloc_5740_, sizeof(void*)*18, v_inconsistent_5703_);
v___x_5736_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; 
v___x_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v_head_5689_);
v___x_5738_ = lean_array_push(v_a_5685_, v___x_5737_);
v_a_5684_ = v_tail_5690_;
v_a_5685_ = v___x_5738_;
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
lean_object* v_a_5794_; uint8_t v_trace_5795_; lean_object* v___x_5796_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc(v_a_5794_);
lean_dec_ref_known(v___x_5793_, 1);
v_trace_5795_ = lean_ctor_get_uint8(v_a_5794_, sizeof(void*)*14);
lean_dec(v_a_5794_);
lean_inc_ref(v_goal_5781_);
v___x_5796_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5781_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5796_) == 0)
{
lean_object* v_a_5797_; lean_object* v_mvarId_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___f_5801_; lean_object* v___x_5802_; lean_object* v___f_5803_; lean_object* v___x_5804_; 
v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
lean_inc_n(v_a_5797_, 2);
lean_dec_ref_known(v___x_5796_, 1);
v_mvarId_5798_ = lean_ctor_get(v_goal_5781_, 1);
lean_inc(v_mvarId_5798_);
v___x_5799_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5775_);
v___x_5800_ = lean_box(v_isRec_5777_);
lean_inc_ref_n(v_c_5775_, 2);
lean_inc_ref(v___x_5799_);
v___f_5801_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5801_, 0, v___x_5799_);
lean_closure_set(v___f_5801_, 1, v_c_5775_);
lean_closure_set(v___f_5801_, 2, v_a_5797_);
lean_closure_set(v___f_5801_, 3, v_numCases_5776_);
lean_closure_set(v___f_5801_, 4, v___x_5800_);
v___x_5802_ = lean_box(v_trace_5795_);
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
lean_object* v_a_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5899_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5818_ = v___x_5815_;
v_isShared_5819_ = v_isSharedCheck_5899_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_a_5816_);
lean_dec(v___x_5815_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5899_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v_fst_5820_; 
v_fst_5820_ = lean_ctor_get(v_a_5816_, 0);
if (lean_obj_tag(v_fst_5820_) == 0)
{
lean_object* v_snd_5821_; lean_object* v_fst_5822_; lean_object* v_snd_5823_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v_mvarId_5873_; lean_object* v___x_5874_; 
v_snd_5821_ = lean_ctor_get(v_a_5816_, 1);
lean_inc(v_snd_5821_);
lean_dec(v_a_5816_);
v_fst_5822_ = lean_ctor_get(v_snd_5821_, 0);
lean_inc(v_fst_5822_);
v_snd_5823_ = lean_ctor_get(v_snd_5821_, 1);
lean_inc(v_snd_5823_);
lean_dec(v_snd_5821_);
v_mvarId_5873_ = lean_ctor_get(v_snd_5807_, 1);
lean_inc_n(v_mvarId_5873_, 2);
lean_dec(v_snd_5807_);
v___x_5874_ = l_Lean_MVarId_getType(v_mvarId_5873_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; uint8_t v___x_5876_; 
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref_known(v___x_5874_, 1);
v___x_5876_ = l_Lean_Expr_isFalse(v_a_5875_);
if (v___x_5876_ == 0)
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v_a_5879_; lean_object* v___x_5880_; 
v___x_5877_ = l_Lean_mkMVar(v_a_5797_);
v___x_5878_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5877_, v_a_5789_);
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5879_);
lean_dec_ref(v___x_5878_);
v___x_5880_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5873_, v_a_5879_, v_a_5789_);
lean_dec_ref(v___x_5880_);
v___y_5825_ = v_a_5790_;
v___y_5826_ = v_a_5791_;
goto v___jp_5824_;
}
else
{
lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v_a_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5881_ = l_Lean_mkMVar(v_a_5797_);
v___x_5882_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5881_, v_a_5789_);
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
lean_inc(v_a_5883_);
lean_dec_ref(v___x_5882_);
v___x_5884_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5885_ = l_Lean_Meta_mkExpectedPropHint(v_a_5883_, v___x_5884_);
v___x_5886_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5873_, v___x_5885_, v_a_5789_);
lean_dec_ref(v___x_5886_);
v___y_5825_ = v_a_5790_;
v___y_5826_ = v_a_5791_;
goto v___jp_5824_;
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec(v_mvarId_5873_);
lean_dec(v_snd_5823_);
lean_dec(v_fst_5822_);
lean_del_object(v___x_5818_);
lean_dec(v_snd_5809_);
lean_dec(v_a_5797_);
v_a_5887_ = lean_ctor_get(v___x_5874_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5874_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5874_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5874_);
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
v___jp_5824_:
{
lean_object* v___x_5827_; uint8_t v___x_5828_; 
v___x_5827_ = lean_array_get_size(v_snd_5823_);
v___x_5828_ = lean_nat_dec_eq(v___x_5827_, v___x_5811_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5832_; 
lean_dec(v_fst_5822_);
lean_dec(v_snd_5809_);
v___x_5829_ = lean_array_to_list(v_snd_5823_);
v___x_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5829_);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v___x_5830_);
v___x_5832_ = v___x_5818_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5830_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
else
{
lean_dec(v_snd_5823_);
if (lean_obj_tag(v_snd_5809_) == 1)
{
lean_object* v_val_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5868_; 
lean_del_object(v___x_5818_);
v_val_5834_ = lean_ctor_get(v_snd_5809_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v_snd_5809_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5836_ = v_snd_5809_;
v_isShared_5837_ = v_isSharedCheck_5868_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_val_5834_);
lean_dec(v_snd_5809_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5868_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5838_; 
v___x_5838_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5834_, v___y_5825_);
lean_dec(v_val_5834_);
if (lean_obj_tag(v___x_5838_) == 0)
{
lean_object* v_a_5839_; lean_object* v___x_5840_; 
v_a_5839_ = lean_ctor_get(v___x_5838_, 0);
lean_inc(v_a_5839_);
lean_dec_ref_known(v___x_5838_, 1);
v___x_5840_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5839_, v_fst_5822_, v_compress_5779_, v___y_5825_, v___y_5826_);
if (lean_obj_tag(v___x_5840_) == 0)
{
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5851_; 
v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5843_ = v___x_5840_;
v_isShared_5844_ = v_isSharedCheck_5851_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5840_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5851_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5846_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set_tag(v___x_5836_, 0);
lean_ctor_set(v___x_5836_, 0, v_a_5841_);
v___x_5846_ = v___x_5836_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5841_);
v___x_5846_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
lean_object* v___x_5848_; 
if (v_isShared_5844_ == 0)
{
lean_ctor_set(v___x_5843_, 0, v___x_5846_);
v___x_5848_ = v___x_5843_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v___x_5846_);
v___x_5848_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5847_;
}
v_reusejp_5847_:
{
return v___x_5848_;
}
}
}
}
else
{
lean_object* v_a_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5859_; 
lean_del_object(v___x_5836_);
v_a_5852_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5854_ = v___x_5840_;
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_a_5852_);
lean_dec(v___x_5840_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5857_; 
if (v_isShared_5855_ == 0)
{
v___x_5857_ = v___x_5854_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
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
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_del_object(v___x_5836_);
lean_dec(v_fst_5822_);
v_a_5860_ = lean_ctor_get(v___x_5838_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5838_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5838_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5838_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___x_5865_; 
if (v_isShared_5863_ == 0)
{
v___x_5865_ = v___x_5862_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
}
else
{
lean_object* v___x_5869_; lean_object* v___x_5871_; 
lean_dec(v_fst_5822_);
lean_dec(v_snd_5809_);
v___x_5869_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v___x_5869_);
v___x_5871_ = v___x_5818_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v___x_5869_);
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
lean_object* v_val_5895_; lean_object* v___x_5897_; 
lean_inc_ref(v_fst_5820_);
lean_dec(v_a_5816_);
lean_dec(v_snd_5809_);
lean_dec(v_snd_5807_);
lean_dec(v_a_5797_);
v_val_5895_ = lean_ctor_get(v_fst_5820_, 0);
lean_inc(v_val_5895_);
lean_dec_ref_known(v_fst_5820_, 1);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v_val_5895_);
v___x_5897_ = v___x_5818_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_val_5895_);
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
lean_dec(v_snd_5809_);
lean_dec(v_snd_5807_);
lean_dec(v_a_5797_);
v_a_5900_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5815_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5815_);
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
lean_dec_ref(v___x_5799_);
lean_dec(v_a_5797_);
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_c_5775_);
v_a_5908_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5910_ = v___x_5804_;
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_a_5908_);
lean_dec(v___x_5804_);
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
else
{
lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_goal_5781_);
lean_dec(v_candidates_x3f_5780_);
lean_dec(v_numCases_5776_);
lean_dec_ref(v_c_5775_);
v_a_5916_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5918_ = v___x_5796_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5796_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec_ref(v_kp_5782_);
lean_dec_ref(v_goal_5781_);
lean_dec(v_candidates_x3f_5780_);
lean_dec(v_numCases_5776_);
lean_dec_ref(v_c_5775_);
v_a_5924_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5793_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5793_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5932_ = _args[0];
lean_object* v_numCases_5933_ = _args[1];
lean_object* v_isRec_5934_ = _args[2];
lean_object* v_stopAtFirstFailure_5935_ = _args[3];
lean_object* v_compress_5936_ = _args[4];
lean_object* v_candidates_x3f_5937_ = _args[5];
lean_object* v_goal_5938_ = _args[6];
lean_object* v_kp_5939_ = _args[7];
lean_object* v_a_5940_ = _args[8];
lean_object* v_a_5941_ = _args[9];
lean_object* v_a_5942_ = _args[10];
lean_object* v_a_5943_ = _args[11];
lean_object* v_a_5944_ = _args[12];
lean_object* v_a_5945_ = _args[13];
lean_object* v_a_5946_ = _args[14];
lean_object* v_a_5947_ = _args[15];
lean_object* v_a_5948_ = _args[16];
lean_object* v_a_5949_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5950_; uint8_t v_stopAtFirstFailure_boxed_5951_; uint8_t v_compress_boxed_5952_; lean_object* v_res_5953_; 
v_isRec_boxed_5950_ = lean_unbox(v_isRec_5934_);
v_stopAtFirstFailure_boxed_5951_ = lean_unbox(v_stopAtFirstFailure_5935_);
v_compress_boxed_5952_ = lean_unbox(v_compress_5936_);
v_res_5953_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5932_, v_numCases_5933_, v_isRec_boxed_5950_, v_stopAtFirstFailure_boxed_5951_, v_compress_boxed_5952_, v_candidates_x3f_5937_, v_goal_5938_, v_kp_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
lean_dec(v_a_5944_);
lean_dec_ref(v_a_5943_);
lean_dec(v_a_5942_);
lean_dec_ref(v_a_5941_);
lean_dec(v_a_5940_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5954_, lean_object* v_numCases_5955_, uint8_t v_isRec_5956_, uint8_t v_stopAtFirstFailure_5957_, uint8_t v_compress_5958_, lean_object* v_candidates_x3f_5959_, lean_object* v_goal_5960_, lean_object* v_x_5961_, lean_object* v_kp_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
lean_object* v___x_5973_; 
v___x_5973_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5954_, v_numCases_5955_, v_isRec_5956_, v_stopAtFirstFailure_5957_, v_compress_5958_, v_candidates_x3f_5959_, v_goal_5960_, v_kp_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_);
return v___x_5973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5974_ = _args[0];
lean_object* v_numCases_5975_ = _args[1];
lean_object* v_isRec_5976_ = _args[2];
lean_object* v_stopAtFirstFailure_5977_ = _args[3];
lean_object* v_compress_5978_ = _args[4];
lean_object* v_candidates_x3f_5979_ = _args[5];
lean_object* v_goal_5980_ = _args[6];
lean_object* v_x_5981_ = _args[7];
lean_object* v_kp_5982_ = _args[8];
lean_object* v_a_5983_ = _args[9];
lean_object* v_a_5984_ = _args[10];
lean_object* v_a_5985_ = _args[11];
lean_object* v_a_5986_ = _args[12];
lean_object* v_a_5987_ = _args[13];
lean_object* v_a_5988_ = _args[14];
lean_object* v_a_5989_ = _args[15];
lean_object* v_a_5990_ = _args[16];
lean_object* v_a_5991_ = _args[17];
lean_object* v_a_5992_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5993_; uint8_t v_stopAtFirstFailure_boxed_5994_; uint8_t v_compress_boxed_5995_; lean_object* v_res_5996_; 
v_isRec_boxed_5993_ = lean_unbox(v_isRec_5976_);
v_stopAtFirstFailure_boxed_5994_ = lean_unbox(v_stopAtFirstFailure_5977_);
v_compress_boxed_5995_ = lean_unbox(v_compress_5978_);
v_res_5996_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5974_, v_numCases_5975_, v_isRec_boxed_5993_, v_stopAtFirstFailure_boxed_5994_, v_compress_boxed_5995_, v_candidates_x3f_5979_, v_goal_5980_, v_x_5981_, v_kp_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
lean_dec(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec_ref(v_a_5988_);
lean_dec(v_a_5987_);
lean_dec_ref(v_a_5986_);
lean_dec(v_a_5985_);
lean_dec_ref(v_a_5984_);
lean_dec(v_a_5983_);
lean_dec_ref(v_x_5981_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5997_, lean_object* v_snd_5998_, uint8_t v_stopAtFirstFailure_5999_, lean_object* v_as_6000_, lean_object* v_as_x27_6001_, lean_object* v_b_6002_, lean_object* v_a_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_){
_start:
{
lean_object* v___x_6014_; 
v___x_6014_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5997_, v_snd_5998_, v_stopAtFirstFailure_5999_, v_as_x27_6001_, v_b_6002_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_);
return v___x_6014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6015_ = _args[0];
lean_object* v_snd_6016_ = _args[1];
lean_object* v_stopAtFirstFailure_6017_ = _args[2];
lean_object* v_as_6018_ = _args[3];
lean_object* v_as_x27_6019_ = _args[4];
lean_object* v_b_6020_ = _args[5];
lean_object* v_a_6021_ = _args[6];
lean_object* v___y_6022_ = _args[7];
lean_object* v___y_6023_ = _args[8];
lean_object* v___y_6024_ = _args[9];
lean_object* v___y_6025_ = _args[10];
lean_object* v___y_6026_ = _args[11];
lean_object* v___y_6027_ = _args[12];
lean_object* v___y_6028_ = _args[13];
lean_object* v___y_6029_ = _args[14];
lean_object* v___y_6030_ = _args[15];
lean_object* v___y_6031_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6032_; lean_object* v_res_6033_; 
v_stopAtFirstFailure_boxed_6032_ = lean_unbox(v_stopAtFirstFailure_6017_);
v_res_6033_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6015_, v_snd_6016_, v_stopAtFirstFailure_boxed_6032_, v_as_6018_, v_as_x27_6019_, v_b_6020_, v_a_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec(v___y_6028_);
lean_dec_ref(v___y_6027_);
lean_dec(v___y_6026_);
lean_dec_ref(v___y_6025_);
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec(v___y_6022_);
lean_dec(v_as_x27_6019_);
lean_dec(v_as_6018_);
return v_res_6033_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6034_, lean_object* v_val_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_){
_start:
{
lean_object* v___x_6046_; 
v___x_6046_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6034_, v_val_6035_, v___y_6042_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6047_, lean_object* v_val_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6047_, v_val_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v___y_6049_);
return v_res_6059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6060_, lean_object* v_x_6061_, lean_object* v_x_6062_, lean_object* v_x_6063_){
_start:
{
lean_object* v___x_6064_; 
v___x_6064_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6061_, v_x_6062_, v_x_6063_);
return v___x_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6065_, lean_object* v_x_6066_, size_t v_x_6067_, size_t v_x_6068_, lean_object* v_x_6069_, lean_object* v_x_6070_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6066_, v_x_6067_, v_x_6068_, v_x_6069_, v_x_6070_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6072_, lean_object* v_x_6073_, lean_object* v_x_6074_, lean_object* v_x_6075_, lean_object* v_x_6076_, lean_object* v_x_6077_){
_start:
{
size_t v_x_67933__boxed_6078_; size_t v_x_67934__boxed_6079_; lean_object* v_res_6080_; 
v_x_67933__boxed_6078_ = lean_unbox_usize(v_x_6074_);
lean_dec(v_x_6074_);
v_x_67934__boxed_6079_ = lean_unbox_usize(v_x_6075_);
lean_dec(v_x_6075_);
v_res_6080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6072_, v_x_6073_, v_x_67933__boxed_6078_, v_x_67934__boxed_6079_, v_x_6076_, v_x_6077_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6081_, lean_object* v_n_6082_, lean_object* v_k_6083_, lean_object* v_v_6084_){
_start:
{
lean_object* v___x_6085_; 
v___x_6085_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6082_, v_k_6083_, v_v_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6086_, size_t v_depth_6087_, lean_object* v_keys_6088_, lean_object* v_vals_6089_, lean_object* v_heq_6090_, lean_object* v_i_6091_, lean_object* v_entries_6092_){
_start:
{
lean_object* v___x_6093_; 
v___x_6093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6087_, v_keys_6088_, v_vals_6089_, v_i_6091_, v_entries_6092_);
return v___x_6093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6094_, lean_object* v_depth_6095_, lean_object* v_keys_6096_, lean_object* v_vals_6097_, lean_object* v_heq_6098_, lean_object* v_i_6099_, lean_object* v_entries_6100_){
_start:
{
size_t v_depth_boxed_6101_; lean_object* v_res_6102_; 
v_depth_boxed_6101_ = lean_unbox_usize(v_depth_6095_);
lean_dec(v_depth_6095_);
v_res_6102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6094_, v_depth_boxed_6101_, v_keys_6096_, v_vals_6097_, v_heq_6098_, v_i_6099_, v_entries_6100_);
lean_dec_ref(v_vals_6097_);
lean_dec_ref(v_keys_6096_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6103_, lean_object* v_x_6104_, lean_object* v_x_6105_, lean_object* v_x_6106_, lean_object* v_x_6107_){
_start:
{
lean_object* v___x_6108_; 
v___x_6108_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6104_, v_x_6105_, v_x_6106_, v_x_6107_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_){
_start:
{
lean_object* v___x_6122_; 
v___x_6122_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6109_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
return v___x_6122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_){
_start:
{
lean_object* v_res_6136_; 
v_res_6136_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_);
lean_dec(v___y_6134_);
lean_dec_ref(v___y_6133_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec_ref(v___y_6127_);
lean_dec(v___y_6126_);
lean_dec_ref(v___y_6124_);
return v_res_6136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_){
_start:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; 
v___x_6148_ = lean_st_mk_ref(v_goal_6137_);
v___x_6149_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6148_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_);
if (lean_obj_tag(v___x_6149_) == 0)
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6159_; 
v_a_6150_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6159_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6159_ == 0)
{
v___x_6152_ = v___x_6149_;
v_isShared_6153_ = v_isSharedCheck_6159_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6149_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6159_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6157_; 
v___x_6154_ = lean_st_ref_get(v___x_6148_);
lean_dec(v___x_6148_);
v___x_6155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6155_, 0, v_a_6150_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 0, v___x_6155_);
v___x_6157_ = v___x_6152_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6155_);
v___x_6157_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
return v___x_6157_;
}
}
}
else
{
lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
lean_dec(v___x_6148_);
v_a_6160_ = lean_ctor_get(v___x_6149_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6149_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_6149_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_6149_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6180_, lean_object* v___f_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_){
_start:
{
lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6195_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6195_, 0, v___y_6180_);
v___x_6196_ = l_Lean_Meta_Grind_Action_andThen(v___x_6195_, v___f_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6197_, lean_object* v___f_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v_res_6212_; 
v_res_6212_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6197_, v___f_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v___y_6202_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6214_, uint8_t v_compress_6215_, lean_object* v_goal_6216_, lean_object* v_kna_6217_, lean_object* v_kp_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_, lean_object* v_a_6227_){
_start:
{
lean_object* v_toGoalState_6229_; lean_object* v_split_6230_; lean_object* v_mvarId_6231_; lean_object* v_candidates_6232_; lean_object* v___f_6233_; lean_object* v___f_6234_; lean_object* v___x_6235_; 
v_toGoalState_6229_ = lean_ctor_get(v_goal_6216_, 0);
v_split_6230_ = lean_ctor_get(v_toGoalState_6229_, 15);
v_mvarId_6231_ = lean_ctor_get(v_goal_6216_, 1);
lean_inc(v_mvarId_6231_);
v_candidates_6232_ = lean_ctor_get(v_split_6230_, 1);
lean_inc(v_candidates_6232_);
v___f_6233_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6234_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6234_, 0, v_goal_6216_);
v___x_6235_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6231_, v___f_6234_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
if (lean_obj_tag(v___x_6235_) == 0)
{
lean_object* v_a_6236_; lean_object* v_fst_6237_; 
v_a_6236_ = lean_ctor_get(v___x_6235_, 0);
lean_inc(v_a_6236_);
lean_dec_ref_known(v___x_6235_, 1);
v_fst_6237_ = lean_ctor_get(v_a_6236_, 0);
if (lean_obj_tag(v_fst_6237_) == 1)
{
lean_object* v_snd_6238_; lean_object* v_c_6239_; lean_object* v_numCases_6240_; uint8_t v_isRec_6241_; lean_object* v___y_6243_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; uint8_t v___x_6256_; 
lean_inc_ref(v_fst_6237_);
v_snd_6238_ = lean_ctor_get(v_a_6236_, 1);
lean_inc(v_snd_6238_);
lean_dec(v_a_6236_);
v_c_6239_ = lean_ctor_get(v_fst_6237_, 0);
lean_inc_ref(v_c_6239_);
v_numCases_6240_ = lean_ctor_get(v_fst_6237_, 1);
lean_inc(v_numCases_6240_);
v_isRec_6241_ = lean_ctor_get_uint8(v_fst_6237_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6237_, 2);
v___x_6251_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6239_);
v___x_6252_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6238_, v___x_6251_);
lean_dec_ref(v___x_6251_);
v___x_6253_ = lean_unsigned_to_nat(1u);
v___x_6256_ = lean_nat_dec_lt(v___x_6253_, v_numCases_6240_);
if (v___x_6256_ == 0)
{
if (v_isRec_6241_ == 0)
{
v___y_6243_ = v___x_6252_;
goto v___jp_6242_;
}
else
{
goto v___jp_6254_;
}
}
else
{
goto v___jp_6254_;
}
v___jp_6242_:
{
lean_object* v___f_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___f_6244_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6244_, 0, v___y_6243_);
lean_closure_set(v___f_6244_, 1, v___f_6233_);
v___x_6245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6245_, 0, v_candidates_6232_);
v___x_6246_ = lean_box(v_isRec_6241_);
v___x_6247_ = lean_box(v_stopAtFirstFailure_6214_);
v___x_6248_ = lean_box(v_compress_6215_);
v___x_6249_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6249_, 0, v_c_6239_);
lean_closure_set(v___x_6249_, 1, v_numCases_6240_);
lean_closure_set(v___x_6249_, 2, v___x_6246_);
lean_closure_set(v___x_6249_, 3, v___x_6247_);
lean_closure_set(v___x_6249_, 4, v___x_6248_);
lean_closure_set(v___x_6249_, 5, v___x_6245_);
v___x_6250_ = l_Lean_Meta_Grind_Action_andThen(v___x_6249_, v___f_6244_, v_snd_6238_, v_kna_6217_, v_kp_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_);
return v___x_6250_;
}
v___jp_6254_:
{
lean_object* v___x_6255_; 
v___x_6255_ = lean_nat_add(v___x_6252_, v___x_6253_);
lean_dec(v___x_6252_);
v___y_6243_ = v___x_6255_;
goto v___jp_6242_;
}
}
else
{
lean_object* v_snd_6257_; lean_object* v___x_6258_; 
lean_dec(v_candidates_6232_);
lean_dec_ref(v_kp_6218_);
v_snd_6257_ = lean_ctor_get(v_a_6236_, 1);
lean_inc(v_snd_6257_);
lean_dec(v_a_6236_);
lean_inc(v_a_6227_);
lean_inc_ref(v_a_6226_);
lean_inc(v_a_6225_);
lean_inc_ref(v_a_6224_);
lean_inc(v_a_6223_);
lean_inc_ref(v_a_6222_);
lean_inc(v_a_6221_);
lean_inc_ref(v_a_6220_);
lean_inc(v_a_6219_);
v___x_6258_ = lean_apply_11(v_kna_6217_, v_snd_6257_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, v_a_6225_, v_a_6226_, v_a_6227_, lean_box(0));
return v___x_6258_;
}
}
else
{
lean_object* v_a_6259_; lean_object* v___x_6261_; uint8_t v_isShared_6262_; uint8_t v_isSharedCheck_6266_; 
lean_dec(v_candidates_6232_);
lean_dec_ref(v_kp_6218_);
lean_dec_ref(v_kna_6217_);
v_a_6259_ = lean_ctor_get(v___x_6235_, 0);
v_isSharedCheck_6266_ = !lean_is_exclusive(v___x_6235_);
if (v_isSharedCheck_6266_ == 0)
{
v___x_6261_ = v___x_6235_;
v_isShared_6262_ = v_isSharedCheck_6266_;
goto v_resetjp_6260_;
}
else
{
lean_inc(v_a_6259_);
lean_dec(v___x_6235_);
v___x_6261_ = lean_box(0);
v_isShared_6262_ = v_isSharedCheck_6266_;
goto v_resetjp_6260_;
}
v_resetjp_6260_:
{
lean_object* v___x_6264_; 
if (v_isShared_6262_ == 0)
{
v___x_6264_ = v___x_6261_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6259_);
v___x_6264_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
return v___x_6264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6267_, lean_object* v_compress_6268_, lean_object* v_goal_6269_, lean_object* v_kna_6270_, lean_object* v_kp_6271_, lean_object* v_a_6272_, lean_object* v_a_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_, lean_object* v_a_6276_, lean_object* v_a_6277_, lean_object* v_a_6278_, lean_object* v_a_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6282_; uint8_t v_compress_boxed_6283_; lean_object* v_res_6284_; 
v_stopAtFirstFailure_boxed_6282_ = lean_unbox(v_stopAtFirstFailure_6267_);
v_compress_boxed_6283_ = lean_unbox(v_compress_6268_);
v_res_6284_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6282_, v_compress_boxed_6283_, v_goal_6269_, v_kna_6270_, v_kp_6271_, v_a_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_, v_a_6278_, v_a_6279_, v_a_6280_);
lean_dec(v_a_6280_);
lean_dec_ref(v_a_6279_);
lean_dec(v_a_6278_);
lean_dec_ref(v_a_6277_);
lean_dec(v_a_6276_);
lean_dec_ref(v_a_6275_);
lean_dec(v_a_6274_);
lean_dec_ref(v_a_6273_);
lean_dec(v_a_6272_);
return v_res_6284_;
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
