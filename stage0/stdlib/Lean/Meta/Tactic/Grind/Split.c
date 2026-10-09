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
v_split_2449_ = lean_ctor_get(v_toGoalState_2445_, 14);
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
lean_object* v___x_2875_; lean_object* v_toGoalState_2876_; lean_object* v_split_2877_; lean_object* v_mvarId_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2986_; 
v___x_2875_ = lean_st_ref_take(v_a_2864_);
v_toGoalState_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc_ref(v_toGoalState_2876_);
v_split_2877_ = lean_ctor_get(v_toGoalState_2876_, 14);
lean_inc_ref(v_split_2877_);
v_mvarId_2878_ = lean_ctor_get(v___x_2875_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2875_, 0);
lean_dec(v_unused_2987_);
v___x_2880_ = v___x_2875_;
v_isShared_2881_ = v_isSharedCheck_2986_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_mvarId_2878_);
lean_dec(v___x_2875_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2986_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_nextDeclIdx_2882_; lean_object* v_enodeMap_2883_; lean_object* v_exprs_2884_; lean_object* v_parents_2885_; lean_object* v_congrTable_2886_; lean_object* v_appMap_2887_; lean_object* v_indicesFound_2888_; lean_object* v_toProcess_2889_; uint8_t v_inconsistent_2890_; lean_object* v_nextIdx_2891_; lean_object* v_newRawFacts_2892_; lean_object* v_facts_2893_; lean_object* v_extThms_2894_; lean_object* v_ematch_2895_; lean_object* v_inj_2896_; lean_object* v_clean_2897_; lean_object* v_sstates_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2984_; 
v_nextDeclIdx_2882_ = lean_ctor_get(v_toGoalState_2876_, 0);
v_enodeMap_2883_ = lean_ctor_get(v_toGoalState_2876_, 1);
v_exprs_2884_ = lean_ctor_get(v_toGoalState_2876_, 2);
v_parents_2885_ = lean_ctor_get(v_toGoalState_2876_, 3);
v_congrTable_2886_ = lean_ctor_get(v_toGoalState_2876_, 4);
v_appMap_2887_ = lean_ctor_get(v_toGoalState_2876_, 5);
v_indicesFound_2888_ = lean_ctor_get(v_toGoalState_2876_, 6);
v_toProcess_2889_ = lean_ctor_get(v_toGoalState_2876_, 7);
v_inconsistent_2890_ = lean_ctor_get_uint8(v_toGoalState_2876_, sizeof(void*)*17);
v_nextIdx_2891_ = lean_ctor_get(v_toGoalState_2876_, 8);
v_newRawFacts_2892_ = lean_ctor_get(v_toGoalState_2876_, 9);
v_facts_2893_ = lean_ctor_get(v_toGoalState_2876_, 10);
v_extThms_2894_ = lean_ctor_get(v_toGoalState_2876_, 11);
v_ematch_2895_ = lean_ctor_get(v_toGoalState_2876_, 12);
v_inj_2896_ = lean_ctor_get(v_toGoalState_2876_, 13);
v_clean_2897_ = lean_ctor_get(v_toGoalState_2876_, 15);
v_sstates_2898_ = lean_ctor_get(v_toGoalState_2876_, 16);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_toGoalState_2876_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_toGoalState_2876_, 14);
lean_dec(v_unused_2985_);
v___x_2900_ = v_toGoalState_2876_;
v_isShared_2901_ = v_isSharedCheck_2984_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_sstates_2898_);
lean_inc(v_clean_2897_);
lean_inc(v_inj_2896_);
lean_inc(v_ematch_2895_);
lean_inc(v_extThms_2894_);
lean_inc(v_facts_2893_);
lean_inc(v_newRawFacts_2892_);
lean_inc(v_nextIdx_2891_);
lean_inc(v_toProcess_2889_);
lean_inc(v_indicesFound_2888_);
lean_inc(v_appMap_2887_);
lean_inc(v_congrTable_2886_);
lean_inc(v_parents_2885_);
lean_inc(v_exprs_2884_);
lean_inc(v_enodeMap_2883_);
lean_inc(v_nextDeclIdx_2882_);
lean_dec(v_toGoalState_2876_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2984_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_num_2902_; lean_object* v_added_2903_; lean_object* v_resolved_2904_; lean_object* v_trace_2905_; lean_object* v_lookaheads_2906_; lean_object* v_argPosMap_2907_; lean_object* v_argsAt_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2982_; 
v_num_2902_ = lean_ctor_get(v_split_2877_, 0);
v_added_2903_ = lean_ctor_get(v_split_2877_, 2);
v_resolved_2904_ = lean_ctor_get(v_split_2877_, 3);
v_trace_2905_ = lean_ctor_get(v_split_2877_, 4);
v_lookaheads_2906_ = lean_ctor_get(v_split_2877_, 5);
v_argPosMap_2907_ = lean_ctor_get(v_split_2877_, 6);
v_argsAt_2908_ = lean_ctor_get(v_split_2877_, 7);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_split_2877_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_split_2877_, 1);
lean_dec(v_unused_2983_);
v___x_2910_ = v_split_2877_;
v_isShared_2911_ = v_isSharedCheck_2982_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_argsAt_2908_);
lean_inc(v_argPosMap_2907_);
lean_inc(v_lookaheads_2906_);
lean_inc(v_trace_2905_);
lean_inc(v_resolved_2904_);
lean_inc(v_added_2903_);
lean_inc(v_num_2902_);
lean_dec(v_split_2877_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2982_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = l_List_reverse___redArg(v_cs_x27_2863_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_num_2902_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_added_2903_);
lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_resolved_2904_);
lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_trace_2905_);
lean_ctor_set(v_reuseFailAlloc_2981_, 5, v_lookaheads_2906_);
lean_ctor_set(v_reuseFailAlloc_2981_, 6, v_argPosMap_2907_);
lean_ctor_set(v_reuseFailAlloc_2981_, 7, v_argsAt_2908_);
v___x_2914_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 14, v___x_2914_);
v___x_2916_ = v___x_2900_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_nextDeclIdx_2882_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_enodeMap_2883_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_exprs_2884_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_parents_2885_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_congrTable_2886_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_appMap_2887_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_indicesFound_2888_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_toProcess_2889_);
lean_ctor_set(v_reuseFailAlloc_2980_, 8, v_nextIdx_2891_);
lean_ctor_set(v_reuseFailAlloc_2980_, 9, v_newRawFacts_2892_);
lean_ctor_set(v_reuseFailAlloc_2980_, 10, v_facts_2893_);
lean_ctor_set(v_reuseFailAlloc_2980_, 11, v_extThms_2894_);
lean_ctor_set(v_reuseFailAlloc_2980_, 12, v_ematch_2895_);
lean_ctor_set(v_reuseFailAlloc_2980_, 13, v_inj_2896_);
lean_ctor_set(v_reuseFailAlloc_2980_, 14, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2980_, 15, v_clean_2897_);
lean_ctor_set(v_reuseFailAlloc_2980_, 16, v_sstates_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*17, v_inconsistent_2890_);
v___x_2916_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2916_);
v___x_2918_ = v___x_2880_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_mvarId_2878_);
v___x_2918_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_st_ref_put(v_a_2864_, v___x_2918_);
if (lean_obj_tag(v_c_x3f_2862_) == 1)
{
lean_object* v___x_2920_; lean_object* v_toGoalState_2921_; lean_object* v_ematch_2922_; lean_object* v_mvarId_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2976_; 
v___x_2920_ = lean_st_ref_take(v_a_2864_);
v_toGoalState_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_toGoalState_2921_);
v_ematch_2922_ = lean_ctor_get(v_toGoalState_2921_, 12);
lean_inc_ref(v_ematch_2922_);
v_mvarId_2923_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2977_);
v___x_2925_ = v___x_2920_;
v_isShared_2926_ = v_isSharedCheck_2976_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_mvarId_2923_);
lean_dec(v___x_2920_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2976_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_nextDeclIdx_2927_; lean_object* v_enodeMap_2928_; lean_object* v_exprs_2929_; lean_object* v_parents_2930_; lean_object* v_congrTable_2931_; lean_object* v_appMap_2932_; lean_object* v_indicesFound_2933_; lean_object* v_toProcess_2934_; uint8_t v_inconsistent_2935_; lean_object* v_nextIdx_2936_; lean_object* v_newRawFacts_2937_; lean_object* v_facts_2938_; lean_object* v_extThms_2939_; lean_object* v_inj_2940_; lean_object* v_split_2941_; lean_object* v_clean_2942_; lean_object* v_sstates_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2974_; 
v_nextDeclIdx_2927_ = lean_ctor_get(v_toGoalState_2921_, 0);
v_enodeMap_2928_ = lean_ctor_get(v_toGoalState_2921_, 1);
v_exprs_2929_ = lean_ctor_get(v_toGoalState_2921_, 2);
v_parents_2930_ = lean_ctor_get(v_toGoalState_2921_, 3);
v_congrTable_2931_ = lean_ctor_get(v_toGoalState_2921_, 4);
v_appMap_2932_ = lean_ctor_get(v_toGoalState_2921_, 5);
v_indicesFound_2933_ = lean_ctor_get(v_toGoalState_2921_, 6);
v_toProcess_2934_ = lean_ctor_get(v_toGoalState_2921_, 7);
v_inconsistent_2935_ = lean_ctor_get_uint8(v_toGoalState_2921_, sizeof(void*)*17);
v_nextIdx_2936_ = lean_ctor_get(v_toGoalState_2921_, 8);
v_newRawFacts_2937_ = lean_ctor_get(v_toGoalState_2921_, 9);
v_facts_2938_ = lean_ctor_get(v_toGoalState_2921_, 10);
v_extThms_2939_ = lean_ctor_get(v_toGoalState_2921_, 11);
v_inj_2940_ = lean_ctor_get(v_toGoalState_2921_, 13);
v_split_2941_ = lean_ctor_get(v_toGoalState_2921_, 14);
v_clean_2942_ = lean_ctor_get(v_toGoalState_2921_, 15);
v_sstates_2943_ = lean_ctor_get(v_toGoalState_2921_, 16);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_toGoalState_2921_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v_toGoalState_2921_, 12);
lean_dec(v_unused_2975_);
v___x_2945_ = v_toGoalState_2921_;
v_isShared_2946_ = v_isSharedCheck_2974_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_sstates_2943_);
lean_inc(v_clean_2942_);
lean_inc(v_split_2941_);
lean_inc(v_inj_2940_);
lean_inc(v_extThms_2939_);
lean_inc(v_facts_2938_);
lean_inc(v_newRawFacts_2937_);
lean_inc(v_nextIdx_2936_);
lean_inc(v_toProcess_2934_);
lean_inc(v_indicesFound_2933_);
lean_inc(v_appMap_2932_);
lean_inc(v_congrTable_2931_);
lean_inc(v_parents_2930_);
lean_inc(v_exprs_2929_);
lean_inc(v_enodeMap_2928_);
lean_inc(v_nextDeclIdx_2927_);
lean_dec(v_toGoalState_2921_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2974_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_thmMap_2947_; lean_object* v_gmt_2948_; lean_object* v_thms_2949_; lean_object* v_newThms_2950_; lean_object* v_numInstances_2951_; lean_object* v_numDelayedInstances_2952_; lean_object* v_preInstances_2953_; lean_object* v_nextThmIdx_2954_; lean_object* v_matchEqNames_2955_; lean_object* v_delayedThmInsts_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2972_; 
v_thmMap_2947_ = lean_ctor_get(v_ematch_2922_, 0);
v_gmt_2948_ = lean_ctor_get(v_ematch_2922_, 1);
v_thms_2949_ = lean_ctor_get(v_ematch_2922_, 2);
v_newThms_2950_ = lean_ctor_get(v_ematch_2922_, 3);
v_numInstances_2951_ = lean_ctor_get(v_ematch_2922_, 4);
v_numDelayedInstances_2952_ = lean_ctor_get(v_ematch_2922_, 5);
v_preInstances_2953_ = lean_ctor_get(v_ematch_2922_, 7);
v_nextThmIdx_2954_ = lean_ctor_get(v_ematch_2922_, 8);
v_matchEqNames_2955_ = lean_ctor_get(v_ematch_2922_, 9);
v_delayedThmInsts_2956_ = lean_ctor_get(v_ematch_2922_, 10);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_ematch_2922_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; 
v_unused_2973_ = lean_ctor_get(v_ematch_2922_, 6);
lean_dec(v_unused_2973_);
v___x_2958_ = v_ematch_2922_;
v_isShared_2959_ = v_isSharedCheck_2972_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_delayedThmInsts_2956_);
lean_inc(v_matchEqNames_2955_);
lean_inc(v_nextThmIdx_2954_);
lean_inc(v_preInstances_2953_);
lean_inc(v_numDelayedInstances_2952_);
lean_inc(v_numInstances_2951_);
lean_inc(v_newThms_2950_);
lean_inc(v_thms_2949_);
lean_inc(v_gmt_2948_);
lean_inc(v_thmMap_2947_);
lean_dec(v_ematch_2922_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2972_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = lean_unsigned_to_nat(0u);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 6, v___x_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_thmMap_2947_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_gmt_2948_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_thms_2949_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_newThms_2950_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_numInstances_2951_);
lean_ctor_set(v_reuseFailAlloc_2971_, 5, v_numDelayedInstances_2952_);
lean_ctor_set(v_reuseFailAlloc_2971_, 6, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2971_, 7, v_preInstances_2953_);
lean_ctor_set(v_reuseFailAlloc_2971_, 8, v_nextThmIdx_2954_);
lean_ctor_set(v_reuseFailAlloc_2971_, 9, v_matchEqNames_2955_);
lean_ctor_set(v_reuseFailAlloc_2971_, 10, v_delayedThmInsts_2956_);
v___x_2962_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 12, v___x_2962_);
v___x_2964_ = v___x_2945_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_nextDeclIdx_2927_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_enodeMap_2928_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_exprs_2929_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_parents_2930_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_congrTable_2931_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v_appMap_2932_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v_indicesFound_2933_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_toProcess_2934_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v_nextIdx_2936_);
lean_ctor_set(v_reuseFailAlloc_2970_, 9, v_newRawFacts_2937_);
lean_ctor_set(v_reuseFailAlloc_2970_, 10, v_facts_2938_);
lean_ctor_set(v_reuseFailAlloc_2970_, 11, v_extThms_2939_);
lean_ctor_set(v_reuseFailAlloc_2970_, 12, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2970_, 13, v_inj_2940_);
lean_ctor_set(v_reuseFailAlloc_2970_, 14, v_split_2941_);
lean_ctor_set(v_reuseFailAlloc_2970_, 15, v_clean_2942_);
lean_ctor_set(v_reuseFailAlloc_2970_, 16, v_sstates_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, sizeof(void*)*17, v_inconsistent_2935_);
v___x_2964_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2964_);
v___x_2966_ = v___x_2925_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_mvarId_2923_);
v___x_2966_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_st_ref_put(v_a_2864_, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v_c_x3f_2862_);
return v___x_2968_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_c_x3f_2862_);
return v___x_2978_;
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
lean_object* v_head_2988_; lean_object* v_tail_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3209_; 
v_head_2988_ = lean_ctor_get(v_cs_2861_, 0);
v_tail_2989_ = lean_ctor_get(v_cs_2861_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_cs_2861_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_2991_ = v_cs_2861_;
v_isShared_2992_ = v_isSharedCheck_3209_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_tail_2989_);
lean_inc(v_head_2988_);
lean_dec(v_cs_2861_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3209_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; uint8_t v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; lean_object* v___x_3101_; 
v___x_3101_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2988_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; uint8_t v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = lean_unbox(v_a_3102_);
lean_dec(v_a_3102_);
if (v___x_3103_ == 0)
{
lean_del_object(v___x_2991_);
lean_dec(v_head_2988_);
v_cs_2861_ = v_tail_2989_;
goto _start;
}
else
{
lean_object* v_toCold_3105_; lean_object* v_options_3106_; lean_object* v_inheritedTraceOptions_3107_; uint8_t v_hasTrace_3108_; uint8_t v___x_3109_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; 
v_toCold_3105_ = lean_ctor_get(v_a_2872_, 0);
v_options_3106_ = lean_ctor_get(v_toCold_3105_, 2);
v_inheritedTraceOptions_3107_ = lean_ctor_get(v_toCold_3105_, 11);
v_hasTrace_3108_ = lean_ctor_get_uint8(v_options_3106_, sizeof(void*)*1);
v___x_3109_ = 0;
if (v_hasTrace_3108_ == 0)
{
v___y_3135_ = v_a_2864_;
v___y_3136_ = v_a_2865_;
v___y_3137_ = v_a_2866_;
v___y_3138_ = v_a_2867_;
v___y_3139_ = v_a_2868_;
v___y_3140_ = v_a_2869_;
v___y_3141_ = v_a_2870_;
v___y_3142_ = v_a_2871_;
v___y_3143_ = v_a_2872_;
v___y_3144_ = v_a_2873_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3107_, v_options_3106_, v___x_3177_);
if (v___x_3178_ == 0)
{
v___y_3135_ = v_a_2864_;
v___y_3136_ = v_a_2865_;
v___y_3137_ = v_a_2866_;
v___y_3138_ = v_a_2867_;
v___y_3139_ = v_a_2868_;
v___y_3140_ = v_a_2869_;
v___y_3141_ = v_a_2870_;
v___y_3142_ = v_a_2871_;
v___y_3143_ = v_a_2872_;
v___y_3144_ = v_a_2873_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_Meta_Grind_updateLastTag(v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec_ref_known(v___x_3179_, 1);
v___x_3180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3181_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2988_);
v___x_3182_ = l_Lean_MessageData_ofExpr(v___x_3181_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3176_, v___x_3183_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_dec_ref_known(v___x_3184_, 1);
v___y_3135_ = v_a_2864_;
v___y_3136_ = v_a_2865_;
v___y_3137_ = v_a_2866_;
v___y_3138_ = v_a_2867_;
v___y_3139_ = v_a_2868_;
v___y_3140_ = v_a_2869_;
v___y_3141_ = v_a_2870_;
v___y_3142_ = v_a_2871_;
v___y_3143_ = v_a_2872_;
v___y_3144_ = v_a_2873_;
goto v___jp_3134_;
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3193_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3179_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3179_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
v___jp_3110_:
{
if (lean_obj_tag(v_c_x3f_2862_) == 0)
{
lean_object* v___x_3125_; 
lean_del_object(v___x_2991_);
v___x_3125_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3125_, 0, v_head_2988_);
lean_ctor_set(v___x_3125_, 1, v___y_3123_);
lean_ctor_set_uint8(v___x_3125_, sizeof(void*)*2, v___y_3122_);
lean_ctor_set_uint8(v___x_3125_, sizeof(void*)*2 + 1, v___y_3115_);
v_cs_2861_ = v_tail_2989_;
v_c_x3f_2862_ = v___x_3125_;
v_a_2864_ = v___y_3119_;
v_a_2865_ = v___y_3114_;
v_a_2866_ = v___y_3117_;
v_a_2867_ = v___y_3121_;
v_a_2868_ = v___y_3111_;
v_a_2869_ = v___y_3120_;
v_a_2870_ = v___y_3112_;
v_a_2871_ = v___y_3116_;
v_a_2872_ = v___y_3113_;
v_a_2873_ = v___y_3118_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3127_; 
v_tryPostpone_3127_ = lean_ctor_get_uint8(v_c_x3f_2862_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3127_ == 0)
{
if (v___y_3115_ == 0)
{
lean_object* v_c_3128_; lean_object* v_numCases_3129_; 
v_c_3128_ = lean_ctor_get(v_c_x3f_2862_, 0);
v_numCases_3129_ = lean_ctor_get(v_c_x3f_2862_, 1);
lean_inc_ref(v_c_3128_);
lean_inc(v_numCases_3129_);
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v___y_3115_;
v___y_3088_ = v_numCases_3129_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v___y_3121_;
v___y_3095_ = v_c_3128_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___x_3109_;
goto v___jp_3082_;
}
else
{
lean_dec(v___y_3123_);
v___y_2994_ = v___y_3120_;
v___y_2995_ = v___y_3111_;
v___y_2996_ = v___y_3112_;
v___y_2997_ = v___y_3113_;
v___y_2998_ = v___y_3114_;
v___y_2999_ = v___y_3121_;
v___y_3000_ = v___y_3116_;
v___y_3001_ = v___y_3118_;
v___y_3002_ = v___y_3117_;
v___y_3003_ = v___y_3119_;
goto v___jp_2993_;
}
}
else
{
if (v___y_3115_ == 0)
{
lean_object* v_c_3130_; 
lean_del_object(v___x_2991_);
v_c_3130_ = lean_ctor_get(v_c_x3f_2862_, 0);
lean_inc_ref(v_c_3130_);
lean_dec_ref_known(v_c_x3f_2862_, 2);
v___y_3009_ = v___y_3111_;
v___y_3010_ = v___y_3112_;
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v___y_3118_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v___y_3120_;
v___y_3019_ = v___y_3121_;
v___y_3020_ = v_c_3130_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
goto v___jp_3008_;
}
else
{
if (v___y_3124_ == 0)
{
lean_object* v_c_3131_; lean_object* v_numCases_3132_; 
v_c_3131_ = lean_ctor_get(v_c_x3f_2862_, 0);
v_numCases_3132_ = lean_ctor_get(v_c_x3f_2862_, 1);
lean_inc_ref(v_c_3131_);
lean_inc(v_numCases_3132_);
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v___y_3115_;
v___y_3088_ = v_numCases_3132_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3118_;
v___y_3092_ = v___y_3119_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v___y_3121_;
v___y_3095_ = v_c_3131_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3124_;
goto v___jp_3082_;
}
else
{
lean_object* v_c_3133_; 
lean_del_object(v___x_2991_);
v_c_3133_ = lean_ctor_get(v_c_x3f_2862_, 0);
lean_inc_ref(v_c_3133_);
lean_dec_ref_known(v_c_x3f_2862_, 2);
v___y_3009_ = v___y_3111_;
v___y_3010_ = v___y_3112_;
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v___y_3118_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3119_;
v___y_3018_ = v___y_3120_;
v___y_3019_ = v___y_3121_;
v___y_3020_ = v_c_3133_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
goto v___jp_3008_;
}
}
}
}
}
v___jp_3134_:
{
lean_object* v___x_3145_; 
lean_inc(v_head_2988_);
v___x_3145_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2988_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
switch(lean_obj_tag(v_a_3146_))
{
case 0:
{
lean_del_object(v___x_2991_);
lean_dec(v_head_2988_);
v_cs_2861_ = v_tail_2989_;
v_a_2864_ = v___y_3135_;
v_a_2865_ = v___y_3136_;
v_a_2866_ = v___y_3137_;
v_a_2867_ = v___y_3138_;
v_a_2868_ = v___y_3139_;
v_a_2869_ = v___y_3140_;
v_a_2870_ = v___y_3141_;
v_a_2871_ = v___y_3142_;
v_a_2872_ = v___y_3143_;
v_a_2873_ = v___y_3144_;
goto _start;
}
case 1:
{
lean_object* v___x_3148_; 
lean_del_object(v___x_2991_);
v___x_3148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_head_2988_);
lean_ctor_set(v___x_3148_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2989_;
v_cs_x27_2863_ = v___x_3148_;
v_a_2864_ = v___y_3135_;
v_a_2865_ = v___y_3136_;
v_a_2866_ = v___y_3137_;
v_a_2867_ = v___y_3138_;
v_a_2868_ = v___y_3139_;
v_a_2869_ = v___y_3140_;
v_a_2870_ = v___y_3141_;
v_a_2871_ = v___y_3142_;
v_a_2872_ = v___y_3143_;
v_a_2873_ = v___y_3144_;
goto _start;
}
default: 
{
lean_object* v_numCases_3150_; uint8_t v_isRec_3151_; uint8_t v_tryPostpone_3152_; lean_object* v___x_3153_; 
v_numCases_3150_ = lean_ctor_get(v_a_3146_, 0);
lean_inc(v_numCases_3150_);
v_isRec_3151_ = lean_ctor_get_uint8(v_a_3146_, sizeof(void*)*1);
v_tryPostpone_3152_ = lean_ctor_get_uint8(v_a_3146_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3146_, 1);
v___x_3153_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3137_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; uint8_t v___x_3155_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = lean_unbox(v_a_3154_);
lean_dec(v_a_3154_);
if (v___x_3155_ == 0)
{
v___y_3111_ = v___y_3139_;
v___y_3112_ = v___y_3141_;
v___y_3113_ = v___y_3143_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v_tryPostpone_3152_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3137_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3135_;
v___y_3120_ = v___y_3140_;
v___y_3121_ = v___y_3138_;
v___y_3122_ = v_isRec_3151_;
v___y_3123_ = v_numCases_3150_;
v___y_3124_ = v___x_3109_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_nat_dec_lt(v___x_3156_, v_numCases_3150_);
if (v___x_3157_ == 0)
{
v___y_3111_ = v___y_3139_;
v___y_3112_ = v___y_3141_;
v___y_3113_ = v___y_3143_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v_tryPostpone_3152_;
v___y_3116_ = v___y_3142_;
v___y_3117_ = v___y_3137_;
v___y_3118_ = v___y_3144_;
v___y_3119_ = v___y_3135_;
v___y_3120_ = v___y_3140_;
v___y_3121_ = v___y_3138_;
v___y_3122_ = v_isRec_3151_;
v___y_3123_ = v_numCases_3150_;
v___y_3124_ = v___x_3157_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3158_; 
lean_dec(v_numCases_3150_);
lean_del_object(v___x_2991_);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_head_2988_);
lean_ctor_set(v___x_3158_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2989_;
v_cs_x27_2863_ = v___x_3158_;
v_a_2864_ = v___y_3135_;
v_a_2865_ = v___y_3136_;
v_a_2866_ = v___y_3137_;
v_a_2867_ = v___y_3138_;
v_a_2868_ = v___y_3139_;
v_a_2869_ = v___y_3140_;
v_a_2870_ = v___y_3141_;
v_a_2871_ = v___y_3142_;
v_a_2872_ = v___y_3143_;
v_a_2873_ = v___y_3144_;
goto _start;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_numCases_3150_);
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3160_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3153_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3153_);
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
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3168_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3145_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3145_);
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
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3201_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3101_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3101_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
v___jp_2993_:
{
lean_object* v___x_3005_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v_cs_x27_2863_);
v___x_3005_ = v___x_2991_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_head_2988_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_cs_x27_2863_);
v___x_3005_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
v_cs_2861_ = v_tail_2989_;
v_cs_x27_2863_ = v___x_3005_;
v_a_2864_ = v___y_3003_;
v_a_2865_ = v___y_2998_;
v_a_2866_ = v___y_3002_;
v_a_2867_ = v___y_2999_;
v_a_2868_ = v___y_2995_;
v_a_2869_ = v___y_2994_;
v_a_2870_ = v___y_2996_;
v_a_2871_ = v___y_3000_;
v_a_2872_ = v___y_2997_;
v_a_2873_ = v___y_3001_;
goto _start;
}
}
v___jp_3008_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3023_, 0, v_head_2988_);
lean_ctor_set(v___x_3023_, 1, v___y_3022_);
lean_ctor_set_uint8(v___x_3023_, sizeof(void*)*2, v___y_3021_);
lean_ctor_set_uint8(v___x_3023_, sizeof(void*)*2 + 1, v___y_3013_);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___y_3020_);
lean_ctor_set(v___x_3024_, 1, v_cs_x27_2863_);
v_cs_2861_ = v_tail_2989_;
v_c_x3f_2862_ = v___x_3023_;
v_cs_x27_2863_ = v___x_3024_;
v_a_2864_ = v___y_3017_;
v_a_2865_ = v___y_3012_;
v_a_2866_ = v___y_3016_;
v_a_2867_ = v___y_3019_;
v_a_2868_ = v___y_3009_;
v_a_2869_ = v___y_3018_;
v_a_2870_ = v___y_3010_;
v_a_2871_ = v___y_3014_;
v_a_2872_ = v___y_3011_;
v_a_2873_ = v___y_3015_;
goto _start;
}
v___jp_3026_:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2988_, v___y_3036_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3039_, v___y_3036_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; uint8_t v___x_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_nat_dec_lt(v_a_3043_, v_a_3045_);
lean_dec(v_a_3045_);
lean_dec(v_a_3043_);
if (v___x_3046_ == 0)
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_nat_dec_lt(v___y_3041_, v___y_3032_);
lean_dec(v___y_3032_);
if (v___x_3047_ == 0)
{
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3039_);
v___y_2994_ = v___y_3037_;
v___y_2995_ = v___y_3027_;
v___y_2996_ = v___y_3028_;
v___y_2997_ = v___y_3029_;
v___y_2998_ = v___y_3030_;
v___y_2999_ = v___y_3038_;
v___y_3000_ = v___y_3033_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___y_3034_;
v___y_3003_ = v___y_3036_;
goto v___jp_2993_;
}
else
{
lean_del_object(v___x_2991_);
lean_dec(v_c_x3f_2862_);
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3028_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3035_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3041_;
goto v___jp_3008_;
}
}
else
{
lean_dec(v___y_3032_);
lean_del_object(v___x_2991_);
lean_dec(v_c_x3f_2862_);
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3028_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3035_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3041_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_3043_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3032_);
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3048_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3044_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3044_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3032_);
lean_del_object(v___x_2991_);
lean_dec(v_tail_2989_);
lean_dec(v_head_2988_);
lean_dec(v_cs_x27_2863_);
lean_dec(v_c_x3f_2862_);
v_a_3056_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3042_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3042_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
v___jp_3064_:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = lean_unsigned_to_nat(1u);
v___x_3081_ = lean_nat_dec_lt(v___x_3080_, v___y_3070_);
if (v___x_3081_ == 0)
{
v___y_3027_ = v___y_3065_;
v___y_3028_ = v___y_3066_;
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
v___y_3041_ = v___y_3079_;
goto v___jp_3026_;
}
else
{
lean_dec(v___y_3070_);
lean_del_object(v___x_2991_);
lean_dec(v_c_x3f_2862_);
v___y_3009_ = v___y_3065_;
v___y_3010_ = v___y_3066_;
v___y_3011_ = v___y_3067_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3069_;
v___y_3014_ = v___y_3071_;
v___y_3015_ = v___y_3073_;
v___y_3016_ = v___y_3072_;
v___y_3017_ = v___y_3074_;
v___y_3018_ = v___y_3075_;
v___y_3019_ = v___y_3076_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3078_;
v___y_3022_ = v___y_3079_;
goto v___jp_3008_;
}
}
v___jp_3082_:
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = lean_unsigned_to_nat(1u);
v___x_3100_ = lean_nat_dec_eq(v___y_3097_, v___x_3099_);
if (v___x_3100_ == 0)
{
v___y_3027_ = v___y_3083_;
v___y_3028_ = v___y_3084_;
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
v___y_3041_ = v___y_3097_;
goto v___jp_3026_;
}
else
{
if (v___y_3096_ == 0)
{
v___y_3065_ = v___y_3083_;
v___y_3066_ = v___y_3084_;
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
goto v___jp_3064_;
}
else
{
if (v___y_3098_ == 0)
{
v___y_3027_ = v___y_3083_;
v___y_3028_ = v___y_3084_;
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
v___y_3041_ = v___y_3097_;
goto v___jp_3026_;
}
else
{
v___y_3065_ = v___y_3083_;
v___y_3066_ = v___y_3084_;
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
goto v___jp_3064_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3210_, lean_object* v_c_x3f_3211_, lean_object* v_cs_x27_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3210_, v_c_x3f_3211_, v_cs_x27_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec(v_a_3213_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3225_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3272_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3272_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3272_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_del_object(v___x_3239_);
v___x_3242_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3225_, v_a_3227_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3259_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3259_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3259_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_unbox(v_a_3243_);
lean_dec(v_a_3243_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v_toGoalState_3249_; lean_object* v_split_3250_; lean_object* v_candidates_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_del_object(v___x_3245_);
v___x_3248_ = lean_st_ref_get(v_a_3225_);
v_toGoalState_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc_ref(v_toGoalState_3249_);
lean_dec(v___x_3248_);
v_split_3250_ = lean_ctor_get(v_toGoalState_3249_, 14);
lean_inc_ref(v_split_3250_);
lean_dec_ref(v_toGoalState_3249_);
v_candidates_3251_ = lean_ctor_get(v_split_3250_, 1);
lean_inc(v_candidates_3251_);
lean_dec_ref(v_split_3250_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_box(0);
v___x_3254_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3251_, v___x_3252_, v___x_3253_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = lean_box(0);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3255_);
v___x_3257_ = v___x_3245_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_a_3260_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3242_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3242_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3268_);
v___x_3270_ = v___x_3239_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3236_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3236_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec(v_a_3281_);
return v_res_3292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3302_ = l_Lean_mkConst(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3305_ = l_Lean_Expr_app___override(v___x_3304_, v_c_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_box(0);
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3316_ = l_Lean_mkConst(v___x_3315_, v___x_3314_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_box(0);
v___x_3323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3324_ = l_Lean_mkConst(v___x_3323_, v___x_3322_);
return v___x_3324_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_box(0);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3332_ = l_Lean_mkConst(v___x_3331_, v___x_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___y_3356_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___x_3405_; 
lean_inc_ref(v_c_3333_);
v___x_3405_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3333_, v_a_3341_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3478_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3478_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3478_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = l_Lean_Expr_cleanupAnnotations(v_a_3406_);
v___x_3411_ = l_Lean_Expr_isApp(v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec_ref(v___x_3410_);
lean_del_object(v___x_3408_);
v___y_3393_ = v_a_3334_;
v___y_3394_ = v_a_3335_;
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
goto v___jp_3392_;
}
else
{
lean_object* v_arg_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_arg_3412_ = lean_ctor_get(v___x_3410_, 1);
lean_inc_ref(v_arg_3412_);
v___x_3413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3410_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3415_ = l_Lean_Expr_isConstOf(v___x_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
uint8_t v___x_3416_; 
v___x_3416_ = l_Lean_Expr_isApp(v___x_3413_);
if (v___x_3416_ == 0)
{
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_arg_3412_);
lean_del_object(v___x_3408_);
v___y_3393_ = v_a_3334_;
v___y_3394_ = v_a_3335_;
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
goto v___jp_3392_;
}
else
{
lean_object* v_arg_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_arg_3417_ = lean_ctor_get(v___x_3413_, 1);
lean_inc_ref(v_arg_3417_);
v___x_3418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3413_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3420_ = l_Lean_Expr_isConstOf(v___x_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_Expr_isApp(v___x_3418_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v___x_3418_);
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
lean_del_object(v___x_3408_);
v___y_3393_ = v_a_3334_;
v___y_3394_ = v_a_3335_;
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
goto v___jp_3392_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3418_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3424_ = l_Lean_Expr_isConstOf(v___x_3422_, v___x_3423_);
lean_dec_ref(v___x_3422_);
if (v___x_3424_ == 0)
{
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
lean_del_object(v___x_3408_);
v___y_3393_ = v_a_3334_;
v___y_3394_ = v_a_3335_;
v___y_3395_ = v_a_3336_;
v___y_3396_ = v_a_3337_;
v___y_3397_ = v_a_3338_;
v___y_3398_ = v_a_3339_;
v___y_3399_ = v_a_3340_;
v___y_3400_ = v_a_3341_;
v___y_3401_ = v_a_3342_;
v___y_3402_ = v_a_3343_;
goto v___jp_3392_;
}
else
{
uint8_t v___x_3425_; 
lean_inc_ref(v_c_3333_);
v___x_3425_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3333_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
v___x_3426_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3333_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3426_);
v___x_3428_ = v___x_3408_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
else
{
lean_object* v___x_3430_; 
lean_del_object(v___x_3408_);
lean_inc_ref(v_c_3333_);
v___x_3430_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3333_, v_a_3334_, v_a_3338_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; uint8_t v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = lean_unbox(v_a_3431_);
lean_dec(v_a_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3443_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3443_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3443_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3439_ = l_Lean_mkApp3(v___x_3438_, v_arg_3417_, v_arg_3412_, v_a_3434_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3439_);
v___x_3441_ = v___x_3436_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
return v___x_3433_;
}
}
else
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3454_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3450_ = l_Lean_mkApp3(v___x_3449_, v_arg_3417_, v_arg_3412_, v_a_3445_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3450_);
v___x_3452_ = v___x_3447_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
return v___x_3444_;
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_c_3333_);
v_a_3455_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3430_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3430_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3463_; 
lean_dec_ref(v___x_3418_);
lean_del_object(v___x_3408_);
v___x_3463_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3473_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3469_ = l_Lean_mkApp3(v___x_3468_, v_arg_3417_, v_arg_3412_, v_a_3464_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3469_);
v___x_3471_ = v___x_3466_;
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
else
{
lean_dec_ref(v_arg_3417_);
lean_dec_ref(v_arg_3412_);
return v___x_3463_;
}
}
}
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3476_; 
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_c_3333_);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3412_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3474_);
v___x_3476_ = v___x_3408_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3333_);
return v___x_3405_;
}
v___jp_3345_:
{
if (v___y_3356_ == 0)
{
lean_object* v___x_3357_; 
lean_inc_ref(v_c_3333_);
v___x_3357_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3333_, v___y_3348_, v___y_3352_, v___y_3355_, v___y_3347_, v___y_3351_, v___y_3354_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3376_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3376_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_unbox(v_a_3358_);
lean_dec(v_a_3358_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3364_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v_c_3333_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_c_3333_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
else
{
lean_object* v___x_3366_; 
lean_del_object(v___x_3360_);
lean_inc_ref(v_c_3333_);
v___x_3366_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3333_, v___y_3348_, v___y_3353_, v___y_3350_, v___y_3346_, v___y_3352_, v___y_3349_, v___y_3355_, v___y_3347_, v___y_3351_, v___y_3354_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3375_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3333_, v_a_3367_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3371_);
v___x_3373_ = v___x_3369_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
else
{
lean_dec_ref(v_c_3333_);
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_c_3333_);
v_a_3377_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3357_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3357_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3385_ = lean_unsigned_to_nat(1u);
v___x_3386_ = l_Lean_Expr_getAppNumArgs(v_c_3333_);
v___x_3387_ = lean_nat_sub(v___x_3386_, v___x_3385_);
lean_dec(v___x_3386_);
v___x_3388_ = lean_nat_sub(v___x_3387_, v___x_3385_);
lean_dec(v___x_3387_);
v___x_3389_ = l_Lean_Expr_getRevArg_x21(v_c_3333_, v___x_3388_);
lean_dec_ref(v_c_3333_);
v___x_3390_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3389_);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
return v___x_3391_;
}
}
v___jp_3392_:
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Meta_Grind_isIte(v_c_3333_);
if (v___x_3403_ == 0)
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_Meta_Grind_isDIte(v_c_3333_);
v___y_3346_ = v___y_3396_;
v___y_3347_ = v___y_3400_;
v___y_3348_ = v___y_3393_;
v___y_3349_ = v___y_3398_;
v___y_3350_ = v___y_3395_;
v___y_3351_ = v___y_3401_;
v___y_3352_ = v___y_3397_;
v___y_3353_ = v___y_3394_;
v___y_3354_ = v___y_3402_;
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3404_;
goto v___jp_3345_;
}
else
{
v___y_3346_ = v___y_3396_;
v___y_3347_ = v___y_3400_;
v___y_3348_ = v___y_3393_;
v___y_3349_ = v___y_3398_;
v___y_3350_ = v___y_3395_;
v___y_3351_ = v___y_3401_;
v___y_3352_ = v___y_3397_;
v___y_3353_ = v___y_3394_;
v___y_3354_ = v___y_3402_;
v___y_3355_ = v___y_3399_;
v___y_3356_ = v___x_3403_;
goto v___jp_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec(v_a_3480_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3492_, lean_object* v_major_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3494_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; uint8_t v_trace_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_trace_3503_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*14);
lean_dec(v_a_3502_);
if (v_trace_3503_ == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Meta_Grind_cases(v_mvarId_3492_, v_major_3493_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; 
lean_inc(v_a_3499_);
lean_inc_ref(v_a_3498_);
lean_inc(v_a_3497_);
lean_inc_ref(v_a_3496_);
lean_inc_ref(v_major_3493_);
v___x_3505_ = lean_infer_type(v_major_3493_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v___x_3507_ = l_Lean_Meta_whnfD(v_a_3506_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l_Lean_Expr_getAppFn(v_a_3508_);
lean_dec(v_a_3508_);
if (lean_obj_tag(v___x_3509_) == 4)
{
lean_object* v_declName_3510_; lean_object* v___x_3511_; 
v_declName_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_declName_3510_);
lean_dec_ref_known(v___x_3509_, 2);
v___x_3511_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3510_, v_a_3495_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v___x_3512_; 
lean_dec_ref_known(v___x_3511_, 1);
v___x_3512_ = l_Lean_Meta_Grind_cases(v_mvarId_3492_, v_major_3493_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3512_;
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_major_3493_);
lean_dec(v_mvarId_3492_);
v_a_3513_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3511_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3511_);
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
else
{
lean_object* v___x_3521_; 
lean_dec_ref(v___x_3509_);
v___x_3521_ = l_Lean_Meta_Grind_cases(v_mvarId_3492_, v_major_3493_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3521_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v_major_3493_);
lean_dec(v_mvarId_3492_);
v_a_3522_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3507_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3507_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v_major_3493_);
lean_dec(v_mvarId_3492_);
v_a_3530_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3505_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3505_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref(v_major_3493_);
lean_dec(v_mvarId_3492_);
v_a_3538_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3501_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3501_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3546_, lean_object* v_major_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3546_, v_major_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3556_, lean_object* v_major_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3556_, v_major_3557_, v_a_3560_, v_a_3561_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3570_, lean_object* v_major_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3570_, v_major_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec(v_a_3572_);
return v_res_3583_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3584_){
_start:
{
uint64_t v_anchor_3585_; 
v_anchor_3585_ = lean_ctor_get_uint64(v_e_3584_, sizeof(void*)*3);
return v_anchor_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3586_){
_start:
{
uint64_t v_res_3587_; lean_object* v_r_3588_; 
v_res_3587_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3586_);
lean_dec_ref(v_e_3586_);
v_r_3588_ = lean_box_uint64(v_res_3587_);
return v_r_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_box(0);
return v___x_3593_;
}
else
{
lean_object* v_key_3594_; lean_object* v_value_3595_; lean_object* v_tail_3596_; uint64_t v___x_3597_; uint8_t v___x_3598_; 
v_key_3594_ = lean_ctor_get(v_x_3592_, 0);
v_value_3595_ = lean_ctor_get(v_x_3592_, 1);
v_tail_3596_ = lean_ctor_get(v_x_3592_, 2);
v___x_3597_ = lean_unbox_uint64(v_key_3594_);
v___x_3598_ = lean_uint64_dec_eq(v___x_3597_, v_a_3591_);
if (v___x_3598_ == 0)
{
v_x_3592_ = v_tail_3596_;
goto _start;
}
else
{
lean_object* v___x_3600_; 
lean_inc(v_value_3595_);
v___x_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_value_3595_);
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3601_, lean_object* v_x_3602_){
_start:
{
uint64_t v_a_boxed_3603_; lean_object* v_res_3604_; 
v_a_boxed_3603_ = lean_unbox_uint64(v_a_3601_);
lean_dec_ref(v_a_3601_);
v_res_3604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3603_, v_x_3602_);
lean_dec(v_x_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3605_, uint64_t v_a_3606_){
_start:
{
lean_object* v_buckets_3607_; lean_object* v___x_3608_; uint64_t v___x_3609_; uint64_t v___x_3610_; uint64_t v_fold_3611_; uint64_t v___x_3612_; uint64_t v___x_3613_; uint64_t v___x_3614_; size_t v___x_3615_; size_t v___x_3616_; size_t v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_buckets_3607_ = lean_ctor_get(v_m_3605_, 1);
v___x_3608_ = lean_array_get_size(v_buckets_3607_);
v___x_3609_ = 32ULL;
v___x_3610_ = lean_uint64_shift_right(v_a_3606_, v___x_3609_);
v_fold_3611_ = lean_uint64_xor(v_a_3606_, v___x_3610_);
v___x_3612_ = 16ULL;
v___x_3613_ = lean_uint64_shift_right(v_fold_3611_, v___x_3612_);
v___x_3614_ = lean_uint64_xor(v_fold_3611_, v___x_3613_);
v___x_3615_ = lean_uint64_to_usize(v___x_3614_);
v___x_3616_ = lean_usize_of_nat(v___x_3608_);
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_sub(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_usize_land(v___x_3615_, v___x_3618_);
v___x_3620_ = lean_array_uget_borrowed(v_buckets_3607_, v___x_3619_);
v___x_3621_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3606_, v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3622_, lean_object* v_a_3623_){
_start:
{
uint64_t v_a_boxed_3624_; lean_object* v_res_3625_; 
v_a_boxed_3624_ = lean_unbox_uint64(v_a_3623_);
lean_dec_ref(v_a_3623_);
v_res_3625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3622_, v_a_boxed_3624_);
lean_dec_ref(v_m_3622_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
if (lean_obj_tag(v_x_3627_) == 0)
{
return v_x_3626_;
}
else
{
lean_object* v_key_3628_; lean_object* v_value_3629_; lean_object* v_tail_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3654_; 
v_key_3628_ = lean_ctor_get(v_x_3627_, 0);
v_value_3629_ = lean_ctor_get(v_x_3627_, 1);
v_tail_3630_ = lean_ctor_get(v_x_3627_, 2);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_x_3627_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3632_ = v_x_3627_;
v_isShared_3633_ = v_isSharedCheck_3654_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_tail_3630_);
lean_inc(v_value_3629_);
lean_inc(v_key_3628_);
lean_dec(v_x_3627_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3654_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; uint64_t v___x_3635_; uint64_t v___x_3636_; uint64_t v___x_3637_; uint64_t v___x_3638_; uint64_t v_fold_3639_; uint64_t v___x_3640_; uint64_t v___x_3641_; uint64_t v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; size_t v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3634_ = lean_array_get_size(v_x_3626_);
v___x_3635_ = 32ULL;
v___x_3636_ = lean_unbox_uint64(v_key_3628_);
v___x_3637_ = lean_uint64_shift_right(v___x_3636_, v___x_3635_);
v___x_3638_ = lean_unbox_uint64(v_key_3628_);
v_fold_3639_ = lean_uint64_xor(v___x_3638_, v___x_3637_);
v___x_3640_ = 16ULL;
v___x_3641_ = lean_uint64_shift_right(v_fold_3639_, v___x_3640_);
v___x_3642_ = lean_uint64_xor(v_fold_3639_, v___x_3641_);
v___x_3643_ = lean_uint64_to_usize(v___x_3642_);
v___x_3644_ = lean_usize_of_nat(v___x_3634_);
v___x_3645_ = ((size_t)1ULL);
v___x_3646_ = lean_usize_sub(v___x_3644_, v___x_3645_);
v___x_3647_ = lean_usize_land(v___x_3643_, v___x_3646_);
v___x_3648_ = lean_array_uget_borrowed(v_x_3626_, v___x_3647_);
lean_inc(v___x_3648_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 2, v___x_3648_);
v___x_3650_ = v___x_3632_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_key_3628_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_value_3629_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_array_uset(v_x_3626_, v___x_3647_, v___x_3650_);
v_x_3626_ = v___x_3651_;
v_x_3627_ = v_tail_3630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3655_, lean_object* v_source_3656_, lean_object* v_target_3657_){
_start:
{
lean_object* v___x_3658_; uint8_t v___x_3659_; 
v___x_3658_ = lean_array_get_size(v_source_3656_);
v___x_3659_ = lean_nat_dec_lt(v_i_3655_, v___x_3658_);
if (v___x_3659_ == 0)
{
lean_dec_ref(v_source_3656_);
lean_dec(v_i_3655_);
return v_target_3657_;
}
else
{
lean_object* v_es_3660_; lean_object* v___x_3661_; lean_object* v_source_3662_; lean_object* v_target_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_es_3660_ = lean_array_fget(v_source_3656_, v_i_3655_);
v___x_3661_ = lean_box(0);
v_source_3662_ = lean_array_fset(v_source_3656_, v_i_3655_, v___x_3661_);
v_target_3663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3657_, v_es_3660_);
v___x_3664_ = lean_unsigned_to_nat(1u);
v___x_3665_ = lean_nat_add(v_i_3655_, v___x_3664_);
lean_dec(v_i_3655_);
v_i_3655_ = v___x_3665_;
v_source_3656_ = v_source_3662_;
v_target_3657_ = v_target_3663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3667_){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v_nbuckets_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3668_ = lean_array_get_size(v_data_3667_);
v___x_3669_ = lean_unsigned_to_nat(2u);
v_nbuckets_3670_ = lean_nat_mul(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_mk_array(v_nbuckets_3670_, v___x_3672_);
v___x_3674_ = lean_array_propagate_mark(v_data_3667_, v___x_3673_);
v___x_3675_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3671_, v_data_3667_, v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3676_, lean_object* v_b_3677_, lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
lean_dec(v_b_3677_);
return v_x_3678_;
}
else
{
lean_object* v_key_3679_; lean_object* v_value_3680_; lean_object* v_tail_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3695_; 
v_key_3679_ = lean_ctor_get(v_x_3678_, 0);
v_value_3680_ = lean_ctor_get(v_x_3678_, 1);
v_tail_3681_ = lean_ctor_get(v_x_3678_, 2);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_x_3678_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3683_ = v_x_3678_;
v_isShared_3684_ = v_isSharedCheck_3695_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_tail_3681_);
lean_inc(v_value_3680_);
lean_inc(v_key_3679_);
lean_dec(v_x_3678_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3695_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint64_t v___x_3685_; uint8_t v___x_3686_; 
v___x_3685_ = lean_unbox_uint64(v_key_3679_);
v___x_3686_ = lean_uint64_dec_eq(v___x_3685_, v_a_3676_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3676_, v_b_3677_, v_tail_3681_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 2, v___x_3687_);
v___x_3689_ = v___x_3683_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_key_3679_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_value_3680_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_dec(v_value_3680_);
lean_dec(v_key_3679_);
v___x_3691_ = lean_box_uint64(v_a_3676_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 1, v_b_3677_);
lean_ctor_set(v___x_3683_, 0, v___x_3691_);
v___x_3693_ = v___x_3683_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_b_3677_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_tail_3681_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3696_, lean_object* v_b_3697_, lean_object* v_x_3698_){
_start:
{
uint64_t v_a_boxed_3699_; lean_object* v_res_3700_; 
v_a_boxed_3699_ = lean_unbox_uint64(v_a_3696_);
lean_dec_ref(v_a_3696_);
v_res_3700_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3699_, v_b_3697_, v_x_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3701_, lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
uint8_t v___x_3703_; 
v___x_3703_ = 0;
return v___x_3703_;
}
else
{
lean_object* v_key_3704_; lean_object* v_tail_3705_; uint64_t v___x_3706_; uint8_t v___x_3707_; 
v_key_3704_ = lean_ctor_get(v_x_3702_, 0);
v_tail_3705_ = lean_ctor_get(v_x_3702_, 2);
v___x_3706_ = lean_unbox_uint64(v_key_3704_);
v___x_3707_ = lean_uint64_dec_eq(v___x_3706_, v_a_3701_);
if (v___x_3707_ == 0)
{
v_x_3702_ = v_tail_3705_;
goto _start;
}
else
{
return v___x_3707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3709_, lean_object* v_x_3710_){
_start:
{
uint64_t v_a_boxed_3711_; uint8_t v_res_3712_; lean_object* v_r_3713_; 
v_a_boxed_3711_ = lean_unbox_uint64(v_a_3709_);
lean_dec_ref(v_a_3709_);
v_res_3712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3711_, v_x_3710_);
lean_dec(v_x_3710_);
v_r_3713_ = lean_box(v_res_3712_);
return v_r_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3714_, uint64_t v_a_3715_, lean_object* v_b_3716_){
_start:
{
lean_object* v_size_3717_; lean_object* v_buckets_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3761_; 
v_size_3717_ = lean_ctor_get(v_m_3714_, 0);
v_buckets_3718_ = lean_ctor_get(v_m_3714_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_m_3714_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3720_ = v_m_3714_;
v_isShared_3721_ = v_isSharedCheck_3761_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_buckets_3718_);
lean_inc(v_size_3717_);
lean_dec(v_m_3714_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3761_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; uint64_t v___x_3723_; uint64_t v___x_3724_; uint64_t v_fold_3725_; uint64_t v___x_3726_; uint64_t v___x_3727_; uint64_t v___x_3728_; size_t v___x_3729_; size_t v___x_3730_; size_t v___x_3731_; size_t v___x_3732_; size_t v___x_3733_; lean_object* v_bkt_3734_; uint8_t v___x_3735_; 
v___x_3722_ = lean_array_get_size(v_buckets_3718_);
v___x_3723_ = 32ULL;
v___x_3724_ = lean_uint64_shift_right(v_a_3715_, v___x_3723_);
v_fold_3725_ = lean_uint64_xor(v_a_3715_, v___x_3724_);
v___x_3726_ = 16ULL;
v___x_3727_ = lean_uint64_shift_right(v_fold_3725_, v___x_3726_);
v___x_3728_ = lean_uint64_xor(v_fold_3725_, v___x_3727_);
v___x_3729_ = lean_uint64_to_usize(v___x_3728_);
v___x_3730_ = lean_usize_of_nat(v___x_3722_);
v___x_3731_ = ((size_t)1ULL);
v___x_3732_ = lean_usize_sub(v___x_3730_, v___x_3731_);
v___x_3733_ = lean_usize_land(v___x_3729_, v___x_3732_);
v_bkt_3734_ = lean_array_uget_borrowed(v_buckets_3718_, v___x_3733_);
v___x_3735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3715_, v_bkt_3734_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; lean_object* v_size_x27_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_buckets_x27_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3736_ = lean_unsigned_to_nat(1u);
v_size_x27_3737_ = lean_nat_add(v_size_3717_, v___x_3736_);
lean_dec(v_size_3717_);
v___x_3738_ = lean_box_uint64(v_a_3715_);
lean_inc(v_bkt_3734_);
v___x_3739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v_b_3716_);
lean_ctor_set(v___x_3739_, 2, v_bkt_3734_);
v_buckets_x27_3740_ = lean_array_uset(v_buckets_3718_, v___x_3733_, v___x_3739_);
v___x_3741_ = lean_unsigned_to_nat(4u);
v___x_3742_ = lean_nat_mul(v_size_x27_3737_, v___x_3741_);
v___x_3743_ = lean_unsigned_to_nat(3u);
v___x_3744_ = lean_nat_div(v___x_3742_, v___x_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_array_get_size(v_buckets_x27_3740_);
v___x_3746_ = lean_nat_dec_le(v___x_3744_, v___x_3745_);
lean_dec(v___x_3744_);
if (v___x_3746_ == 0)
{
lean_object* v_val_3747_; lean_object* v___x_3749_; 
v_val_3747_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3740_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 1, v_val_3747_);
lean_ctor_set(v___x_3720_, 0, v_size_x27_3737_);
v___x_3749_ = v___x_3720_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_size_x27_3737_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_val_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
else
{
lean_object* v___x_3752_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 1, v_buckets_x27_3740_);
lean_ctor_set(v___x_3720_, 0, v_size_x27_3737_);
v___x_3752_ = v___x_3720_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_size_x27_3737_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_buckets_x27_3740_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_object* v___x_3754_; lean_object* v_buckets_x27_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_inc(v_bkt_3734_);
v___x_3754_ = lean_box(0);
v_buckets_x27_3755_ = lean_array_uset(v_buckets_3718_, v___x_3733_, v___x_3754_);
v___x_3756_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3715_, v_b_3716_, v_bkt_3734_);
v___x_3757_ = lean_array_uset(v_buckets_x27_3755_, v___x_3733_, v___x_3756_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 1, v___x_3757_);
v___x_3759_ = v___x_3720_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_size_3717_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3762_, lean_object* v_a_3763_, lean_object* v_b_3764_){
_start:
{
uint64_t v_a_boxed_3765_; lean_object* v_res_3766_; 
v_a_boxed_3765_ = lean_unbox_uint64(v_a_3763_);
lean_dec_ref(v_a_3763_);
v_res_3766_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3762_, v_a_boxed_3765_, v_b_3764_);
return v_res_3766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_unsigned_to_nat(16u);
v___x_3769_ = lean_mk_array(v___x_3768_, v___x_3767_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v_found_3772_; 
v___x_3770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3771_ = lean_unsigned_to_nat(0u);
v_found_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3772_, 0, v___x_3771_);
lean_ctor_set(v_found_3772_, 1, v___x_3770_);
return v_found_3772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v_found_3773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3774_ = lean_box(0);
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
lean_ctor_set(v___x_3775_, 1, v_found_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3776_, lean_object* v_numDigits_3777_, lean_object* v_es_3778_, lean_object* v_as_3779_, size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_b_3782_){
_start:
{
lean_object* v_a_3784_; uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3788_ == 0)
{
return v_b_3782_;
}
else
{
lean_object* v_snd_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3823_; 
v_snd_3789_ = lean_ctor_get(v_b_3782_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_b_3782_);
if (v_isSharedCheck_3823_ == 0)
{
lean_object* v_unused_3824_; 
v_unused_3824_ = lean_ctor_get(v_b_3782_, 0);
lean_dec(v_unused_3824_);
v___x_3791_ = v_b_3782_;
v_isShared_3792_ = v_isSharedCheck_3823_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_snd_3789_);
lean_dec(v_b_3782_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3823_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_a_3793_; uint64_t v_anchor_3794_; lean_object* v___x_3795_; uint64_t v___x_3796_; uint64_t v___x_3797_; lean_object* v___x_3798_; 
v_a_3793_ = lean_array_uget_borrowed(v_as_3779_, v_i_3781_);
v_anchor_3794_ = lean_ctor_get_uint64(v_a_3793_, sizeof(void*)*3);
v___x_3795_ = lean_box(0);
v___x_3796_ = lean_uint64_of_nat(v_shift_3776_);
v___x_3797_ = lean_uint64_shift_right(v_anchor_3794_, v___x_3796_);
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3789_, v___x_3797_);
if (lean_obj_tag(v___x_3798_) == 1)
{
lean_object* v_val_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3817_; 
v_val_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3817_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_val_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3817_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
uint64_t v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = lean_unbox_uint64(v_val_3799_);
lean_dec(v_val_3799_);
v___x_3804_ = lean_uint64_dec_eq(v___x_3803_, v_anchor_3794_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3805_ = lean_unsigned_to_nat(1u);
v___x_3806_ = lean_nat_add(v_numDigits_3777_, v___x_3805_);
v___x_3807_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3778_, v___x_3806_);
lean_dec(v___x_3806_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3807_);
v___x_3809_ = v___x_3801_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3809_);
v___x_3811_ = v___x_3791_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_snd_3789_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
lean_object* v___x_3815_; 
lean_del_object(v___x_3801_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3795_);
v___x_3815_ = v___x_3791_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_snd_3789_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v_a_3784_ = v___x_3815_;
goto v___jp_3783_;
}
}
}
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
lean_dec(v___x_3798_);
v___x_3818_ = lean_box_uint64(v_anchor_3794_);
v___x_3819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3789_, v___x_3797_, v___x_3818_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 1, v___x_3819_);
lean_ctor_set(v___x_3791_, 0, v___x_3795_);
v___x_3821_ = v___x_3791_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
v_a_3784_ = v___x_3821_;
goto v___jp_3783_;
}
}
}
}
v___jp_3783_:
{
size_t v___x_3785_; size_t v___x_3786_; 
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3781_, v___x_3785_);
v_i_3781_ = v___x_3786_;
v_b_3782_ = v_a_3784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3825_, lean_object* v_numDigits_3826_){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3827_ = lean_unsigned_to_nat(4u);
v___x_3828_ = lean_nat_mul(v___x_3827_, v_numDigits_3826_);
v___x_3829_ = lean_unsigned_to_nat(64u);
v___x_3830_ = lean_nat_dec_lt(v___x_3828_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_dec(v___x_3828_);
lean_inc(v_numDigits_3826_);
return v_numDigits_3826_;
}
else
{
lean_object* v_shift_3831_; lean_object* v___x_3832_; size_t v_sz_3833_; size_t v___x_3834_; lean_object* v___x_3835_; lean_object* v_fst_3836_; 
v_shift_3831_ = lean_nat_sub(v___x_3829_, v___x_3828_);
lean_dec(v___x_3828_);
v___x_3832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3833_ = lean_array_size(v_es_3825_);
v___x_3834_ = ((size_t)0ULL);
v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3831_, v_numDigits_3826_, v_es_3825_, v_es_3825_, v_sz_3833_, v___x_3834_, v___x_3832_);
lean_dec(v_shift_3831_);
v_fst_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_fst_3836_);
lean_dec_ref(v___x_3835_);
if (lean_obj_tag(v_fst_3836_) == 0)
{
lean_inc(v_numDigits_3826_);
return v_numDigits_3826_;
}
else
{
lean_object* v_val_3837_; 
v_val_3837_ = lean_ctor_get(v_fst_3836_, 0);
lean_inc(v_val_3837_);
lean_dec_ref_known(v_fst_3836_, 1);
return v_val_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3838_, lean_object* v_numDigits_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3838_, v_numDigits_3839_);
lean_dec(v_numDigits_3839_);
lean_dec_ref(v_es_3838_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3841_, lean_object* v_numDigits_3842_, lean_object* v_es_3843_, lean_object* v_as_3844_, lean_object* v_sz_3845_, lean_object* v_i_3846_, lean_object* v_b_3847_){
_start:
{
size_t v_sz_boxed_3848_; size_t v_i_boxed_3849_; lean_object* v_res_3850_; 
v_sz_boxed_3848_ = lean_unbox_usize(v_sz_3845_);
lean_dec(v_sz_3845_);
v_i_boxed_3849_ = lean_unbox_usize(v_i_3846_);
lean_dec(v_i_3846_);
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3841_, v_numDigits_3842_, v_es_3843_, v_as_3844_, v_sz_boxed_3848_, v_i_boxed_3849_, v_b_3847_);
lean_dec_ref(v_as_3844_);
lean_dec_ref(v_es_3843_);
lean_dec(v_numDigits_3842_);
lean_dec(v_shift_3841_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3851_){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_unsigned_to_nat(4u);
v___x_3853_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3851_, v___x_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3854_);
lean_dec_ref(v_es_3854_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3856_, lean_object* v_as_3857_, size_t v_i_3858_, size_t v_stop_3859_, lean_object* v_b_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_a_3873_; uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_eq(v_i_3858_, v_stop_3859_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v_e_3879_; lean_object* v___x_3880_; 
v___x_3878_ = lean_array_uget_borrowed(v_as_3857_, v_i_3858_);
v_e_3879_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3878_);
v___x_3880_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3878_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
lean_inc(v___x_3878_);
v___x_3882_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3878_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
if (lean_obj_tag(v_a_3883_) == 2)
{
lean_object* v_numCases_3884_; uint8_t v_isRec_3885_; lean_object* v___x_3886_; 
v_numCases_3884_ = lean_ctor_get(v_a_3883_, 0);
lean_inc(v_numCases_3884_);
v_isRec_3885_ = lean_ctor_get_uint8(v_a_3883_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3883_, 1);
lean_inc_ref(v_filter_3856_);
lean_inc(v___y_3870_);
lean_inc_ref(v___y_3869_);
lean_inc(v___y_3868_);
lean_inc_ref(v___y_3867_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc(v___y_3862_);
lean_inc(v___y_3861_);
lean_inc_ref(v_e_3879_);
v___x_3886_ = lean_apply_12(v_filter_3856_, v_e_3879_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, lean_box(0));
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; uint8_t v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_unbox(v_a_3887_);
lean_dec(v_a_3887_);
if (v___x_3888_ == 0)
{
lean_dec(v_numCases_3884_);
lean_dec(v_a_3881_);
lean_dec_ref(v_e_3879_);
v_a_3873_ = v_b_3860_;
goto v___jp_3872_;
}
else
{
lean_object* v___x_3889_; uint64_t v___x_3890_; lean_object* v___x_3891_; 
lean_inc(v___x_3878_);
v___x_3889_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3889_, 0, v___x_3878_);
lean_ctor_set(v___x_3889_, 1, v_numCases_3884_);
lean_ctor_set(v___x_3889_, 2, v_e_3879_);
lean_ctor_set_uint8(v___x_3889_, sizeof(void*)*3 + 8, v_isRec_3885_);
v___x_3890_ = lean_unbox_uint64(v_a_3881_);
lean_dec(v_a_3881_);
lean_ctor_set_uint64(v___x_3889_, sizeof(void*)*3, v___x_3890_);
v___x_3891_ = lean_array_push(v_b_3860_, v___x_3889_);
v_a_3873_ = v___x_3891_;
goto v___jp_3872_;
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v_numCases_3884_);
lean_dec(v_a_3881_);
lean_dec_ref(v_e_3879_);
lean_dec_ref(v_b_3860_);
lean_dec_ref(v_filter_3856_);
v_a_3892_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3886_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3886_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_dec(v_a_3883_);
lean_dec(v_a_3881_);
lean_dec_ref(v_e_3879_);
v_a_3873_ = v_b_3860_;
goto v___jp_3872_;
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v_a_3881_);
lean_dec_ref(v_e_3879_);
lean_dec_ref(v_b_3860_);
lean_dec_ref(v_filter_3856_);
v_a_3900_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3882_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3882_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_e_3879_);
lean_dec_ref(v_b_3860_);
lean_dec_ref(v_filter_3856_);
v_a_3908_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3880_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3880_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v___x_3916_; 
lean_dec_ref(v_filter_3856_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_b_3860_);
return v___x_3916_;
}
v___jp_3872_:
{
size_t v___x_3874_; size_t v___x_3875_; 
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3858_, v___x_3874_);
v_i_3858_ = v___x_3875_;
v_b_3860_ = v_a_3873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3917_, lean_object* v_as_3918_, lean_object* v_i_3919_, lean_object* v_stop_3920_, lean_object* v_b_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
size_t v_i_boxed_3933_; size_t v_stop_boxed_3934_; lean_object* v_res_3935_; 
v_i_boxed_3933_ = lean_unbox_usize(v_i_3919_);
lean_dec(v_i_3919_);
v_stop_boxed_3934_ = lean_unbox_usize(v_stop_3920_);
lean_dec(v_stop_3920_);
v_res_3935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3917_, v_as_3918_, v_i_boxed_3933_, v_stop_boxed_3934_, v_b_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v_as_3918_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3938_, lean_object* v_as_3939_, lean_object* v_start_3940_, lean_object* v_stop_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3953_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3954_ = lean_nat_dec_lt(v_start_3940_, v_stop_3941_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
lean_dec_ref(v_filter_3938_);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = lean_array_get_size(v_as_3939_);
v___x_3957_ = lean_nat_dec_le(v_stop_3941_, v___x_3956_);
if (v___x_3957_ == 0)
{
uint8_t v___x_3958_; 
v___x_3958_ = lean_nat_dec_lt(v_start_3940_, v___x_3956_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec_ref(v_filter_3938_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3953_);
return v___x_3959_;
}
else
{
size_t v___x_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_usize_of_nat(v_start_3940_);
v___x_3961_ = lean_usize_of_nat(v___x_3956_);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3938_, v_as_3939_, v___x_3960_, v___x_3961_, v___x_3953_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3962_;
}
}
else
{
size_t v___x_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_usize_of_nat(v_start_3940_);
v___x_3964_ = lean_usize_of_nat(v_stop_3941_);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3938_, v_as_3939_, v___x_3963_, v___x_3964_, v___x_3953_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3966_, lean_object* v_as_3967_, lean_object* v_start_3968_, lean_object* v_stop_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3966_, v_as_3967_, v_start_3968_, v_stop_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec(v_stop_3969_);
lean_dec(v_start_3968_);
lean_dec_ref(v_as_3967_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3982_, lean_object* v_candidates_x3f_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_candidates_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; 
if (lean_obj_tag(v_candidates_x3f_3983_) == 0)
{
lean_object* v___x_4029_; lean_object* v_toGoalState_4030_; lean_object* v_split_4031_; lean_object* v_candidates_4032_; 
v___x_4029_ = lean_st_ref_get(v_a_3984_);
v_toGoalState_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc_ref(v_toGoalState_4030_);
lean_dec(v___x_4029_);
v_split_4031_ = lean_ctor_get(v_toGoalState_4030_, 14);
lean_inc_ref(v_split_4031_);
lean_dec_ref(v_toGoalState_4030_);
v_candidates_4032_ = lean_ctor_get(v_split_4031_, 1);
lean_inc(v_candidates_4032_);
lean_dec_ref(v_split_4031_);
v_candidates_3996_ = v_candidates_4032_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
v___y_4003_ = v_a_3990_;
v___y_4004_ = v_a_3991_;
v___y_4005_ = v_a_3992_;
v___y_4006_ = v_a_3993_;
goto v___jp_3995_;
}
else
{
lean_object* v_val_4033_; 
v_val_4033_ = lean_ctor_get(v_candidates_x3f_3983_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v_candidates_x3f_3983_, 1);
v_candidates_3996_ = v_val_4033_;
v___y_3997_ = v_a_3984_;
v___y_3998_ = v_a_3985_;
v___y_3999_ = v_a_3986_;
v___y_4000_ = v_a_3987_;
v___y_4001_ = v_a_3988_;
v___y_4002_ = v_a_3989_;
v___y_4003_ = v_a_3990_;
v___y_4004_ = v_a_3991_;
v___y_4005_ = v_a_3992_;
v___y_4006_ = v_a_3993_;
goto v___jp_3995_;
}
v___jp_3995_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4007_ = lean_array_mk(v_candidates_3996_);
v___x_4008_ = lean_unsigned_to_nat(0u);
v___x_4009_ = lean_array_get_size(v___x_4007_);
v___x_4010_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3982_, v___x_4007_, v___x_4008_, v___x_4009_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec_ref(v___x_4007_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4020_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4020_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4020_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4015_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4011_);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v_a_4011_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4016_);
v___x_4018_ = v___x_4013_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
v_a_4021_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4010_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4010_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4034_, lean_object* v_candidates_x3f_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4034_, v_candidates_x3f_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
lean_dec(v_a_4036_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4048_, lean_object* v_m_4049_, uint64_t v_a_4050_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4049_, v_a_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4052_, lean_object* v_m_4053_, lean_object* v_a_4054_){
_start:
{
uint64_t v_a_boxed_4055_; lean_object* v_res_4056_; 
v_a_boxed_4055_ = lean_unbox_uint64(v_a_4054_);
lean_dec_ref(v_a_4054_);
v_res_4056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4052_, v_m_4053_, v_a_boxed_4055_);
lean_dec_ref(v_m_4053_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4057_, lean_object* v_m_4058_, uint64_t v_a_4059_, lean_object* v_b_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4058_, v_a_4059_, v_b_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4062_, lean_object* v_m_4063_, lean_object* v_a_4064_, lean_object* v_b_4065_){
_start:
{
uint64_t v_a_boxed_4066_; lean_object* v_res_4067_; 
v_a_boxed_4066_ = lean_unbox_uint64(v_a_4064_);
lean_dec_ref(v_a_4064_);
v_res_4067_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4062_, v_m_4063_, v_a_boxed_4066_, v_b_4065_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4068_, uint64_t v_a_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4069_, v_x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4072_, lean_object* v_a_4073_, lean_object* v_x_4074_){
_start:
{
uint64_t v_a_boxed_4075_; lean_object* v_res_4076_; 
v_a_boxed_4075_ = lean_unbox_uint64(v_a_4073_);
lean_dec_ref(v_a_4073_);
v_res_4076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4072_, v_a_boxed_4075_, v_x_4074_);
lean_dec(v_x_4074_);
return v_res_4076_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4077_, uint64_t v_a_4078_, lean_object* v_x_4079_){
_start:
{
uint8_t v___x_4080_; 
v___x_4080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4078_, v_x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4081_, lean_object* v_a_4082_, lean_object* v_x_4083_){
_start:
{
uint64_t v_a_boxed_4084_; uint8_t v_res_4085_; lean_object* v_r_4086_; 
v_a_boxed_4084_ = lean_unbox_uint64(v_a_4082_);
lean_dec_ref(v_a_4082_);
v_res_4085_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4081_, v_a_boxed_4084_, v_x_4083_);
lean_dec(v_x_4083_);
v_r_4086_ = lean_box(v_res_4085_);
return v_r_4086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4087_, lean_object* v_data_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4090_, uint64_t v_a_4091_, lean_object* v_b_4092_, lean_object* v_x_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4091_, v_b_4092_, v_x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4095_, lean_object* v_a_4096_, lean_object* v_b_4097_, lean_object* v_x_4098_){
_start:
{
uint64_t v_a_boxed_4099_; lean_object* v_res_4100_; 
v_a_boxed_4099_ = lean_unbox_uint64(v_a_4096_);
lean_dec_ref(v_a_4096_);
v_res_4100_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4095_, v_a_boxed_4099_, v_b_4097_, v_x_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4101_, lean_object* v_i_4102_, lean_object* v_source_4103_, lean_object* v_target_4104_){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4102_, v_source_4103_, v_target_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4106_, lean_object* v_x_4107_, lean_object* v_x_4108_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4107_, v_x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = 1;
v___x_4123_ = lean_box(v___x_4122_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v_x_4125_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4138_, uint64_t v_a_4139_, lean_object* v_c_4140_, lean_object* v_numDigits_4141_, lean_object* v_as_4142_, size_t v_sz_4143_, size_t v_i_4144_, lean_object* v_b_4145_){
_start:
{
lean_object* v_a_4148_; uint8_t v___x_4152_; 
v___x_4152_ = lean_usize_dec_lt(v_i_4144_, v_sz_4143_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec(v_numDigits_4141_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_b_4145_);
return v___x_4153_;
}
else
{
lean_object* v_snd_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4180_; 
v_snd_4154_ = lean_ctor_get(v_b_4145_, 1);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_b_4145_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v_b_4145_, 0);
lean_dec(v_unused_4181_);
v___x_4156_ = v_b_4145_;
v_isShared_4157_ = v_isSharedCheck_4180_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_snd_4154_);
lean_dec(v_b_4145_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4180_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v_a_4158_; lean_object* v_c_4159_; uint64_t v_anchor_4160_; lean_object* v___x_4161_; uint64_t v___x_4162_; uint64_t v___x_4163_; uint8_t v___x_4164_; 
v_a_4158_ = lean_array_uget_borrowed(v_as_4142_, v_i_4144_);
v_c_4159_ = lean_ctor_get(v_a_4158_, 0);
v_anchor_4160_ = lean_ctor_get_uint64(v_a_4158_, sizeof(void*)*3);
v___x_4161_ = lean_box(0);
v___x_4162_ = lean_uint64_shift_right(v_anchor_4160_, v___x_4138_);
v___x_4163_ = lean_uint64_shift_right(v_a_4139_, v___x_4138_);
v___x_4164_ = lean_uint64_dec_eq(v___x_4162_, v___x_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4166_; 
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4161_);
v___x_4166_ = v___x_4156_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_snd_4154_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
v_a_4148_ = v___x_4166_;
goto v___jp_4147_;
}
}
else
{
uint8_t v___x_4168_; 
v___x_4168_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4159_, v_c_4140_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4169_ = lean_unsigned_to_nat(1u);
v___x_4170_ = lean_nat_add(v_snd_4154_, v___x_4169_);
lean_dec(v_snd_4154_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 1, v___x_4170_);
lean_ctor_set(v___x_4156_, 0, v___x_4161_);
v___x_4172_ = v___x_4156_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
v_a_4148_ = v___x_4172_;
goto v___jp_4147_;
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
lean_inc(v_snd_4154_);
v___x_4174_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4174_, 0, v_numDigits_4141_);
lean_ctor_set(v___x_4174_, 1, v_snd_4154_);
lean_ctor_set_uint64(v___x_4174_, sizeof(void*)*2, v_a_4139_);
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4175_);
v___x_4177_ = v___x_4156_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_snd_4154_);
v___x_4177_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
}
}
}
v___jp_4147_:
{
size_t v___x_4149_; size_t v___x_4150_; 
v___x_4149_ = ((size_t)1ULL);
v___x_4150_ = lean_usize_add(v_i_4144_, v___x_4149_);
v_i_4144_ = v___x_4150_;
v_b_4145_ = v_a_4148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4182_, lean_object* v_a_4183_, lean_object* v_c_4184_, lean_object* v_numDigits_4185_, lean_object* v_as_4186_, lean_object* v_sz_4187_, lean_object* v_i_4188_, lean_object* v_b_4189_, lean_object* v___y_4190_){
_start:
{
uint64_t v___x_7681__boxed_4191_; uint64_t v_a_7682__boxed_4192_; size_t v_sz_boxed_4193_; size_t v_i_boxed_4194_; lean_object* v_res_4195_; 
v___x_7681__boxed_4191_ = lean_unbox_uint64(v___x_4182_);
lean_dec_ref(v___x_4182_);
v_a_7682__boxed_4192_ = lean_unbox_uint64(v_a_4183_);
lean_dec_ref(v_a_4183_);
v_sz_boxed_4193_ = lean_unbox_usize(v_sz_4187_);
lean_dec(v_sz_4187_);
v_i_boxed_4194_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7681__boxed_4191_, v_a_7682__boxed_4192_, v_c_4184_, v_numDigits_4185_, v_as_4186_, v_sz_boxed_4193_, v_i_boxed_4194_, v_b_4189_);
lean_dec_ref(v_as_4186_);
lean_dec_ref(v_c_4184_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4200_, lean_object* v_candidates_x3f_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v___f_4213_; lean_object* v___x_4214_; 
v___f_4213_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4214_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4213_, v_candidates_x3f_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v_candidates_4216_; lean_object* v_numDigits_4217_; lean_object* v___x_4218_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v_candidates_4216_ = lean_ctor_get(v_a_4215_, 0);
lean_inc_ref(v_candidates_4216_);
v_numDigits_4217_ = lean_ctor_get(v_a_4215_, 1);
lean_inc(v_numDigits_4217_);
lean_dec(v_a_4215_);
v___x_4218_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4200_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; uint64_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; size_t v_sz_4227_; size_t v___x_4228_; uint64_t v___x_4229_; lean_object* v___x_4230_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
lean_dec_ref_known(v___x_4218_, 1);
v___x_4220_ = lean_unsigned_to_nat(64u);
v___x_4221_ = lean_unsigned_to_nat(4u);
v___x_4222_ = lean_nat_mul(v___x_4221_, v_numDigits_4217_);
v___x_4223_ = lean_nat_sub(v___x_4220_, v___x_4222_);
lean_dec(v___x_4222_);
v___x_4224_ = lean_uint64_of_nat(v___x_4223_);
lean_dec(v___x_4223_);
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4227_ = lean_array_size(v_candidates_4216_);
v___x_4228_ = ((size_t)0ULL);
v___x_4229_ = lean_unbox_uint64(v_a_4219_);
lean_inc(v_numDigits_4217_);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4224_, v___x_4229_, v_c_4200_, v_numDigits_4217_, v_candidates_4216_, v_sz_4227_, v___x_4228_, v___x_4226_);
lean_dec_ref(v_candidates_4216_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4245_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4233_ = v___x_4230_;
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v_fst_4235_; 
v_fst_4235_ = lean_ctor_get(v_a_4231_, 0);
lean_inc(v_fst_4235_);
lean_dec(v_a_4231_);
if (lean_obj_tag(v_fst_4235_) == 0)
{
lean_object* v___x_4236_; uint64_t v___x_4237_; lean_object* v___x_4239_; 
v___x_4236_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4236_, 0, v_numDigits_4217_);
lean_ctor_set(v___x_4236_, 1, v___x_4225_);
v___x_4237_ = lean_unbox_uint64(v_a_4219_);
lean_dec(v_a_4219_);
lean_ctor_set_uint64(v___x_4236_, sizeof(void*)*2, v___x_4237_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4236_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4236_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
else
{
lean_object* v_val_4241_; lean_object* v___x_4243_; 
lean_dec(v_a_4219_);
lean_dec(v_numDigits_4217_);
v_val_4241_ = lean_ctor_get(v_fst_4235_, 0);
lean_inc(v_val_4241_);
lean_dec_ref_known(v_fst_4235_, 1);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v_val_4241_);
v___x_4243_ = v___x_4233_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_val_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec(v_a_4219_);
lean_dec(v_numDigits_4217_);
v_a_4246_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4230_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4230_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec(v_numDigits_4217_);
lean_dec_ref(v_candidates_4216_);
v_a_4254_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4218_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4218_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4214_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4214_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4270_, lean_object* v_candidates_x3f_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4270_, v_candidates_x3f_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec_ref(v_c_4270_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4284_, uint64_t v_a_4285_, lean_object* v_c_4286_, lean_object* v_numDigits_4287_, lean_object* v_as_4288_, size_t v_sz_4289_, size_t v_i_4290_, lean_object* v_b_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4284_, v_a_4285_, v_c_4286_, v_numDigits_4287_, v_as_4288_, v_sz_4289_, v_i_4290_, v_b_4291_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4304_ = _args[0];
lean_object* v_a_4305_ = _args[1];
lean_object* v_c_4306_ = _args[2];
lean_object* v_numDigits_4307_ = _args[3];
lean_object* v_as_4308_ = _args[4];
lean_object* v_sz_4309_ = _args[5];
lean_object* v_i_4310_ = _args[6];
lean_object* v_b_4311_ = _args[7];
lean_object* v___y_4312_ = _args[8];
lean_object* v___y_4313_ = _args[9];
lean_object* v___y_4314_ = _args[10];
lean_object* v___y_4315_ = _args[11];
lean_object* v___y_4316_ = _args[12];
lean_object* v___y_4317_ = _args[13];
lean_object* v___y_4318_ = _args[14];
lean_object* v___y_4319_ = _args[15];
lean_object* v___y_4320_ = _args[16];
lean_object* v___y_4321_ = _args[17];
lean_object* v___y_4322_ = _args[18];
_start:
{
uint64_t v___x_7880__boxed_4323_; uint64_t v_a_7881__boxed_4324_; size_t v_sz_boxed_4325_; size_t v_i_boxed_4326_; lean_object* v_res_4327_; 
v___x_7880__boxed_4323_ = lean_unbox_uint64(v___x_4304_);
lean_dec_ref(v___x_4304_);
v_a_7881__boxed_4324_ = lean_unbox_uint64(v_a_4305_);
lean_dec_ref(v_a_4305_);
v_sz_boxed_4325_ = lean_unbox_usize(v_sz_4309_);
lean_dec(v_sz_4309_);
v_i_boxed_4326_ = lean_unbox_usize(v_i_4310_);
lean_dec(v_i_4310_);
v_res_4327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7880__boxed_4323_, v_a_7881__boxed_4324_, v_c_4306_, v_numDigits_4307_, v_as_4308_, v_sz_boxed_4325_, v_i_boxed_4326_, v_b_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v_as_4308_);
lean_dec_ref(v_c_4306_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_numDigits_4355_; uint64_t v_anchor_4356_; lean_object* v_ordinal_4357_; lean_object* v___x_4358_; 
v_numDigits_4355_ = lean_ctor_get(v_info_4352_, 0);
v_anchor_4356_ = lean_ctor_get_uint64(v_info_4352_, sizeof(void*)*2);
v_ordinal_4357_ = lean_ctor_get(v_info_4352_, 1);
v___x_4358_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4355_, v_anchor_4356_, v_a_4353_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4395_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4395_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4395_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = lean_nat_dec_eq(v_ordinal_4357_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_object* v_ref_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v_ref_4365_ = lean_ctor_get(v_a_4353_, 2);
v___x_4366_ = l_Lean_SourceInfo_fromRef(v_ref_4365_, v___x_4364_);
v___x_4367_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4368_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4366_, 3);
v___x_4369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4366_);
lean_ctor_set(v___x_4369_, 1, v___x_4367_);
v___x_4370_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4371_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4366_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_unsigned_to_nat(1u);
v___x_4374_ = lean_nat_add(v_ordinal_4357_, v___x_4373_);
v___x_4375_ = l_Nat_reprFast(v___x_4374_);
v___x_4376_ = lean_box(2);
v___x_4377_ = l_Lean_Syntax_mkNumLit(v___x_4375_, v___x_4376_);
v___x_4378_ = l_Lean_Syntax_node3(v___x_4366_, v___x_4370_, v_a_4359_, v___x_4372_, v___x_4377_);
v___x_4379_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4368_, v___x_4369_, v___x_4378_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4379_);
v___x_4381_ = v___x_4361_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
else
{
lean_object* v_ref_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v_ref_4383_ = lean_ctor_get(v_a_4353_, 2);
v___x_4384_ = 0;
v___x_4385_ = l_Lean_SourceInfo_fromRef(v_ref_4383_, v___x_4384_);
v___x_4386_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4387_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4385_, 2);
v___x_4388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4385_);
lean_ctor_set(v___x_4388_, 1, v___x_4386_);
v___x_4389_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4390_ = l_Lean_Syntax_node1(v___x_4385_, v___x_4389_, v_a_4359_);
v___x_4391_ = l_Lean_Syntax_node2(v___x_4385_, v___x_4387_, v___x_4388_, v___x_4390_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4391_);
v___x_4393_ = v___x_4361_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
else
{
return v___x_4358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4396_, v_a_4397_);
lean_dec_ref(v_a_4397_);
lean_dec_ref(v_info_4396_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4400_, v_a_4401_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4405_, v_a_4406_, v_a_4407_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec_ref(v_info_4405_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v_p_4441_; lean_object* v___x_4444_; 
lean_inc_ref(v_proof_4422_);
v___x_4444_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4422_, v_a_4424_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4471_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4471_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4471_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4449_ = l_Lean_Expr_cleanupAnnotations(v_a_4445_);
v___x_4450_ = l_Lean_Expr_isApp(v___x_4449_);
if (v___x_4450_ == 0)
{
lean_dec_ref(v___x_4449_);
lean_del_object(v___x_4447_);
v___y_4429_ = v_a_4423_;
v___y_4430_ = v_a_4424_;
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
goto v___jp_4428_;
}
else
{
lean_object* v_arg_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v_arg_4451_ = lean_ctor_get(v___x_4449_, 1);
lean_inc_ref(v_arg_4451_);
v___x_4452_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4449_);
v___x_4453_ = l_Lean_Expr_isApp(v___x_4452_);
if (v___x_4453_ == 0)
{
lean_dec_ref(v___x_4452_);
lean_dec_ref(v_arg_4451_);
lean_del_object(v___x_4447_);
v___y_4429_ = v_a_4423_;
v___y_4430_ = v_a_4424_;
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
goto v___jp_4428_;
}
else
{
lean_object* v_arg_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v_arg_4454_ = lean_ctor_get(v___x_4452_, 1);
lean_inc_ref(v_arg_4454_);
v___x_4455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4452_);
v___x_4456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4457_ = l_Lean_Expr_isConstOf(v___x_4455_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; uint8_t v___x_4459_; 
lean_dec_ref(v_arg_4454_);
lean_del_object(v___x_4447_);
v___x_4458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4459_ = l_Lean_Expr_isConstOf(v___x_4455_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4461_ = l_Lean_Expr_isConstOf(v___x_4455_, v___x_4460_);
lean_dec_ref(v___x_4455_);
if (v___x_4461_ == 0)
{
lean_dec_ref(v_arg_4451_);
v___y_4429_ = v_a_4423_;
v___y_4430_ = v_a_4424_;
v___y_4431_ = v_a_4425_;
v___y_4432_ = v_a_4426_;
goto v___jp_4428_;
}
else
{
lean_dec_ref(v_proof_4422_);
v_p_4441_ = v_arg_4451_;
goto v___jp_4440_;
}
}
else
{
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_proof_4422_);
v_p_4441_ = v_arg_4451_;
goto v___jp_4440_;
}
}
else
{
uint8_t v___x_4462_; 
lean_dec_ref(v___x_4455_);
lean_dec_ref(v_proof_4422_);
v___x_4462_ = l_Lean_Expr_isFalse(v_arg_4454_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
lean_dec_ref(v_arg_4451_);
v___x_4463_ = lean_box(0);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4463_);
v___x_4465_ = v___x_4447_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4467_, 0, v_arg_4451_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4467_);
v___x_4469_ = v___x_4447_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref(v_proof_4422_);
v_a_4472_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4444_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4444_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
v___jp_4428_:
{
if (lean_obj_tag(v_proof_4422_) == 6)
{
lean_object* v_body_4433_; uint8_t v___x_4434_; 
v_body_4433_ = lean_ctor_get(v_proof_4422_, 2);
lean_inc_ref(v_body_4433_);
lean_dec_ref_known(v_proof_4422_, 3);
v___x_4434_ = l_Lean_Expr_hasLooseBVars(v_body_4433_);
if (v___x_4434_ == 0)
{
v_proof_4422_ = v_body_4433_;
v_a_4423_ = v___y_4429_;
v_a_4424_ = v___y_4430_;
v_a_4425_ = v___y_4431_;
v_a_4426_ = v___y_4432_;
goto _start;
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec_ref(v_body_4433_);
v___x_4436_ = lean_box(0);
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
return v___x_4437_;
}
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec_ref(v_proof_4422_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
return v___x_4439_;
}
}
v___jp_4440_:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4442_, 0, v_p_4441_);
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
return v___x_4443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4487_, lean_object* v___y_4488_){
_start:
{
uint8_t v___x_4490_; 
v___x_4490_ = l_Lean_Expr_hasMVar(v_e_4487_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4491_, 0, v_e_4487_);
return v___x_4491_;
}
else
{
lean_object* v___x_4492_; lean_object* v_mctx_4493_; lean_object* v___x_4494_; lean_object* v_fst_4495_; lean_object* v_snd_4496_; lean_object* v___x_4497_; lean_object* v_cache_4498_; lean_object* v_zetaDeltaFVarIds_4499_; lean_object* v_postponed_4500_; lean_object* v_diag_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4510_; 
v___x_4492_ = lean_st_ref_get(v___y_4488_);
v_mctx_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc_ref(v_mctx_4493_);
lean_dec(v___x_4492_);
v___x_4494_ = l_Lean_instantiateMVarsCore(v_mctx_4493_, v_e_4487_);
v_fst_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_fst_4495_);
v_snd_4496_ = lean_ctor_get(v___x_4494_, 1);
lean_inc(v_snd_4496_);
lean_dec_ref(v___x_4494_);
v___x_4497_ = lean_st_ref_take(v___y_4488_);
v_cache_4498_ = lean_ctor_get(v___x_4497_, 1);
v_zetaDeltaFVarIds_4499_ = lean_ctor_get(v___x_4497_, 2);
v_postponed_4500_ = lean_ctor_get(v___x_4497_, 3);
v_diag_4501_ = lean_ctor_get(v___x_4497_, 4);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4510_ == 0)
{
lean_object* v_unused_4511_; 
v_unused_4511_ = lean_ctor_get(v___x_4497_, 0);
lean_dec(v_unused_4511_);
v___x_4503_ = v___x_4497_;
v_isShared_4504_ = v_isSharedCheck_4510_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_diag_4501_);
lean_inc(v_postponed_4500_);
lean_inc(v_zetaDeltaFVarIds_4499_);
lean_inc(v_cache_4498_);
lean_dec(v___x_4497_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4510_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v_snd_4496_);
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_snd_4496_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_cache_4498_);
lean_ctor_set(v_reuseFailAlloc_4509_, 2, v_zetaDeltaFVarIds_4499_);
lean_ctor_set(v_reuseFailAlloc_4509_, 3, v_postponed_4500_);
lean_ctor_set(v_reuseFailAlloc_4509_, 4, v_diag_4501_);
v___x_4506_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_st_ref_put(v___y_4488_, v___x_4506_);
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v_fst_4495_);
return v___x_4508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4512_, v___y_4513_);
lean_dec(v___y_4513_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4516_, v___y_4518_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4530_, v_x_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
v_a_4546_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4537_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4537_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4554_, lean_object* v_x_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4554_, v_x_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4562_, lean_object* v_mvarId_4563_, lean_object* v_x_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4563_, v_x_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4571_, lean_object* v_mvarId_4572_, lean_object* v_x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4571_, v_mvarId_4572_, v_x_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4597_; 
v___x_4586_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4580_, v___y_4582_);
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4589_ = v___x_4586_;
v_isShared_4590_ = v_isSharedCheck_4597_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4597_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
uint8_t v___x_4591_; 
v___x_4591_ = l_Lean_Expr_hasSyntheticSorry(v_a_4587_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_del_object(v___x_4589_);
v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4587_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
return v___x_4592_;
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
lean_dec(v_a_4587_);
v___x_4593_ = lean_box(0);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v___x_4593_);
v___x_4595_ = v___x_4589_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v___x_4611_; lean_object* v___f_4612_; lean_object* v___x_4613_; 
lean_inc(v_mvarId_4605_);
v___x_4611_ = l_Lean_mkMVar(v_mvarId_4605_);
v___f_4612_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4612_, 0, v___x_4611_);
v___x_4613_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4605_, v___f_4612_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
return v_res_4620_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4642_){
_start:
{
if (lean_obj_tag(v_x_4642_) == 0)
{
uint8_t v___x_4643_; 
v___x_4643_ = 1;
return v___x_4643_;
}
else
{
lean_object* v_head_4644_; lean_object* v_tail_4645_; uint8_t v___y_4647_; lean_object* v___x_4649_; uint8_t v___x_4650_; 
v_head_4644_ = lean_ctor_get(v_x_4642_, 0);
lean_inc_n(v_head_4644_, 2);
v_tail_4645_ = lean_ctor_get(v_x_4642_, 1);
lean_inc(v_tail_4645_);
lean_dec_ref_known(v_x_4642_, 2);
v___x_4649_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4650_ = l_Lean_Syntax_isOfKind(v_head_4644_, v___x_4649_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; uint8_t v___x_4652_; 
v___x_4651_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4644_);
v___x_4652_ = l_Lean_Syntax_isOfKind(v_head_4644_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_dec(v_head_4644_);
v_x_4642_ = v_tail_4645_;
goto _start;
}
else
{
if (v___x_4650_ == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4654_ = lean_unsigned_to_nat(1u);
v___x_4655_ = l_Lean_Syntax_getArg(v_head_4644_, v___x_4654_);
lean_dec(v_head_4644_);
v___x_4656_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4657_ = l_Lean_Syntax_isOfKind(v___x_4655_, v___x_4656_);
if (v___x_4657_ == 0)
{
v_x_4642_ = v_tail_4645_;
goto _start;
}
else
{
v___y_4647_ = v___x_4650_;
goto v___jp_4646_;
}
}
else
{
lean_dec(v_head_4644_);
v___y_4647_ = v___x_4650_;
goto v___jp_4646_;
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v___x_4659_ = lean_unsigned_to_nat(3u);
v___x_4660_ = l_Lean_Syntax_getArg(v_head_4644_, v___x_4659_);
lean_dec(v_head_4644_);
v___x_4661_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4662_ = l_Lean_Syntax_isOfKind(v___x_4660_, v___x_4661_);
if (v___x_4662_ == 0)
{
v_x_4642_ = v_tail_4645_;
goto _start;
}
else
{
uint8_t v___x_4664_; 
lean_dec(v_tail_4645_);
v___x_4664_ = 0;
return v___x_4664_;
}
}
v___jp_4646_:
{
if (v___y_4647_ == 0)
{
lean_dec(v_tail_4645_);
return v___y_4647_;
}
else
{
v_x_4642_ = v_tail_4645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4665_){
_start:
{
uint8_t v_res_4666_; lean_object* v_r_4667_; 
v_res_4666_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4665_);
v_r_4667_ = lean_box(v_res_4666_);
return v_r_4667_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4668_){
_start:
{
uint8_t v___x_4669_; 
v___x_4669_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4668_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4670_){
_start:
{
uint8_t v_res_4671_; lean_object* v_r_4672_; 
v_res_4671_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4670_);
v_r_4672_ = lean_box(v_res_4671_);
return v_r_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4688_, lean_object* v_a_4689_){
_start:
{
if (lean_obj_tag(v_seq_4688_) == 0)
{
lean_object* v_ref_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v_ref_4691_ = lean_ctor_get(v_a_4689_, 2);
v___x_4692_ = 0;
v___x_4693_ = l_Lean_SourceInfo_fromRef(v_ref_4691_, v___x_4692_);
v___x_4694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4693_);
v___x_4696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4693_);
lean_ctor_set(v___x_4696_, 1, v___x_4694_);
v___x_4697_ = l_Lean_Syntax_node1(v___x_4693_, v___x_4695_, v___x_4696_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
else
{
lean_object* v_tail_4699_; 
v_tail_4699_ = lean_ctor_get(v_seq_4688_, 1);
if (lean_obj_tag(v_tail_4699_) == 0)
{
lean_object* v_head_4700_; lean_object* v___x_4701_; 
v_head_4700_ = lean_ctor_get(v_seq_4688_, 0);
lean_inc(v_head_4700_);
lean_dec_ref_known(v_seq_4688_, 2);
v___x_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4701_, 0, v_head_4700_);
return v___x_4701_;
}
else
{
lean_object* v_head_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4724_; 
lean_inc(v_tail_4699_);
v_head_4702_ = lean_ctor_get(v_seq_4688_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_seq_4688_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; 
v_unused_4725_ = lean_ctor_get(v_seq_4688_, 1);
lean_dec(v_unused_4725_);
v___x_4704_ = v_seq_4688_;
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_head_4702_);
lean_dec(v_seq_4688_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4723_; 
v___x_4706_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4699_, v_a_4689_);
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4709_ = v___x_4706_;
v_isShared_4710_ = v_isSharedCheck_4723_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4706_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4723_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_ref_4711_; uint8_t v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v_ref_4711_ = lean_ctor_get(v_a_4689_, 2);
v___x_4712_ = 0;
v___x_4713_ = l_Lean_SourceInfo_fromRef(v_ref_4711_, v___x_4712_);
v___x_4714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4713_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 2);
lean_ctor_set(v___x_4704_, 1, v___x_4715_);
lean_ctor_set(v___x_4704_, 0, v___x_4713_);
v___x_4717_ = v___x_4704_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; lean_object* v___x_4720_; 
v___x_4718_ = l_Lean_Syntax_node3(v___x_4713_, v___x_4714_, v_head_4702_, v___x_4717_, v_a_4707_);
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v___x_4718_);
v___x_4720_ = v___x_4709_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4726_, v_a_4727_);
lean_dec_ref(v_a_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4730_, v_a_4731_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4735_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4740_, lean_object* v_seq_4741_, lean_object* v_a_4742_){
_start:
{
if (lean_obj_tag(v_seq_4741_) == 0)
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v_cases_4740_);
return v___x_4744_;
}
else
{
lean_object* v___x_4745_; lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4760_; 
v___x_4745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4741_, v_a_4742_);
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4760_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4760_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v_ref_4750_; uint8_t v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
v_ref_4750_ = lean_ctor_get(v_a_4742_, 2);
v___x_4751_ = 0;
v___x_4752_ = l_Lean_SourceInfo_fromRef(v_ref_4750_, v___x_4751_);
v___x_4753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4752_);
v___x_4755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4752_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = l_Lean_Syntax_node3(v___x_4752_, v___x_4753_, v_cases_4740_, v___x_4755_, v_a_4746_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4756_);
v___x_4758_ = v___x_4748_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4761_, lean_object* v_seq_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4761_, v_seq_4762_, v_a_4763_);
lean_dec_ref(v_a_4763_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4766_, lean_object* v_seq_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4766_, v_seq_4767_, v_a_4768_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4772_, lean_object* v_seq_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4772_, v_seq_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
return v_res_4777_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4778_, lean_object* v_x_4779_){
_start:
{
if (lean_obj_tag(v_x_4778_) == 0)
{
if (lean_obj_tag(v_x_4779_) == 0)
{
uint8_t v___x_4780_; 
v___x_4780_ = 1;
return v___x_4780_;
}
else
{
uint8_t v___x_4781_; 
v___x_4781_ = 0;
return v___x_4781_;
}
}
else
{
if (lean_obj_tag(v_x_4779_) == 0)
{
uint8_t v___x_4782_; 
v___x_4782_ = 0;
return v___x_4782_;
}
else
{
lean_object* v_head_4783_; lean_object* v_tail_4784_; lean_object* v_head_4785_; lean_object* v_tail_4786_; uint8_t v___x_4787_; 
v_head_4783_ = lean_ctor_get(v_x_4778_, 0);
v_tail_4784_ = lean_ctor_get(v_x_4778_, 1);
v_head_4785_ = lean_ctor_get(v_x_4779_, 0);
v_tail_4786_ = lean_ctor_get(v_x_4779_, 1);
v___x_4787_ = l_Lean_Syntax_structEq(v_head_4783_, v_head_4785_);
if (v___x_4787_ == 0)
{
return v___x_4787_;
}
else
{
v_x_4778_ = v_tail_4784_;
v_x_4779_ = v_tail_4786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4789_, lean_object* v_x_4790_){
_start:
{
uint8_t v_res_4791_; lean_object* v_r_4792_; 
v_res_4791_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4789_, v_x_4790_);
lean_dec(v_x_4790_);
lean_dec(v_x_4789_);
v_r_4792_ = lean_box(v_res_4791_);
return v_r_4792_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4793_, lean_object* v___x_4794_, lean_object* v_as_4795_, size_t v_i_4796_, size_t v_stop_4797_){
_start:
{
uint8_t v___x_4802_; 
v___x_4802_ = lean_usize_dec_eq(v_i_4796_, v_stop_4797_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; uint8_t v___x_4804_; 
v___x_4803_ = lean_array_uget_borrowed(v_as_4795_, v_i_4796_);
v___x_4804_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4803_, v_alt_4793_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = lean_unsigned_to_nat(0u);
v___x_4806_ = lean_nat_dec_lt(v___x_4805_, v___x_4794_);
if (v___x_4806_ == 0)
{
goto v___jp_4798_;
}
else
{
return v___x_4806_;
}
}
else
{
goto v___jp_4798_;
}
}
else
{
uint8_t v___x_4807_; 
v___x_4807_ = 0;
return v___x_4807_;
}
v___jp_4798_:
{
size_t v___x_4799_; size_t v___x_4800_; 
v___x_4799_ = ((size_t)1ULL);
v___x_4800_ = lean_usize_add(v_i_4796_, v___x_4799_);
v_i_4796_ = v___x_4800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4808_, lean_object* v___x_4809_, lean_object* v_as_4810_, lean_object* v_i_4811_, lean_object* v_stop_4812_){
_start:
{
size_t v_i_boxed_4813_; size_t v_stop_boxed_4814_; uint8_t v_res_4815_; lean_object* v_r_4816_; 
v_i_boxed_4813_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_stop_boxed_4814_ = lean_unbox_usize(v_stop_4812_);
lean_dec(v_stop_4812_);
v_res_4815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4808_, v___x_4809_, v_as_4810_, v_i_boxed_4813_, v_stop_boxed_4814_);
lean_dec_ref(v_as_4810_);
lean_dec(v___x_4809_);
lean_dec(v_alt_4808_);
v_r_4816_ = lean_box(v_res_4815_);
return v_r_4816_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4817_){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; 
v___x_4818_ = lean_unsigned_to_nat(0u);
v___x_4819_ = lean_array_get_size(v_alts_4817_);
v___x_4820_ = lean_nat_dec_lt(v___x_4818_, v___x_4819_);
if (v___x_4820_ == 0)
{
uint8_t v___x_4821_; 
v___x_4821_ = 1;
return v___x_4821_;
}
else
{
lean_object* v_alt_4822_; uint8_t v___x_4823_; 
v_alt_4822_ = lean_array_fget_borrowed(v_alts_4817_, v___x_4818_);
lean_inc(v_alt_4822_);
v___x_4823_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4822_);
if (v___x_4823_ == 0)
{
return v___x_4823_;
}
else
{
if (v___x_4820_ == 0)
{
return v___x_4820_;
}
else
{
if (v___x_4820_ == 0)
{
return v___x_4820_;
}
else
{
size_t v___x_4824_; size_t v___x_4825_; uint8_t v___x_4826_; 
v___x_4824_ = ((size_t)0ULL);
v___x_4825_ = lean_usize_of_nat(v___x_4819_);
v___x_4826_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4822_, v___x_4819_, v_alts_4817_, v___x_4824_, v___x_4825_);
if (v___x_4826_ == 0)
{
return v___x_4820_;
}
else
{
uint8_t v___x_4827_; 
v___x_4827_ = 0;
return v___x_4827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4828_){
_start:
{
uint8_t v_res_4829_; lean_object* v_r_4830_; 
v_res_4829_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4828_);
lean_dec_ref(v_alts_4828_);
v_r_4830_ = lean_box(v_res_4829_);
return v_r_4830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4838_){
_start:
{
if (lean_obj_tag(v_alt_4838_) == 1)
{
lean_object* v_tail_4839_; 
v_tail_4839_ = lean_ctor_get(v_alt_4838_, 1);
if (lean_obj_tag(v_tail_4839_) == 0)
{
lean_object* v_head_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v_head_4840_ = lean_ctor_get(v_alt_4838_, 0);
lean_inc(v_head_4840_);
lean_dec_ref_known(v_alt_4838_, 2);
v___x_4841_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4842_ = l_Lean_Syntax_isOfKind(v_head_4840_, v___x_4841_);
return v___x_4842_;
}
else
{
uint8_t v___x_4843_; 
lean_dec_ref_known(v_alt_4838_, 2);
v___x_4843_ = 0;
return v___x_4843_;
}
}
else
{
uint8_t v___x_4844_; 
lean_dec(v_alt_4838_);
v___x_4844_ = 0;
return v___x_4844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4845_){
_start:
{
uint8_t v_res_4846_; lean_object* v_r_4847_; 
v_res_4846_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4845_);
v_r_4847_ = lean_box(v_res_4846_);
return v_r_4847_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4848_, lean_object* v_x_4849_, lean_object* v___y_4850_){
_start:
{
if (lean_obj_tag(v_x_4848_) == 0)
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4852_ = l_List_reverse___redArg(v_x_4849_);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
else
{
lean_object* v_head_4854_; lean_object* v_tail_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4873_; 
v_head_4854_ = lean_ctor_get(v_x_4848_, 0);
v_tail_4855_ = lean_ctor_get(v_x_4848_, 1);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_x_4848_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4857_ = v_x_4848_;
v_isShared_4858_ = v_isSharedCheck_4873_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_tail_4855_);
lean_inc(v_head_4854_);
lean_dec(v_x_4848_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4873_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4854_, v___y_4850_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref_known(v___x_4859_, 1);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 1, v_x_4849_);
lean_ctor_set(v___x_4857_, 0, v_a_4860_);
v___x_4862_ = v___x_4857_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4860_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v_x_4849_);
v___x_4862_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
v_x_4848_ = v_tail_4855_;
v_x_4849_ = v___x_4862_;
goto _start;
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
lean_del_object(v___x_4857_);
lean_dec(v_tail_4855_);
lean_dec(v_x_4849_);
v_a_4865_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4859_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4859_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4874_, lean_object* v_x_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4874_, v_x_4875_, v___y_4876_);
lean_dec_ref(v___y_4876_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4879_, lean_object* v_alts_4880_, uint8_t v_compress_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v_seq_4886_; 
if (v_compress_4881_ == 0)
{
goto v___jp_4889_;
}
else
{
uint8_t v___x_4899_; 
v___x_4899_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4880_);
if (v___x_4899_ == 0)
{
goto v___jp_4889_;
}
else
{
lean_object* v___x_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
v___x_4900_ = lean_unsigned_to_nat(0u);
v___x_4901_ = lean_array_get_size(v_alts_4880_);
v___x_4902_ = lean_nat_dec_lt(v___x_4900_, v___x_4901_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
lean_dec_ref(v_alts_4880_);
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4904_, 0, v_cases_4879_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
else
{
lean_object* v___x_4906_; lean_object* v_firstAlt_4907_; uint8_t v___x_4908_; 
v___x_4906_ = lean_box(0);
v_firstAlt_4907_ = lean_array_get(v___x_4906_, v_alts_4880_, v___x_4900_);
lean_dec_ref(v_alts_4880_);
lean_inc(v_firstAlt_4907_);
v___x_4908_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4907_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4918_; 
v___x_4909_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4879_, v_firstAlt_4907_, v_a_4882_);
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4914_, 0, v_a_4910_);
lean_ctor_set(v___x_4914_, 1, v___x_4906_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4914_);
v___x_4916_ = v___x_4912_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
else
{
lean_object* v___x_4919_; 
lean_dec(v_cases_4879_);
v___x_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4919_, 0, v_firstAlt_4907_);
return v___x_4919_;
}
}
}
}
v___jp_4885_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4887_, 0, v_cases_4879_);
lean_ctor_set(v___x_4887_, 1, v_seq_4886_);
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
return v___x_4888_;
}
v___jp_4889_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4890_ = lean_array_get_size(v_alts_4880_);
v___x_4891_ = lean_unsigned_to_nat(1u);
v___x_4892_ = lean_nat_dec_eq(v___x_4890_, v___x_4891_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_array_to_list(v_alts_4880_);
v___x_4894_ = lean_box(0);
v___x_4895_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4893_, v___x_4894_, v_a_4882_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref_known(v___x_4895_, 1);
v_seq_4886_ = v_a_4896_;
goto v___jp_4885_;
}
else
{
lean_dec(v_cases_4879_);
return v___x_4895_;
}
}
else
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4897_ = lean_unsigned_to_nat(0u);
v___x_4898_ = lean_array_fget(v_alts_4880_, v___x_4897_);
lean_dec_ref(v_alts_4880_);
v_seq_4886_ = v___x_4898_;
goto v___jp_4885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4920_, lean_object* v_alts_4921_, lean_object* v_compress_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
uint8_t v_compress_boxed_4926_; lean_object* v_res_4927_; 
v_compress_boxed_4926_ = lean_unbox(v_compress_4922_);
v_res_4927_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4920_, v_alts_4921_, v_compress_boxed_4926_, v_a_4923_, v_a_4924_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4928_, lean_object* v_x_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4928_, v_x_4929_, v___y_4930_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4934_, lean_object* v_x_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4934_, v_x_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; lean_object* v_env_4944_; uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4943_ = lean_st_ref_get(v___y_4941_);
v_env_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc_ref(v_env_4944_);
lean_dec(v___x_4943_);
v___x_4945_ = l_Lean_Meta_isMatcherAppCore(v_env_4944_, v_e_4940_);
v___x_4946_ = lean_box(v___x_4945_);
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4948_, v___y_4949_);
lean_dec(v___y_4949_);
lean_dec_ref(v_e_4948_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4952_, v___y_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v_e_4965_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v___x_4989_; 
lean_inc(v___y_4983_);
lean_inc_ref(v___y_4982_);
lean_inc(v___y_4981_);
lean_inc_ref(v___y_4980_);
lean_inc(v___y_4979_);
v___x_4989_ = lean_apply_10(v_x_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, lean_box(0));
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_5002_, lean_object* v_x_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v___f_5014_; lean_object* v___x_5015_; 
lean_inc(v___y_5008_);
lean_inc_ref(v___y_5007_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
v___f_5014_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5014_, 0, v_x_5003_);
lean_closure_set(v___f_5014_, 1, v___y_5004_);
lean_closure_set(v___f_5014_, 2, v___y_5005_);
lean_closure_set(v___f_5014_, 3, v___y_5006_);
lean_closure_set(v___f_5014_, 4, v___y_5007_);
lean_closure_set(v___f_5014_, 5, v___y_5008_);
v___x_5015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5002_, v___f_5014_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_);
if (lean_obj_tag(v___x_5015_) == 0)
{
return v___x_5015_;
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5015_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5015_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5024_, lean_object* v_x_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5024_, v_x_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5037_, lean_object* v_mvarId_5038_, lean_object* v_x_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5038_, v_x_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5051_, lean_object* v_mvarId_5052_, lean_object* v_x_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5051_, v_mvarId_5052_, v_x_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5065_, lean_object* v___y_5066_){
_start:
{
uint8_t v___x_5068_; 
v___x_5068_ = l_Lean_Expr_hasMVar(v_e_5065_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v_e_5065_);
return v___x_5069_;
}
else
{
lean_object* v___x_5070_; lean_object* v_mctx_5071_; lean_object* v___x_5072_; lean_object* v_fst_5073_; lean_object* v_snd_5074_; lean_object* v___x_5075_; lean_object* v_cache_5076_; lean_object* v_zetaDeltaFVarIds_5077_; lean_object* v_postponed_5078_; lean_object* v_diag_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5088_; 
v___x_5070_ = lean_st_ref_get(v___y_5066_);
v_mctx_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc_ref(v_mctx_5071_);
lean_dec(v___x_5070_);
v___x_5072_ = l_Lean_instantiateMVarsCore(v_mctx_5071_, v_e_5065_);
v_fst_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc(v_fst_5073_);
v_snd_5074_ = lean_ctor_get(v___x_5072_, 1);
lean_inc(v_snd_5074_);
lean_dec_ref(v___x_5072_);
v___x_5075_ = lean_st_ref_take(v___y_5066_);
v_cache_5076_ = lean_ctor_get(v___x_5075_, 1);
v_zetaDeltaFVarIds_5077_ = lean_ctor_get(v___x_5075_, 2);
v_postponed_5078_ = lean_ctor_get(v___x_5075_, 3);
v_diag_5079_ = lean_ctor_get(v___x_5075_, 4);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v___x_5075_, 0);
lean_dec(v_unused_5089_);
v___x_5081_ = v___x_5075_;
v_isShared_5082_ = v_isSharedCheck_5088_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_diag_5079_);
lean_inc(v_postponed_5078_);
lean_inc(v_zetaDeltaFVarIds_5077_);
lean_inc(v_cache_5076_);
lean_dec(v___x_5075_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5088_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 0, v_snd_5074_);
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_snd_5074_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v_cache_5076_);
lean_ctor_set(v_reuseFailAlloc_5087_, 2, v_zetaDeltaFVarIds_5077_);
lean_ctor_set(v_reuseFailAlloc_5087_, 3, v_postponed_5078_);
lean_ctor_set(v_reuseFailAlloc_5087_, 4, v_diag_5079_);
v___x_5084_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_st_ref_put(v___y_5066_, v___x_5084_);
v___x_5086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5086_, 0, v_fst_5073_);
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5090_, v___y_5091_);
lean_dec(v___y_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v___x_5105_; 
v___x_5105_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5094_, v___y_5101_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
return v_res_5117_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5120_ = l_Lean_stringToMessageData(v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5121_, lean_object* v_c_5122_, lean_object* v_a_5123_, lean_object* v_numCases_5124_, uint8_t v_isRec_5125_, lean_object* v_anchorInfo_x3f_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v_mvarIds_5139_; lean_object* v___x_5189_; 
v___x_5189_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5121_, v___y_5127_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v___y_5192_; lean_object* v___x_5244_; uint8_t v___x_5247_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___x_5189_, 1);
v___x_5244_ = lean_unsigned_to_nat(1u);
v___x_5247_ = lean_nat_dec_lt(v___x_5244_, v_numCases_5124_);
if (v___x_5247_ == 0)
{
if (v_isRec_5125_ == 0)
{
lean_inc(v_a_5190_);
v___y_5192_ = v_a_5190_;
goto v___jp_5191_;
}
else
{
goto v___jp_5245_;
}
}
else
{
goto v___jp_5245_;
}
v___jp_5191_:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5193_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5122_);
lean_inc_ref(v___x_5121_);
v___x_5194_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5121_, v___y_5192_, v_numCases_5124_, v___x_5193_, v___y_5130_, v___y_5133_, v___y_5135_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v___x_5195_; 
lean_dec_ref_known(v___x_5194_, 1);
lean_inc_ref(v___x_5121_);
v___x_5195_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5121_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_toCold_5196_; lean_object* v_options_5197_; uint8_t v_hasTrace_5198_; 
lean_dec_ref_known(v___x_5195_, 1);
v_toCold_5196_ = lean_ctor_get(v___y_5135_, 0);
v_options_5197_ = lean_ctor_get(v_toCold_5196_, 2);
v_hasTrace_5198_ = lean_ctor_get_uint8(v_options_5197_, sizeof(void*)*1);
if (v_hasTrace_5198_ == 0)
{
lean_dec(v_a_5190_);
goto v___jp_5142_;
}
else
{
lean_object* v_inheritedTraceOptions_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; uint8_t v___x_5202_; 
v_inheritedTraceOptions_5199_ = lean_ctor_get(v_toCold_5196_, 11);
v___x_5200_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5201_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5199_, v_options_5197_, v___x_5201_);
if (v___x_5202_ == 0)
{
lean_dec(v_a_5190_);
goto v___jp_5142_;
}
else
{
lean_object* v___x_5203_; 
v___x_5203_ = l_Lean_Meta_Grind_updateLastTag(v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
lean_dec_ref_known(v___x_5203_, 1);
lean_inc_ref(v___x_5121_);
v___x_5204_ = l_Lean_MessageData_ofExpr(v___x_5121_);
v___x_5205_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5204_);
lean_ctor_set(v___x_5206_, 1, v___x_5205_);
v___x_5207_ = l_Nat_reprFast(v_a_5190_);
v___x_5208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
v___x_5209_ = l_Lean_MessageData_ofFormat(v___x_5208_);
v___x_5210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5206_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
v___x_5211_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5200_, v___x_5210_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_dec_ref_known(v___x_5211_, 1);
goto v___jp_5142_;
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_a_5123_);
lean_dec_ref(v_c_5122_);
lean_dec_ref(v___x_5121_);
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
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
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_dec(v_a_5190_);
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_a_5123_);
lean_dec_ref(v_c_5122_);
lean_dec_ref(v___x_5121_);
v_a_5220_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5203_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5203_);
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
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec(v_a_5190_);
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_a_5123_);
lean_dec_ref(v_c_5122_);
lean_dec_ref(v___x_5121_);
v_a_5228_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5195_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5195_);
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
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec(v_a_5190_);
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_a_5123_);
lean_dec_ref(v_c_5122_);
lean_dec_ref(v___x_5121_);
v_a_5236_ = lean_ctor_get(v___x_5194_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5194_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5194_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
v___jp_5245_:
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_nat_add(v_a_5190_, v___x_5244_);
v___y_5192_ = v___x_5246_;
goto v___jp_5191_;
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_numCases_5124_);
lean_dec(v_a_5123_);
lean_dec_ref(v_c_5122_);
lean_dec_ref(v___x_5121_);
v_a_5248_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5189_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5189_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
v___jp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5140_, 0, v_mvarIds_5139_);
lean_ctor_set(v___x_5140_, 1, v_anchorInfo_x3f_5126_);
v___x_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
return v___x_5141_;
}
v___jp_5142_:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5121_, v___y_5136_);
if (lean_obj_tag(v_c_5122_) == 1)
{
lean_object* v_e_5144_; lean_object* v_binderType_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
lean_dec_ref(v___x_5143_);
lean_dec_ref(v___x_5121_);
v_e_5144_ = lean_ctor_get(v_c_5122_, 0);
lean_inc_ref(v_e_5144_);
lean_dec_ref_known(v_c_5122_, 2);
v_binderType_5145_ = lean_ctor_get(v_e_5144_, 1);
lean_inc_ref(v_binderType_5145_);
lean_dec_ref(v_e_5144_);
v___x_5146_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5145_);
v___x_5147_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5123_, v___x_5146_, v___y_5129_, v___y_5130_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v_mvarIds_5139_ = v_a_5148_;
goto v___jp_5138_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec(v_anchorInfo_x3f_5126_);
v_a_5149_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5147_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5147_);
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
lean_object* v_a_5157_; uint8_t v___x_5158_; 
lean_dec_ref(v_c_5122_);
v_a_5157_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5157_);
lean_dec_ref(v___x_5143_);
v___x_5158_ = lean_unbox(v_a_5157_);
lean_dec(v_a_5157_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5121_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5161_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
v___x_5161_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5123_, v_a_5160_, v___y_5129_, v___y_5130_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v_mvarIds_5139_ = v_a_5162_;
goto v___jp_5138_;
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_dec(v_anchorInfo_x3f_5126_);
v_a_5163_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5161_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5161_);
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
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
lean_dec(v_anchorInfo_x3f_5126_);
lean_dec(v_a_5123_);
v_a_5171_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5159_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5159_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
else
{
lean_object* v___x_5179_; 
v___x_5179_ = l_Lean_Meta_Grind_casesMatch(v_a_5123_, v___x_5121_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref_known(v___x_5179_, 1);
v_mvarIds_5139_ = v_a_5180_;
goto v___jp_5138_;
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5188_; 
lean_dec(v_anchorInfo_x3f_5126_);
v_a_5181_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5183_ = v___x_5179_;
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_a_5181_);
lean_dec(v___x_5179_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5188_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5186_; 
if (v_isShared_5184_ == 0)
{
v___x_5186_ = v___x_5183_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5256_ = _args[0];
lean_object* v_c_5257_ = _args[1];
lean_object* v_a_5258_ = _args[2];
lean_object* v_numCases_5259_ = _args[3];
lean_object* v_isRec_5260_ = _args[4];
lean_object* v_anchorInfo_x3f_5261_ = _args[5];
lean_object* v___y_5262_ = _args[6];
lean_object* v___y_5263_ = _args[7];
lean_object* v___y_5264_ = _args[8];
lean_object* v___y_5265_ = _args[9];
lean_object* v___y_5266_ = _args[10];
lean_object* v___y_5267_ = _args[11];
lean_object* v___y_5268_ = _args[12];
lean_object* v___y_5269_ = _args[13];
lean_object* v___y_5270_ = _args[14];
lean_object* v___y_5271_ = _args[15];
lean_object* v___y_5272_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5273_; lean_object* v_res_5274_; 
v_isRec_boxed_5273_ = lean_unbox(v_isRec_5260_);
v_res_5274_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5256_, v_c_5257_, v_a_5258_, v_numCases_5259_, v_isRec_boxed_5273_, v_anchorInfo_x3f_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec(v___y_5262_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5275_, uint8_t v_trace_5276_, lean_object* v___f_5277_, lean_object* v_c_5278_, lean_object* v_candidates_x3f_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v___x_5290_; lean_object* v___y_5292_; 
v___x_5290_ = lean_st_mk_ref(v_goal_5275_);
if (v_trace_5276_ == 0)
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
lean_dec(v_candidates_x3f_5279_);
v___x_5311_ = lean_box(0);
lean_inc(v___x_5290_);
v___x_5312_ = lean_apply_12(v___f_5277_, v___x_5311_, v___x_5290_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, lean_box(0));
v___y_5292_ = v___x_5312_;
goto v___jp_5291_;
}
else
{
lean_object* v___x_5313_; 
v___x_5313_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5278_, v_candidates_x3f_5279_, v___x_5290_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref_known(v___x_5313_, 1);
v___x_5315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5315_, 0, v_a_5314_);
lean_inc(v___x_5290_);
v___x_5316_ = lean_apply_12(v___f_5277_, v___x_5315_, v___x_5290_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, lean_box(0));
v___y_5292_ = v___x_5316_;
goto v___jp_5291_;
}
else
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5324_; 
lean_dec(v___x_5290_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___f_5277_);
v_a_5317_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5319_ = v___x_5313_;
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5313_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5322_; 
if (v_isShared_5320_ == 0)
{
v___x_5322_ = v___x_5319_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5317_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
v___jp_5291_:
{
if (lean_obj_tag(v___y_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5302_; 
v_a_5293_ = lean_ctor_get(v___y_5292_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___y_5292_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5295_ = v___y_5292_;
v_isShared_5296_ = v_isSharedCheck_5302_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___y_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5302_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5300_; 
v___x_5297_ = lean_st_ref_get(v___x_5290_);
lean_dec(v___x_5290_);
v___x_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5298_, 0, v_a_5293_);
lean_ctor_set(v___x_5298_, 1, v___x_5297_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5298_);
v___x_5300_ = v___x_5295_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_dec(v___x_5290_);
v_a_5303_ = lean_ctor_get(v___y_5292_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___y_5292_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___y_5292_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___y_5292_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5325_, lean_object* v_trace_5326_, lean_object* v___f_5327_, lean_object* v_c_5328_, lean_object* v_candidates_x3f_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
uint8_t v_trace_boxed_5340_; lean_object* v_res_5341_; 
v_trace_boxed_5340_ = lean_unbox(v_trace_5326_);
v_res_5341_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5325_, v_trace_boxed_5340_, v___f_5327_, v_c_5328_, v_candidates_x3f_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
lean_dec_ref(v_c_5328_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5342_, lean_object* v_x_5343_, lean_object* v_x_5344_, lean_object* v_x_5345_){
_start:
{
lean_object* v_ks_5346_; lean_object* v_vs_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5371_; 
v_ks_5346_ = lean_ctor_get(v_x_5342_, 0);
v_vs_5347_ = lean_ctor_get(v_x_5342_, 1);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_x_5342_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5349_ = v_x_5342_;
v_isShared_5350_ = v_isSharedCheck_5371_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_vs_5347_);
lean_inc(v_ks_5346_);
lean_dec(v_x_5342_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5371_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5351_; uint8_t v___x_5352_; 
v___x_5351_ = lean_array_get_size(v_ks_5346_);
v___x_5352_ = lean_nat_dec_lt(v_x_5343_, v___x_5351_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5356_; 
lean_dec(v_x_5343_);
v___x_5353_ = lean_array_push(v_ks_5346_, v_x_5344_);
v___x_5354_ = lean_array_push(v_vs_5347_, v_x_5345_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5354_);
lean_ctor_set(v___x_5349_, 0, v___x_5353_);
v___x_5356_ = v___x_5349_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5353_);
lean_ctor_set(v_reuseFailAlloc_5357_, 1, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
else
{
lean_object* v_k_x27_5358_; uint8_t v___x_5359_; 
v_k_x27_5358_ = lean_array_fget_borrowed(v_ks_5346_, v_x_5343_);
v___x_5359_ = l_Lean_instBEqMVarId_beq(v_x_5344_, v_k_x27_5358_);
if (v___x_5359_ == 0)
{
lean_object* v___x_5361_; 
if (v_isShared_5350_ == 0)
{
v___x_5361_ = v___x_5349_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_ks_5346_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_vs_5347_);
v___x_5361_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
v___x_5362_ = lean_unsigned_to_nat(1u);
v___x_5363_ = lean_nat_add(v_x_5343_, v___x_5362_);
lean_dec(v_x_5343_);
v_x_5342_ = v___x_5361_;
v_x_5343_ = v___x_5363_;
goto _start;
}
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5369_; 
v___x_5366_ = lean_array_fset(v_ks_5346_, v_x_5343_, v_x_5344_);
v___x_5367_ = lean_array_fset(v_vs_5347_, v_x_5343_, v_x_5345_);
lean_dec(v_x_5343_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5367_);
lean_ctor_set(v___x_5349_, 0, v___x_5366_);
v___x_5369_ = v___x_5349_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5366_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v___x_5367_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5372_, lean_object* v_k_5373_, lean_object* v_v_5374_){
_start:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5375_ = lean_unsigned_to_nat(0u);
v___x_5376_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5372_, v___x_5375_, v_k_5373_, v_v_5374_);
return v___x_5376_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5377_; 
v___x_5377_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5378_, size_t v_x_5379_, size_t v_x_5380_, lean_object* v_x_5381_, lean_object* v_x_5382_){
_start:
{
if (lean_obj_tag(v_x_5378_) == 0)
{
lean_object* v_es_5383_; size_t v___x_5384_; size_t v___x_5385_; lean_object* v_j_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; 
v_es_5383_ = lean_ctor_get(v_x_5378_, 0);
v___x_5384_ = ((size_t)31ULL);
v___x_5385_ = lean_usize_land(v_x_5379_, v___x_5384_);
v_j_5386_ = lean_usize_to_nat(v___x_5385_);
v___x_5387_ = lean_array_get_size(v_es_5383_);
v___x_5388_ = lean_nat_dec_lt(v_j_5386_, v___x_5387_);
if (v___x_5388_ == 0)
{
lean_dec(v_j_5386_);
lean_dec(v_x_5382_);
lean_dec(v_x_5381_);
return v_x_5378_;
}
else
{
lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5427_; 
lean_inc_ref(v_es_5383_);
v_isSharedCheck_5427_ = !lean_is_exclusive(v_x_5378_);
if (v_isSharedCheck_5427_ == 0)
{
lean_object* v_unused_5428_; 
v_unused_5428_ = lean_ctor_get(v_x_5378_, 0);
lean_dec(v_unused_5428_);
v___x_5390_ = v_x_5378_;
v_isShared_5391_ = v_isSharedCheck_5427_;
goto v_resetjp_5389_;
}
else
{
lean_dec(v_x_5378_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5427_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v_v_5392_; lean_object* v___x_5393_; lean_object* v_xs_x27_5394_; lean_object* v___y_5396_; 
v_v_5392_ = lean_array_fget(v_es_5383_, v_j_5386_);
v___x_5393_ = lean_box(0);
v_xs_x27_5394_ = lean_array_fset(v_es_5383_, v_j_5386_, v___x_5393_);
switch(lean_obj_tag(v_v_5392_))
{
case 0:
{
lean_object* v_key_5401_; lean_object* v_val_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5412_; 
v_key_5401_ = lean_ctor_get(v_v_5392_, 0);
v_val_5402_ = lean_ctor_get(v_v_5392_, 1);
v_isSharedCheck_5412_ = !lean_is_exclusive(v_v_5392_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5404_ = v_v_5392_;
v_isShared_5405_ = v_isSharedCheck_5412_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_val_5402_);
lean_inc(v_key_5401_);
lean_dec(v_v_5392_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5412_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
uint8_t v___x_5406_; 
v___x_5406_ = l_Lean_instBEqMVarId_beq(v_x_5381_, v_key_5401_);
if (v___x_5406_ == 0)
{
lean_object* v___x_5407_; lean_object* v___x_5408_; 
lean_del_object(v___x_5404_);
v___x_5407_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5401_, v_val_5402_, v_x_5381_, v_x_5382_);
v___x_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
v___y_5396_ = v___x_5408_;
goto v___jp_5395_;
}
else
{
lean_object* v___x_5410_; 
lean_dec(v_val_5402_);
lean_dec(v_key_5401_);
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v_x_5382_);
lean_ctor_set(v___x_5404_, 0, v_x_5381_);
v___x_5410_ = v___x_5404_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_x_5381_);
lean_ctor_set(v_reuseFailAlloc_5411_, 1, v_x_5382_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
v___y_5396_ = v___x_5410_;
goto v___jp_5395_;
}
}
}
}
case 1:
{
lean_object* v_node_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5425_; 
v_node_5413_ = lean_ctor_get(v_v_5392_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v_v_5392_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5415_ = v_v_5392_;
v_isShared_5416_ = v_isSharedCheck_5425_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_node_5413_);
lean_dec(v_v_5392_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5425_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
size_t v___x_5417_; size_t v___x_5418_; size_t v___x_5419_; size_t v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5423_; 
v___x_5417_ = ((size_t)5ULL);
v___x_5418_ = lean_usize_shift_right(v_x_5379_, v___x_5417_);
v___x_5419_ = ((size_t)1ULL);
v___x_5420_ = lean_usize_add(v_x_5380_, v___x_5419_);
v___x_5421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5413_, v___x_5418_, v___x_5420_, v_x_5381_, v_x_5382_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 0, v___x_5421_);
v___x_5423_ = v___x_5415_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
v___y_5396_ = v___x_5423_;
goto v___jp_5395_;
}
}
}
default: 
{
lean_object* v___x_5426_; 
v___x_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5426_, 0, v_x_5381_);
lean_ctor_set(v___x_5426_, 1, v_x_5382_);
v___y_5396_ = v___x_5426_;
goto v___jp_5395_;
}
}
v___jp_5395_:
{
lean_object* v___x_5397_; lean_object* v___x_5399_; 
v___x_5397_ = lean_array_fset(v_xs_x27_5394_, v_j_5386_, v___y_5396_);
lean_dec(v_j_5386_);
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 0, v___x_5397_);
v___x_5399_ = v___x_5390_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
}
else
{
lean_object* v_ks_5429_; lean_object* v_vs_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5448_; 
v_ks_5429_ = lean_ctor_get(v_x_5378_, 0);
v_vs_5430_ = lean_ctor_get(v_x_5378_, 1);
v_isSharedCheck_5448_ = !lean_is_exclusive(v_x_5378_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5432_ = v_x_5378_;
v_isShared_5433_ = v_isSharedCheck_5448_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_vs_5430_);
lean_inc(v_ks_5429_);
lean_dec(v_x_5378_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5448_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_ks_5429_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v_vs_5430_);
v___x_5435_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
lean_object* v_newNode_5436_; size_t v___x_5437_; uint8_t v___x_5438_; 
v_newNode_5436_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5435_, v_x_5381_, v_x_5382_);
v___x_5437_ = ((size_t)7ULL);
v___x_5438_ = lean_usize_dec_le(v___x_5437_, v_x_5380_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; lean_object* v___x_5440_; uint8_t v___x_5441_; 
v___x_5439_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5436_);
v___x_5440_ = lean_unsigned_to_nat(4u);
v___x_5441_ = lean_nat_dec_lt(v___x_5439_, v___x_5440_);
lean_dec(v___x_5439_);
if (v___x_5441_ == 0)
{
lean_object* v_ks_5442_; lean_object* v_vs_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v_ks_5442_ = lean_ctor_get(v_newNode_5436_, 0);
lean_inc_ref(v_ks_5442_);
v_vs_5443_ = lean_ctor_get(v_newNode_5436_, 1);
lean_inc_ref(v_vs_5443_);
lean_dec_ref(v_newNode_5436_);
v___x_5444_ = lean_unsigned_to_nat(0u);
v___x_5445_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5380_, v_ks_5442_, v_vs_5443_, v___x_5444_, v___x_5445_);
lean_dec_ref(v_vs_5443_);
lean_dec_ref(v_ks_5442_);
return v___x_5446_;
}
else
{
return v_newNode_5436_;
}
}
else
{
return v_newNode_5436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(size_t v_depth_5449_, lean_object* v_keys_5450_, lean_object* v_vals_5451_, lean_object* v_i_5452_, lean_object* v_entries_5453_){
_start:
{
lean_object* v___x_5454_; uint8_t v___x_5455_; 
v___x_5454_ = lean_array_get_size(v_keys_5450_);
v___x_5455_ = lean_nat_dec_lt(v_i_5452_, v___x_5454_);
if (v___x_5455_ == 0)
{
lean_dec(v_i_5452_);
return v_entries_5453_;
}
else
{
lean_object* v_k_5456_; lean_object* v_v_5457_; uint64_t v___x_5458_; size_t v_h_5459_; size_t v___x_5460_; lean_object* v___x_5461_; size_t v___x_5462_; size_t v___x_5463_; size_t v___x_5464_; size_t v_h_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
v_k_5456_ = lean_array_fget_borrowed(v_keys_5450_, v_i_5452_);
v_v_5457_ = lean_array_fget_borrowed(v_vals_5451_, v_i_5452_);
v___x_5458_ = l_Lean_instHashableMVarId_hash(v_k_5456_);
v_h_5459_ = lean_uint64_to_usize(v___x_5458_);
v___x_5460_ = ((size_t)5ULL);
v___x_5461_ = lean_unsigned_to_nat(1u);
v___x_5462_ = ((size_t)1ULL);
v___x_5463_ = lean_usize_sub(v_depth_5449_, v___x_5462_);
v___x_5464_ = lean_usize_mul(v___x_5460_, v___x_5463_);
v_h_5465_ = lean_usize_shift_right(v_h_5459_, v___x_5464_);
v___x_5466_ = lean_nat_add(v_i_5452_, v___x_5461_);
lean_dec(v_i_5452_);
lean_inc(v_v_5457_);
lean_inc(v_k_5456_);
v___x_5467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_entries_5453_, v_h_5465_, v_depth_5449_, v_k_5456_, v_v_5457_);
v_i_5452_ = v___x_5466_;
v_entries_5453_ = v___x_5467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_depth_5469_, lean_object* v_keys_5470_, lean_object* v_vals_5471_, lean_object* v_i_5472_, lean_object* v_entries_5473_){
_start:
{
size_t v_depth_boxed_5474_; lean_object* v_res_5475_; 
v_depth_boxed_5474_ = lean_unbox_usize(v_depth_5469_);
lean_dec(v_depth_5469_);
v_res_5475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_boxed_5474_, v_keys_5470_, v_vals_5471_, v_i_5472_, v_entries_5473_);
lean_dec_ref(v_vals_5471_);
lean_dec_ref(v_keys_5470_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___boxed(lean_object* v_x_5476_, lean_object* v_x_5477_, lean_object* v_x_5478_, lean_object* v_x_5479_, lean_object* v_x_5480_){
_start:
{
size_t v_x_66926__boxed_5481_; size_t v_x_66927__boxed_5482_; lean_object* v_res_5483_; 
v_x_66926__boxed_5481_ = lean_unbox_usize(v_x_5477_);
lean_dec(v_x_5477_);
v_x_66927__boxed_5482_ = lean_unbox_usize(v_x_5478_);
lean_dec(v_x_5478_);
v_res_5483_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5476_, v_x_66926__boxed_5481_, v_x_66927__boxed_5482_, v_x_5479_, v_x_5480_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(lean_object* v_x_5484_, lean_object* v_x_5485_, lean_object* v_x_5486_){
_start:
{
uint64_t v___x_5487_; size_t v___x_5488_; size_t v___x_5489_; lean_object* v___x_5490_; 
v___x_5487_ = l_Lean_instHashableMVarId_hash(v_x_5485_);
v___x_5488_ = lean_uint64_to_usize(v___x_5487_);
v___x_5489_ = ((size_t)1ULL);
v___x_5490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5484_, v___x_5488_, v___x_5489_, v_x_5485_, v_x_5486_);
return v___x_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_mvarId_5491_, lean_object* v_val_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v___x_5495_; lean_object* v_mctx_5496_; lean_object* v_cache_5497_; lean_object* v_zetaDeltaFVarIds_5498_; lean_object* v_postponed_5499_; lean_object* v_diag_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5530_; 
v___x_5495_ = lean_st_ref_take(v___y_5493_);
v_mctx_5496_ = lean_ctor_get(v___x_5495_, 0);
v_cache_5497_ = lean_ctor_get(v___x_5495_, 1);
v_zetaDeltaFVarIds_5498_ = lean_ctor_get(v___x_5495_, 2);
v_postponed_5499_ = lean_ctor_get(v___x_5495_, 3);
v_diag_5500_ = lean_ctor_get(v___x_5495_, 4);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5502_ = v___x_5495_;
v_isShared_5503_ = v_isSharedCheck_5530_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_diag_5500_);
lean_inc(v_postponed_5499_);
lean_inc(v_zetaDeltaFVarIds_5498_);
lean_inc(v_cache_5497_);
lean_inc(v_mctx_5496_);
lean_dec(v___x_5495_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5530_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v_depth_5504_; lean_object* v_levelAssignDepth_5505_; lean_object* v_lmvarCounter_5506_; lean_object* v_mvarCounter_5507_; lean_object* v_lDecls_5508_; lean_object* v_decls_5509_; lean_object* v_userNames_5510_; lean_object* v_lAssignment_5511_; lean_object* v_eAssignment_5512_; lean_object* v_dAssignment_5513_; lean_object* v_instanceTypedMVars_5514_; lean_object* v_synthNormMemo_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5529_; 
v_depth_5504_ = lean_ctor_get(v_mctx_5496_, 0);
v_levelAssignDepth_5505_ = lean_ctor_get(v_mctx_5496_, 1);
v_lmvarCounter_5506_ = lean_ctor_get(v_mctx_5496_, 2);
v_mvarCounter_5507_ = lean_ctor_get(v_mctx_5496_, 3);
v_lDecls_5508_ = lean_ctor_get(v_mctx_5496_, 4);
v_decls_5509_ = lean_ctor_get(v_mctx_5496_, 5);
v_userNames_5510_ = lean_ctor_get(v_mctx_5496_, 6);
v_lAssignment_5511_ = lean_ctor_get(v_mctx_5496_, 7);
v_eAssignment_5512_ = lean_ctor_get(v_mctx_5496_, 8);
v_dAssignment_5513_ = lean_ctor_get(v_mctx_5496_, 9);
v_instanceTypedMVars_5514_ = lean_ctor_get(v_mctx_5496_, 10);
v_synthNormMemo_5515_ = lean_ctor_get(v_mctx_5496_, 11);
v_isSharedCheck_5529_ = !lean_is_exclusive(v_mctx_5496_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5517_ = v_mctx_5496_;
v_isShared_5518_ = v_isSharedCheck_5529_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_synthNormMemo_5515_);
lean_inc(v_instanceTypedMVars_5514_);
lean_inc(v_dAssignment_5513_);
lean_inc(v_eAssignment_5512_);
lean_inc(v_lAssignment_5511_);
lean_inc(v_userNames_5510_);
lean_inc(v_decls_5509_);
lean_inc(v_lDecls_5508_);
lean_inc(v_mvarCounter_5507_);
lean_inc(v_lmvarCounter_5506_);
lean_inc(v_levelAssignDepth_5505_);
lean_inc(v_depth_5504_);
lean_dec(v_mctx_5496_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5529_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5522_; 
v___x_5519_ = lean_box(0);
v___x_5520_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5512_, v_mvarId_5491_, v_val_5492_);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 8, v___x_5520_);
v___x_5522_ = v___x_5517_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_depth_5504_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v_levelAssignDepth_5505_);
lean_ctor_set(v_reuseFailAlloc_5528_, 2, v_lmvarCounter_5506_);
lean_ctor_set(v_reuseFailAlloc_5528_, 3, v_mvarCounter_5507_);
lean_ctor_set(v_reuseFailAlloc_5528_, 4, v_lDecls_5508_);
lean_ctor_set(v_reuseFailAlloc_5528_, 5, v_decls_5509_);
lean_ctor_set(v_reuseFailAlloc_5528_, 6, v_userNames_5510_);
lean_ctor_set(v_reuseFailAlloc_5528_, 7, v_lAssignment_5511_);
lean_ctor_set(v_reuseFailAlloc_5528_, 8, v___x_5520_);
lean_ctor_set(v_reuseFailAlloc_5528_, 9, v_dAssignment_5513_);
lean_ctor_set(v_reuseFailAlloc_5528_, 10, v_instanceTypedMVars_5514_);
lean_ctor_set(v_reuseFailAlloc_5528_, 11, v_synthNormMemo_5515_);
v___x_5522_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5524_; 
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 0, v___x_5522_);
v___x_5524_ = v___x_5502_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5522_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_cache_5497_);
lean_ctor_set(v_reuseFailAlloc_5527_, 2, v_zetaDeltaFVarIds_5498_);
lean_ctor_set(v_reuseFailAlloc_5527_, 3, v_postponed_5499_);
lean_ctor_set(v_reuseFailAlloc_5527_, 4, v_diag_5500_);
v___x_5524_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5525_ = lean_st_ref_put(v___y_5493_, v___x_5524_);
v___x_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5519_);
return v___x_5526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5531_, lean_object* v_val_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5531_, v_val_5532_, v___y_5533_);
lean_dec(v___y_5533_);
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5536_, lean_object* v_snd_5537_, uint8_t v_stopAtFirstFailure_5538_, lean_object* v_as_x27_5539_, lean_object* v_b_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
if (lean_obj_tag(v_as_x27_5539_) == 0)
{
lean_object* v___x_5551_; 
lean_dec_ref(v_snd_5537_);
lean_dec_ref(v_kp_5536_);
v___x_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5551_, 0, v_b_5540_);
return v___x_5551_;
}
else
{
lean_object* v_snd_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5658_; 
v_snd_5552_ = lean_ctor_get(v_b_5540_, 1);
v_isSharedCheck_5658_ = !lean_is_exclusive(v_b_5540_);
if (v_isSharedCheck_5658_ == 0)
{
lean_object* v_unused_5659_; 
v_unused_5659_ = lean_ctor_get(v_b_5540_, 0);
lean_dec(v_unused_5659_);
v___x_5554_ = v_b_5540_;
v_isShared_5555_ = v_isSharedCheck_5658_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_snd_5552_);
lean_dec(v_b_5540_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5658_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v_head_5556_; lean_object* v_tail_5557_; lean_object* v_fst_5558_; lean_object* v_snd_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5657_; 
v_head_5556_ = lean_ctor_get(v_as_x27_5539_, 0);
v_tail_5557_ = lean_ctor_get(v_as_x27_5539_, 1);
v_fst_5558_ = lean_ctor_get(v_snd_5552_, 0);
v_snd_5559_ = lean_ctor_get(v_snd_5552_, 1);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_snd_5552_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5561_ = v_snd_5552_;
v_isShared_5562_ = v_isSharedCheck_5657_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_snd_5559_);
lean_inc(v_fst_5558_);
lean_dec(v_snd_5552_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5657_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5563_ = lean_box(0);
lean_inc_ref(v_kp_5536_);
lean_inc(v___y_5549_);
lean_inc_ref(v___y_5548_);
lean_inc(v___y_5547_);
lean_inc_ref(v___y_5546_);
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
lean_inc(v___y_5541_);
lean_inc(v_head_5556_);
v___x_5564_ = lean_apply_11(v_kp_5536_, v_head_5556_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, lean_box(0));
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5648_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5567_ = v___x_5564_;
v_isShared_5568_ = v_isSharedCheck_5648_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5564_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5648_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
if (lean_obj_tag(v_a_5565_) == 0)
{
lean_object* v_seq_5569_; lean_object* v_mvarId_5570_; lean_object* v___x_5571_; 
lean_del_object(v___x_5567_);
v_seq_5569_ = lean_ctor_get(v_a_5565_, 0);
v_mvarId_5570_ = lean_ctor_get(v_head_5556_, 1);
lean_inc(v_mvarId_5570_);
v___x_5571_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5570_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
lean_inc(v_a_5572_);
lean_dec_ref_known(v___x_5571_, 1);
if (lean_obj_tag(v_a_5572_) == 1)
{
lean_object* v_val_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5604_; 
lean_dec_ref(v_kp_5536_);
v_val_5573_ = lean_ctor_get(v_a_5572_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_a_5572_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5575_ = v_a_5572_;
v_isShared_5576_ = v_isSharedCheck_5604_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_val_5573_);
lean_dec(v_a_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5604_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v_mvarId_5577_; lean_object* v___x_5578_; 
v_mvarId_5577_ = lean_ctor_get(v_snd_5537_, 1);
lean_inc(v_mvarId_5577_);
lean_dec_ref(v_snd_5537_);
v___x_5578_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5577_, v_val_5573_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5594_; 
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; 
v_unused_5595_ = lean_ctor_get(v___x_5578_, 0);
lean_dec(v_unused_5595_);
v___x_5580_ = v___x_5578_;
v_isShared_5581_ = v_isSharedCheck_5594_;
goto v_resetjp_5579_;
}
else
{
lean_dec(v___x_5578_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5594_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 0, v_a_5565_);
v___x_5583_ = v___x_5575_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5565_);
v___x_5583_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5585_; 
if (v_isShared_5562_ == 0)
{
v___x_5585_ = v___x_5561_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_fst_5558_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_snd_5559_);
v___x_5585_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5587_; 
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5585_);
lean_ctor_set(v___x_5554_, 0, v___x_5583_);
v___x_5587_ = v___x_5554_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5589_; 
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 0, v___x_5587_);
v___x_5589_ = v___x_5580_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_del_object(v___x_5575_);
lean_dec_ref_known(v_a_5565_, 1);
lean_del_object(v___x_5561_);
lean_dec(v_snd_5559_);
lean_dec(v_fst_5558_);
lean_del_object(v___x_5554_);
v_a_5596_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5578_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5578_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
}
else
{
uint8_t v___x_5605_; 
lean_inc(v_seq_5569_);
lean_dec(v_a_5572_);
lean_dec_ref_known(v_a_5565_, 1);
v___x_5605_ = l_List_isEmpty___redArg(v_seq_5569_);
if (v___x_5605_ == 0)
{
lean_object* v___x_5606_; lean_object* v___x_5608_; 
v___x_5606_ = lean_array_push(v_fst_5558_, v_seq_5569_);
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 0, v___x_5606_);
v___x_5608_ = v___x_5561_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5606_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_snd_5559_);
v___x_5608_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
lean_object* v___x_5610_; 
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5608_);
lean_ctor_set(v___x_5554_, 0, v___x_5563_);
v___x_5610_ = v___x_5554_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5608_);
v___x_5610_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
v_as_x27_5539_ = v_tail_5557_;
v_b_5540_ = v___x_5610_;
goto _start;
}
}
}
else
{
lean_object* v___x_5615_; 
lean_dec(v_seq_5569_);
if (v_isShared_5562_ == 0)
{
v___x_5615_ = v___x_5561_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_fst_5558_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v_snd_5559_);
v___x_5615_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
lean_object* v___x_5617_; 
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5615_);
lean_ctor_set(v___x_5554_, 0, v___x_5563_);
v___x_5617_ = v___x_5554_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
v_as_x27_5539_ = v_tail_5557_;
v_b_5540_ = v___x_5617_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_dec_ref_known(v_a_5565_, 1);
lean_del_object(v___x_5561_);
lean_dec(v_snd_5559_);
lean_dec(v_fst_5558_);
lean_del_object(v___x_5554_);
lean_dec_ref(v_snd_5537_);
lean_dec_ref(v_kp_5536_);
v_a_5621_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5571_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5571_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5538_ == 0)
{
lean_object* v_gs_5629_; lean_object* v___x_5630_; lean_object* v___x_5632_; 
lean_del_object(v___x_5567_);
v_gs_5629_ = lean_ctor_get(v_a_5565_, 0);
lean_inc(v_gs_5629_);
lean_dec_ref_known(v_a_5565_, 1);
v___x_5630_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5559_, v_gs_5629_);
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 1, v___x_5630_);
v___x_5632_ = v___x_5561_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5558_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
lean_object* v___x_5634_; 
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5632_);
lean_ctor_set(v___x_5554_, 0, v___x_5563_);
v___x_5634_ = v___x_5554_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5636_, 1, v___x_5632_);
v___x_5634_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
v_as_x27_5539_ = v_tail_5557_;
v_b_5540_ = v___x_5634_;
goto _start;
}
}
}
else
{
lean_object* v___x_5638_; lean_object* v___x_5640_; 
lean_dec_ref(v_snd_5537_);
lean_dec_ref(v_kp_5536_);
v___x_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5638_, 0, v_a_5565_);
if (v_isShared_5562_ == 0)
{
v___x_5640_ = v___x_5561_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_fst_5558_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_snd_5559_);
v___x_5640_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5642_; 
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5640_);
lean_ctor_set(v___x_5554_, 0, v___x_5638_);
v___x_5642_ = v___x_5554_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v___x_5640_);
v___x_5642_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5644_; 
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 0, v___x_5642_);
v___x_5644_ = v___x_5567_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v___x_5642_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
lean_del_object(v___x_5561_);
lean_dec(v_snd_5559_);
lean_dec(v_fst_5558_);
lean_del_object(v___x_5554_);
lean_dec_ref(v_snd_5537_);
lean_dec_ref(v_kp_5536_);
v_a_5649_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5564_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5564_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5660_, lean_object* v_snd_5661_, lean_object* v_stopAtFirstFailure_5662_, lean_object* v_as_x27_5663_, lean_object* v_b_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5675_; lean_object* v_res_5676_; 
v_stopAtFirstFailure_boxed_5675_ = lean_unbox(v_stopAtFirstFailure_5662_);
v_res_5676_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5660_, v_snd_5661_, v_stopAtFirstFailure_boxed_5675_, v_as_x27_5663_, v_b_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
lean_dec(v___y_5669_);
lean_dec_ref(v___y_5668_);
lean_dec(v___y_5667_);
lean_dec_ref(v___y_5666_);
lean_dec(v___y_5665_);
lean_dec(v_as_x27_5663_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5677_, lean_object* v_c_5678_, lean_object* v___x_5679_, lean_object* v___x_5680_, uint8_t v_isRec_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
if (lean_obj_tag(v_a_5682_) == 0)
{
lean_object* v___x_5684_; 
lean_dec(v___x_5680_);
lean_dec_ref(v___x_5679_);
lean_dec_ref(v_snd_5677_);
v___x_5684_ = lean_array_to_list(v_a_5683_);
return v___x_5684_;
}
else
{
lean_object* v_toGoalState_5685_; lean_object* v_split_5686_; lean_object* v_head_5687_; lean_object* v_tail_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5748_; 
v_toGoalState_5685_ = lean_ctor_get(v_snd_5677_, 0);
lean_inc_ref(v_toGoalState_5685_);
v_split_5686_ = lean_ctor_get(v_toGoalState_5685_, 14);
lean_inc_ref(v_split_5686_);
v_head_5687_ = lean_ctor_get(v_a_5682_, 0);
v_tail_5688_ = lean_ctor_get(v_a_5682_, 1);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_a_5682_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5690_ = v_a_5682_;
v_isShared_5691_ = v_isSharedCheck_5748_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_tail_5688_);
lean_inc(v_head_5687_);
lean_dec(v_a_5682_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5748_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v_nextDeclIdx_5692_; lean_object* v_enodeMap_5693_; lean_object* v_exprs_5694_; lean_object* v_parents_5695_; lean_object* v_congrTable_5696_; lean_object* v_appMap_5697_; lean_object* v_indicesFound_5698_; lean_object* v_toProcess_5699_; uint8_t v_inconsistent_5700_; lean_object* v_nextIdx_5701_; lean_object* v_newRawFacts_5702_; lean_object* v_facts_5703_; lean_object* v_extThms_5704_; lean_object* v_ematch_5705_; lean_object* v_inj_5706_; lean_object* v_clean_5707_; lean_object* v_sstates_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5746_; 
v_nextDeclIdx_5692_ = lean_ctor_get(v_toGoalState_5685_, 0);
v_enodeMap_5693_ = lean_ctor_get(v_toGoalState_5685_, 1);
v_exprs_5694_ = lean_ctor_get(v_toGoalState_5685_, 2);
v_parents_5695_ = lean_ctor_get(v_toGoalState_5685_, 3);
v_congrTable_5696_ = lean_ctor_get(v_toGoalState_5685_, 4);
v_appMap_5697_ = lean_ctor_get(v_toGoalState_5685_, 5);
v_indicesFound_5698_ = lean_ctor_get(v_toGoalState_5685_, 6);
v_toProcess_5699_ = lean_ctor_get(v_toGoalState_5685_, 7);
v_inconsistent_5700_ = lean_ctor_get_uint8(v_toGoalState_5685_, sizeof(void*)*17);
v_nextIdx_5701_ = lean_ctor_get(v_toGoalState_5685_, 8);
v_newRawFacts_5702_ = lean_ctor_get(v_toGoalState_5685_, 9);
v_facts_5703_ = lean_ctor_get(v_toGoalState_5685_, 10);
v_extThms_5704_ = lean_ctor_get(v_toGoalState_5685_, 11);
v_ematch_5705_ = lean_ctor_get(v_toGoalState_5685_, 12);
v_inj_5706_ = lean_ctor_get(v_toGoalState_5685_, 13);
v_clean_5707_ = lean_ctor_get(v_toGoalState_5685_, 15);
v_sstates_5708_ = lean_ctor_get(v_toGoalState_5685_, 16);
v_isSharedCheck_5746_ = !lean_is_exclusive(v_toGoalState_5685_);
if (v_isSharedCheck_5746_ == 0)
{
lean_object* v_unused_5747_; 
v_unused_5747_ = lean_ctor_get(v_toGoalState_5685_, 14);
lean_dec(v_unused_5747_);
v___x_5710_ = v_toGoalState_5685_;
v_isShared_5711_ = v_isSharedCheck_5746_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_sstates_5708_);
lean_inc(v_clean_5707_);
lean_inc(v_inj_5706_);
lean_inc(v_ematch_5705_);
lean_inc(v_extThms_5704_);
lean_inc(v_facts_5703_);
lean_inc(v_newRawFacts_5702_);
lean_inc(v_nextIdx_5701_);
lean_inc(v_toProcess_5699_);
lean_inc(v_indicesFound_5698_);
lean_inc(v_appMap_5697_);
lean_inc(v_congrTable_5696_);
lean_inc(v_parents_5695_);
lean_inc(v_exprs_5694_);
lean_inc(v_enodeMap_5693_);
lean_inc(v_nextDeclIdx_5692_);
lean_dec(v_toGoalState_5685_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5746_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v_num_5712_; lean_object* v_candidates_5713_; lean_object* v_added_5714_; lean_object* v_resolved_5715_; lean_object* v_trace_5716_; lean_object* v_lookaheads_5717_; lean_object* v_argPosMap_5718_; lean_object* v_argsAt_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5745_; 
v_num_5712_ = lean_ctor_get(v_split_5686_, 0);
v_candidates_5713_ = lean_ctor_get(v_split_5686_, 1);
v_added_5714_ = lean_ctor_get(v_split_5686_, 2);
v_resolved_5715_ = lean_ctor_get(v_split_5686_, 3);
v_trace_5716_ = lean_ctor_get(v_split_5686_, 4);
v_lookaheads_5717_ = lean_ctor_get(v_split_5686_, 5);
v_argPosMap_5718_ = lean_ctor_get(v_split_5686_, 6);
v_argsAt_5719_ = lean_ctor_get(v_split_5686_, 7);
v_isSharedCheck_5745_ = !lean_is_exclusive(v_split_5686_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5721_ = v_split_5686_;
v_isShared_5722_ = v_isSharedCheck_5745_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_argsAt_5719_);
lean_inc(v_argPosMap_5718_);
lean_inc(v_lookaheads_5717_);
lean_inc(v_trace_5716_);
lean_inc(v_resolved_5715_);
lean_inc(v_added_5714_);
lean_inc(v_candidates_5713_);
lean_inc(v_num_5712_);
lean_dec(v_split_5686_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5745_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5723_; lean_object* v___y_5725_; lean_object* v___x_5743_; uint8_t v___x_5744_; 
v___x_5723_ = lean_array_get_size(v_a_5683_);
v___x_5743_ = lean_unsigned_to_nat(0u);
v___x_5744_ = lean_nat_dec_lt(v___x_5743_, v___x_5723_);
if (v___x_5744_ == 0)
{
if (v_isRec_5681_ == 0)
{
v___y_5725_ = v_num_5712_;
goto v___jp_5724_;
}
else
{
goto v___jp_5740_;
}
}
else
{
goto v___jp_5740_;
}
v___jp_5724_:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5729_; 
v___x_5726_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5678_);
lean_inc(v___x_5680_);
lean_inc_ref(v___x_5679_);
v___x_5727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5679_);
lean_ctor_set(v___x_5727_, 1, v___x_5723_);
lean_ctor_set(v___x_5727_, 2, v___x_5680_);
lean_ctor_set(v___x_5727_, 3, v___x_5726_);
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 1, v_trace_5716_);
lean_ctor_set(v___x_5690_, 0, v___x_5727_);
v___x_5729_ = v___x_5690_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5727_);
lean_ctor_set(v_reuseFailAlloc_5739_, 1, v_trace_5716_);
v___x_5729_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
lean_object* v___x_5731_; 
if (v_isShared_5722_ == 0)
{
lean_ctor_set(v___x_5721_, 4, v___x_5729_);
lean_ctor_set(v___x_5721_, 0, v___y_5725_);
v___x_5731_ = v___x_5721_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___y_5725_);
lean_ctor_set(v_reuseFailAlloc_5738_, 1, v_candidates_5713_);
lean_ctor_set(v_reuseFailAlloc_5738_, 2, v_added_5714_);
lean_ctor_set(v_reuseFailAlloc_5738_, 3, v_resolved_5715_);
lean_ctor_set(v_reuseFailAlloc_5738_, 4, v___x_5729_);
lean_ctor_set(v_reuseFailAlloc_5738_, 5, v_lookaheads_5717_);
lean_ctor_set(v_reuseFailAlloc_5738_, 6, v_argPosMap_5718_);
lean_ctor_set(v_reuseFailAlloc_5738_, 7, v_argsAt_5719_);
v___x_5731_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
lean_object* v___x_5733_; 
if (v_isShared_5711_ == 0)
{
lean_ctor_set(v___x_5710_, 14, v___x_5731_);
v___x_5733_ = v___x_5710_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_nextDeclIdx_5692_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v_enodeMap_5693_);
lean_ctor_set(v_reuseFailAlloc_5737_, 2, v_exprs_5694_);
lean_ctor_set(v_reuseFailAlloc_5737_, 3, v_parents_5695_);
lean_ctor_set(v_reuseFailAlloc_5737_, 4, v_congrTable_5696_);
lean_ctor_set(v_reuseFailAlloc_5737_, 5, v_appMap_5697_);
lean_ctor_set(v_reuseFailAlloc_5737_, 6, v_indicesFound_5698_);
lean_ctor_set(v_reuseFailAlloc_5737_, 7, v_toProcess_5699_);
lean_ctor_set(v_reuseFailAlloc_5737_, 8, v_nextIdx_5701_);
lean_ctor_set(v_reuseFailAlloc_5737_, 9, v_newRawFacts_5702_);
lean_ctor_set(v_reuseFailAlloc_5737_, 10, v_facts_5703_);
lean_ctor_set(v_reuseFailAlloc_5737_, 11, v_extThms_5704_);
lean_ctor_set(v_reuseFailAlloc_5737_, 12, v_ematch_5705_);
lean_ctor_set(v_reuseFailAlloc_5737_, 13, v_inj_5706_);
lean_ctor_set(v_reuseFailAlloc_5737_, 14, v___x_5731_);
lean_ctor_set(v_reuseFailAlloc_5737_, 15, v_clean_5707_);
lean_ctor_set(v_reuseFailAlloc_5737_, 16, v_sstates_5708_);
lean_ctor_set_uint8(v_reuseFailAlloc_5737_, sizeof(void*)*17, v_inconsistent_5700_);
v___x_5733_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5733_);
lean_ctor_set(v___x_5734_, 1, v_head_5687_);
v___x_5735_ = lean_array_push(v_a_5683_, v___x_5734_);
v_a_5682_ = v_tail_5688_;
v_a_5683_ = v___x_5735_;
goto _start;
}
}
}
}
v___jp_5740_:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5741_ = lean_unsigned_to_nat(1u);
v___x_5742_ = lean_nat_add(v_num_5712_, v___x_5741_);
lean_dec(v_num_5712_);
v___y_5725_ = v___x_5742_;
goto v___jp_5724_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5749_, lean_object* v_c_5750_, lean_object* v___x_5751_, lean_object* v___x_5752_, lean_object* v_isRec_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_){
_start:
{
uint8_t v_isRec_boxed_5756_; lean_object* v_res_5757_; 
v_isRec_boxed_5756_ = lean_unbox(v_isRec_5753_);
v_res_5757_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5749_, v_c_5750_, v___x_5751_, v___x_5752_, v_isRec_boxed_5756_, v_a_5754_, v_a_5755_);
lean_dec_ref(v_c_5750_);
return v_res_5757_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; 
v___x_5769_ = lean_box(0);
v___x_5770_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5771_ = l_Lean_mkConst(v___x_5770_, v___x_5769_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5772_, lean_object* v_numCases_5773_, uint8_t v_isRec_5774_, uint8_t v_stopAtFirstFailure_5775_, uint8_t v_compress_5776_, lean_object* v_candidates_x3f_5777_, lean_object* v_goal_5778_, lean_object* v_kp_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v___x_5790_; 
v___x_5790_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5781_);
if (lean_obj_tag(v___x_5790_) == 0)
{
lean_object* v_a_5791_; uint8_t v_trace_5792_; lean_object* v___x_5793_; 
v_a_5791_ = lean_ctor_get(v___x_5790_, 0);
lean_inc(v_a_5791_);
lean_dec_ref_known(v___x_5790_, 1);
v_trace_5792_ = lean_ctor_get_uint8(v_a_5791_, sizeof(void*)*14);
lean_dec(v_a_5791_);
lean_inc_ref(v_goal_5778_);
v___x_5793_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5778_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v_mvarId_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___f_5798_; lean_object* v___x_5799_; lean_object* v___f_5800_; lean_object* v___x_5801_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc_n(v_a_5794_, 2);
lean_dec_ref_known(v___x_5793_, 1);
v_mvarId_5795_ = lean_ctor_get(v_goal_5778_, 1);
lean_inc(v_mvarId_5795_);
v___x_5796_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5772_);
v___x_5797_ = lean_box(v_isRec_5774_);
lean_inc_ref_n(v_c_5772_, 2);
lean_inc_ref(v___x_5796_);
v___f_5798_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5798_, 0, v___x_5796_);
lean_closure_set(v___f_5798_, 1, v_c_5772_);
lean_closure_set(v___f_5798_, 2, v_a_5794_);
lean_closure_set(v___f_5798_, 3, v_numCases_5773_);
lean_closure_set(v___f_5798_, 4, v___x_5797_);
v___x_5799_ = lean_box(v_trace_5792_);
v___f_5800_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5800_, 0, v_goal_5778_);
lean_closure_set(v___f_5800_, 1, v___x_5799_);
lean_closure_set(v___f_5800_, 2, v___f_5798_);
lean_closure_set(v___f_5800_, 3, v_c_5772_);
lean_closure_set(v___f_5800_, 4, v_candidates_x3f_5777_);
v___x_5801_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5795_, v___f_5800_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v_fst_5803_; lean_object* v_snd_5804_; lean_object* v_fst_5805_; lean_object* v_snd_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
lean_inc(v_a_5802_);
lean_dec_ref_known(v___x_5801_, 1);
v_fst_5803_ = lean_ctor_get(v_a_5802_, 0);
lean_inc(v_fst_5803_);
v_snd_5804_ = lean_ctor_get(v_a_5802_, 1);
lean_inc_n(v_snd_5804_, 3);
lean_dec(v_a_5802_);
v_fst_5805_ = lean_ctor_get(v_fst_5803_, 0);
lean_inc(v_fst_5805_);
v_snd_5806_ = lean_ctor_get(v_fst_5803_, 1);
lean_inc(v_snd_5806_);
lean_dec(v_fst_5803_);
v___x_5807_ = l_List_lengthTR___redArg(v_fst_5805_);
v___x_5808_ = lean_unsigned_to_nat(0u);
v___x_5809_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5810_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5804_, v_c_5772_, v___x_5796_, v___x_5807_, v_isRec_5774_, v_fst_5805_, v___x_5809_);
lean_dec_ref(v_c_5772_);
v___x_5811_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5812_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5779_, v_snd_5804_, v_stopAtFirstFailure_5775_, v___x_5810_, v___x_5811_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
lean_dec(v___x_5810_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5896_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5815_ = v___x_5812_;
v_isShared_5816_ = v_isSharedCheck_5896_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5812_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5896_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v_fst_5817_; 
v_fst_5817_ = lean_ctor_get(v_a_5813_, 0);
if (lean_obj_tag(v_fst_5817_) == 0)
{
lean_object* v_snd_5818_; lean_object* v_fst_5819_; lean_object* v_snd_5820_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v_mvarId_5870_; lean_object* v___x_5871_; 
v_snd_5818_ = lean_ctor_get(v_a_5813_, 1);
lean_inc(v_snd_5818_);
lean_dec(v_a_5813_);
v_fst_5819_ = lean_ctor_get(v_snd_5818_, 0);
lean_inc(v_fst_5819_);
v_snd_5820_ = lean_ctor_get(v_snd_5818_, 1);
lean_inc(v_snd_5820_);
lean_dec(v_snd_5818_);
v_mvarId_5870_ = lean_ctor_get(v_snd_5804_, 1);
lean_inc_n(v_mvarId_5870_, 2);
lean_dec(v_snd_5804_);
v___x_5871_ = l_Lean_MVarId_getType(v_mvarId_5870_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v_a_5872_; uint8_t v___x_5873_; 
v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_a_5872_);
lean_dec_ref_known(v___x_5871_, 1);
v___x_5873_ = l_Lean_Expr_isFalse(v_a_5872_);
if (v___x_5873_ == 0)
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v_a_5876_; lean_object* v___x_5877_; 
v___x_5874_ = l_Lean_mkMVar(v_a_5794_);
v___x_5875_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5874_, v_a_5786_);
v_a_5876_ = lean_ctor_get(v___x_5875_, 0);
lean_inc(v_a_5876_);
lean_dec_ref(v___x_5875_);
v___x_5877_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5870_, v_a_5876_, v_a_5786_);
lean_dec_ref(v___x_5877_);
v___y_5822_ = v_a_5787_;
v___y_5823_ = v_a_5788_;
goto v___jp_5821_;
}
else
{
lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v_a_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; 
v___x_5878_ = l_Lean_mkMVar(v_a_5794_);
v___x_5879_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5878_, v_a_5786_);
v_a_5880_ = lean_ctor_get(v___x_5879_, 0);
lean_inc(v_a_5880_);
lean_dec_ref(v___x_5879_);
v___x_5881_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5882_ = l_Lean_Meta_mkExpectedPropHint(v_a_5880_, v___x_5881_);
v___x_5883_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5870_, v___x_5882_, v_a_5786_);
lean_dec_ref(v___x_5883_);
v___y_5822_ = v_a_5787_;
v___y_5823_ = v_a_5788_;
goto v___jp_5821_;
}
}
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_dec(v_mvarId_5870_);
lean_dec(v_snd_5820_);
lean_dec(v_fst_5819_);
lean_del_object(v___x_5815_);
lean_dec(v_snd_5806_);
lean_dec(v_a_5794_);
v_a_5884_ = lean_ctor_get(v___x_5871_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5871_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5871_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5871_);
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
v___jp_5821_:
{
lean_object* v___x_5824_; uint8_t v___x_5825_; 
v___x_5824_ = lean_array_get_size(v_snd_5820_);
v___x_5825_ = lean_nat_dec_eq(v___x_5824_, v___x_5808_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5829_; 
lean_dec(v_fst_5819_);
lean_dec(v_snd_5806_);
v___x_5826_ = lean_array_to_list(v_snd_5820_);
v___x_5827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5826_);
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 0, v___x_5827_);
v___x_5829_ = v___x_5815_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5827_);
v___x_5829_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
return v___x_5829_;
}
}
else
{
lean_dec(v_snd_5820_);
if (lean_obj_tag(v_snd_5806_) == 1)
{
lean_object* v_val_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5865_; 
lean_del_object(v___x_5815_);
v_val_5831_ = lean_ctor_get(v_snd_5806_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v_snd_5806_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5833_ = v_snd_5806_;
v_isShared_5834_ = v_isSharedCheck_5865_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_val_5831_);
lean_dec(v_snd_5806_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5865_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v___x_5835_; 
v___x_5835_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5831_, v___y_5822_);
lean_dec(v_val_5831_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v_a_5836_; lean_object* v___x_5837_; 
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
lean_inc(v_a_5836_);
lean_dec_ref_known(v___x_5835_, 1);
v___x_5837_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5836_, v_fst_5819_, v_compress_5776_, v___y_5822_, v___y_5823_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5848_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5840_ = v___x_5837_;
v_isShared_5841_ = v_isSharedCheck_5848_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5837_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5848_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set_tag(v___x_5833_, 0);
lean_ctor_set(v___x_5833_, 0, v_a_5838_);
v___x_5843_ = v___x_5833_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
lean_object* v___x_5845_; 
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 0, v___x_5843_);
v___x_5845_ = v___x_5840_;
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
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_del_object(v___x_5833_);
v_a_5849_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5837_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5837_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
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
lean_object* v_a_5857_; lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5864_; 
lean_del_object(v___x_5833_);
lean_dec(v_fst_5819_);
v_a_5857_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5864_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5859_ = v___x_5835_;
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
else
{
lean_inc(v_a_5857_);
lean_dec(v___x_5835_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
lean_object* v___x_5862_; 
if (v_isShared_5860_ == 0)
{
v___x_5862_ = v___x_5859_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
v___x_5862_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5861_;
}
v_reusejp_5861_:
{
return v___x_5862_;
}
}
}
}
}
else
{
lean_object* v___x_5866_; lean_object* v___x_5868_; 
lean_dec(v_fst_5819_);
lean_dec(v_snd_5806_);
v___x_5866_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 0, v___x_5866_);
v___x_5868_ = v___x_5815_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v___x_5866_);
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
}
else
{
lean_object* v_val_5892_; lean_object* v___x_5894_; 
lean_inc_ref(v_fst_5817_);
lean_dec(v_a_5813_);
lean_dec(v_snd_5806_);
lean_dec(v_snd_5804_);
lean_dec(v_a_5794_);
v_val_5892_ = lean_ctor_get(v_fst_5817_, 0);
lean_inc(v_val_5892_);
lean_dec_ref_known(v_fst_5817_, 1);
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 0, v_val_5892_);
v___x_5894_ = v___x_5815_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_val_5892_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec(v_snd_5806_);
lean_dec(v_snd_5804_);
lean_dec(v_a_5794_);
v_a_5897_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5812_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5812_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec_ref(v___x_5796_);
lean_dec(v_a_5794_);
lean_dec_ref(v_kp_5779_);
lean_dec_ref(v_c_5772_);
v_a_5905_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5801_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5801_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
lean_dec_ref(v_kp_5779_);
lean_dec_ref(v_goal_5778_);
lean_dec(v_candidates_x3f_5777_);
lean_dec(v_numCases_5773_);
lean_dec_ref(v_c_5772_);
v_a_5913_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5793_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5793_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
}
else
{
lean_object* v_a_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5928_; 
lean_dec_ref(v_kp_5779_);
lean_dec_ref(v_goal_5778_);
lean_dec(v_candidates_x3f_5777_);
lean_dec(v_numCases_5773_);
lean_dec_ref(v_c_5772_);
v_a_5921_ = lean_ctor_get(v___x_5790_, 0);
v_isSharedCheck_5928_ = !lean_is_exclusive(v___x_5790_);
if (v_isSharedCheck_5928_ == 0)
{
v___x_5923_ = v___x_5790_;
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_a_5921_);
lean_dec(v___x_5790_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5928_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5926_; 
if (v_isShared_5924_ == 0)
{
v___x_5926_ = v___x_5923_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_a_5921_);
v___x_5926_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
return v___x_5926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5929_ = _args[0];
lean_object* v_numCases_5930_ = _args[1];
lean_object* v_isRec_5931_ = _args[2];
lean_object* v_stopAtFirstFailure_5932_ = _args[3];
lean_object* v_compress_5933_ = _args[4];
lean_object* v_candidates_x3f_5934_ = _args[5];
lean_object* v_goal_5935_ = _args[6];
lean_object* v_kp_5936_ = _args[7];
lean_object* v_a_5937_ = _args[8];
lean_object* v_a_5938_ = _args[9];
lean_object* v_a_5939_ = _args[10];
lean_object* v_a_5940_ = _args[11];
lean_object* v_a_5941_ = _args[12];
lean_object* v_a_5942_ = _args[13];
lean_object* v_a_5943_ = _args[14];
lean_object* v_a_5944_ = _args[15];
lean_object* v_a_5945_ = _args[16];
lean_object* v_a_5946_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5947_; uint8_t v_stopAtFirstFailure_boxed_5948_; uint8_t v_compress_boxed_5949_; lean_object* v_res_5950_; 
v_isRec_boxed_5947_ = lean_unbox(v_isRec_5931_);
v_stopAtFirstFailure_boxed_5948_ = lean_unbox(v_stopAtFirstFailure_5932_);
v_compress_boxed_5949_ = lean_unbox(v_compress_5933_);
v_res_5950_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5929_, v_numCases_5930_, v_isRec_boxed_5947_, v_stopAtFirstFailure_boxed_5948_, v_compress_boxed_5949_, v_candidates_x3f_5934_, v_goal_5935_, v_kp_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_);
lean_dec(v_a_5945_);
lean_dec_ref(v_a_5944_);
lean_dec(v_a_5943_);
lean_dec_ref(v_a_5942_);
lean_dec(v_a_5941_);
lean_dec_ref(v_a_5940_);
lean_dec(v_a_5939_);
lean_dec_ref(v_a_5938_);
lean_dec(v_a_5937_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5951_, lean_object* v_numCases_5952_, uint8_t v_isRec_5953_, uint8_t v_stopAtFirstFailure_5954_, uint8_t v_compress_5955_, lean_object* v_candidates_x3f_5956_, lean_object* v_goal_5957_, lean_object* v_x_5958_, lean_object* v_kp_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5951_, v_numCases_5952_, v_isRec_5953_, v_stopAtFirstFailure_5954_, v_compress_5955_, v_candidates_x3f_5956_, v_goal_5957_, v_kp_5959_, v_a_5960_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5971_ = _args[0];
lean_object* v_numCases_5972_ = _args[1];
lean_object* v_isRec_5973_ = _args[2];
lean_object* v_stopAtFirstFailure_5974_ = _args[3];
lean_object* v_compress_5975_ = _args[4];
lean_object* v_candidates_x3f_5976_ = _args[5];
lean_object* v_goal_5977_ = _args[6];
lean_object* v_x_5978_ = _args[7];
lean_object* v_kp_5979_ = _args[8];
lean_object* v_a_5980_ = _args[9];
lean_object* v_a_5981_ = _args[10];
lean_object* v_a_5982_ = _args[11];
lean_object* v_a_5983_ = _args[12];
lean_object* v_a_5984_ = _args[13];
lean_object* v_a_5985_ = _args[14];
lean_object* v_a_5986_ = _args[15];
lean_object* v_a_5987_ = _args[16];
lean_object* v_a_5988_ = _args[17];
lean_object* v_a_5989_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5990_; uint8_t v_stopAtFirstFailure_boxed_5991_; uint8_t v_compress_boxed_5992_; lean_object* v_res_5993_; 
v_isRec_boxed_5990_ = lean_unbox(v_isRec_5973_);
v_stopAtFirstFailure_boxed_5991_ = lean_unbox(v_stopAtFirstFailure_5974_);
v_compress_boxed_5992_ = lean_unbox(v_compress_5975_);
v_res_5993_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5971_, v_numCases_5972_, v_isRec_boxed_5990_, v_stopAtFirstFailure_boxed_5991_, v_compress_boxed_5992_, v_candidates_x3f_5976_, v_goal_5977_, v_x_5978_, v_kp_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_);
lean_dec(v_a_5988_);
lean_dec_ref(v_a_5987_);
lean_dec(v_a_5986_);
lean_dec_ref(v_a_5985_);
lean_dec(v_a_5984_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec_ref(v_a_5981_);
lean_dec(v_a_5980_);
lean_dec_ref(v_x_5978_);
return v_res_5993_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5994_, lean_object* v_snd_5995_, uint8_t v_stopAtFirstFailure_5996_, lean_object* v_as_5997_, lean_object* v_as_x27_5998_, lean_object* v_b_5999_, lean_object* v_a_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_){
_start:
{
lean_object* v___x_6011_; 
v___x_6011_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5994_, v_snd_5995_, v_stopAtFirstFailure_5996_, v_as_x27_5998_, v_b_5999_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
return v___x_6011_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_6012_ = _args[0];
lean_object* v_snd_6013_ = _args[1];
lean_object* v_stopAtFirstFailure_6014_ = _args[2];
lean_object* v_as_6015_ = _args[3];
lean_object* v_as_x27_6016_ = _args[4];
lean_object* v_b_6017_ = _args[5];
lean_object* v_a_6018_ = _args[6];
lean_object* v___y_6019_ = _args[7];
lean_object* v___y_6020_ = _args[8];
lean_object* v___y_6021_ = _args[9];
lean_object* v___y_6022_ = _args[10];
lean_object* v___y_6023_ = _args[11];
lean_object* v___y_6024_ = _args[12];
lean_object* v___y_6025_ = _args[13];
lean_object* v___y_6026_ = _args[14];
lean_object* v___y_6027_ = _args[15];
lean_object* v___y_6028_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6029_; lean_object* v_res_6030_; 
v_stopAtFirstFailure_boxed_6029_ = lean_unbox(v_stopAtFirstFailure_6014_);
v_res_6030_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_6012_, v_snd_6013_, v_stopAtFirstFailure_boxed_6029_, v_as_6015_, v_as_x27_6016_, v_b_6017_, v_a_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec_ref(v___y_6022_);
lean_dec(v___y_6021_);
lean_dec_ref(v___y_6020_);
lean_dec(v___y_6019_);
lean_dec(v_as_x27_6016_);
lean_dec(v_as_6015_);
return v_res_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6031_, lean_object* v_val_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6031_, v_val_6032_, v___y_6039_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6044_, lean_object* v_val_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_){
_start:
{
lean_object* v_res_6056_; 
v_res_6056_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6044_, v_val_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v___y_6046_);
return v_res_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6057_, lean_object* v_x_6058_, lean_object* v_x_6059_, lean_object* v_x_6060_){
_start:
{
lean_object* v___x_6061_; 
v___x_6061_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6058_, v_x_6059_, v_x_6060_);
return v___x_6061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6062_, lean_object* v_x_6063_, size_t v_x_6064_, size_t v_x_6065_, lean_object* v_x_6066_, lean_object* v_x_6067_){
_start:
{
lean_object* v___x_6068_; 
v___x_6068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6063_, v_x_6064_, v_x_6065_, v_x_6066_, v_x_6067_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6069_, lean_object* v_x_6070_, lean_object* v_x_6071_, lean_object* v_x_6072_, lean_object* v_x_6073_, lean_object* v_x_6074_){
_start:
{
size_t v_x_67873__boxed_6075_; size_t v_x_67874__boxed_6076_; lean_object* v_res_6077_; 
v_x_67873__boxed_6075_ = lean_unbox_usize(v_x_6071_);
lean_dec(v_x_6071_);
v_x_67874__boxed_6076_ = lean_unbox_usize(v_x_6072_);
lean_dec(v_x_6072_);
v_res_6077_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6069_, v_x_6070_, v_x_67873__boxed_6075_, v_x_67874__boxed_6076_, v_x_6073_, v_x_6074_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6078_, lean_object* v_n_6079_, lean_object* v_k_6080_, lean_object* v_v_6081_){
_start:
{
lean_object* v___x_6082_; 
v___x_6082_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6079_, v_k_6080_, v_v_6081_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6083_, size_t v_depth_6084_, lean_object* v_keys_6085_, lean_object* v_vals_6086_, lean_object* v_heq_6087_, lean_object* v_i_6088_, lean_object* v_entries_6089_){
_start:
{
lean_object* v___x_6090_; 
v___x_6090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6084_, v_keys_6085_, v_vals_6086_, v_i_6088_, v_entries_6089_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6091_, lean_object* v_depth_6092_, lean_object* v_keys_6093_, lean_object* v_vals_6094_, lean_object* v_heq_6095_, lean_object* v_i_6096_, lean_object* v_entries_6097_){
_start:
{
size_t v_depth_boxed_6098_; lean_object* v_res_6099_; 
v_depth_boxed_6098_ = lean_unbox_usize(v_depth_6092_);
lean_dec(v_depth_6092_);
v_res_6099_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6091_, v_depth_boxed_6098_, v_keys_6093_, v_vals_6094_, v_heq_6095_, v_i_6096_, v_entries_6097_);
lean_dec_ref(v_vals_6094_);
lean_dec_ref(v_keys_6093_);
return v_res_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6100_, lean_object* v_x_6101_, lean_object* v_x_6102_, lean_object* v_x_6103_, lean_object* v_x_6104_){
_start:
{
lean_object* v___x_6105_; 
v___x_6105_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6101_, v_x_6102_, v_x_6103_, v_x_6104_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6106_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6121_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6145_ = lean_st_mk_ref(v_goal_6134_);
v___x_6146_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6145_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_);
if (lean_obj_tag(v___x_6146_) == 0)
{
lean_object* v_a_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6156_; 
v_a_6147_ = lean_ctor_get(v___x_6146_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v___x_6146_);
if (v_isSharedCheck_6156_ == 0)
{
v___x_6149_ = v___x_6146_;
v_isShared_6150_ = v_isSharedCheck_6156_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_a_6147_);
lean_dec(v___x_6146_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6156_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6154_; 
v___x_6151_ = lean_st_ref_get(v___x_6145_);
lean_dec(v___x_6145_);
v___x_6152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6152_, 0, v_a_6147_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 0, v___x_6152_);
v___x_6154_ = v___x_6149_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6152_);
v___x_6154_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
return v___x_6154_;
}
}
}
else
{
lean_object* v_a_6157_; lean_object* v___x_6159_; uint8_t v_isShared_6160_; uint8_t v_isSharedCheck_6164_; 
lean_dec(v___x_6145_);
v_a_6157_ = lean_ctor_get(v___x_6146_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6146_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6159_ = v___x_6146_;
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
else
{
lean_inc(v_a_6157_);
lean_dec(v___x_6146_);
v___x_6159_ = lean_box(0);
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
v_resetjp_6158_:
{
lean_object* v___x_6162_; 
if (v_isShared_6160_ == 0)
{
v___x_6162_ = v___x_6159_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
v___x_6162_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
return v___x_6162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_){
_start:
{
lean_object* v_res_6176_; 
v_res_6176_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_);
lean_dec(v___y_6174_);
lean_dec_ref(v___y_6173_);
lean_dec(v___y_6172_);
lean_dec_ref(v___y_6171_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
return v_res_6176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6177_, lean_object* v___f_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6192_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6192_, 0, v___y_6177_);
v___x_6193_ = l_Lean_Meta_Grind_Action_andThen(v___x_6192_, v___f_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6194_, lean_object* v___f_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v_res_6209_; 
v_res_6209_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6194_, v___f_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6204_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6202_);
lean_dec(v___y_6201_);
lean_dec_ref(v___y_6200_);
lean_dec(v___y_6199_);
return v_res_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6211_, uint8_t v_compress_6212_, lean_object* v_goal_6213_, lean_object* v_kna_6214_, lean_object* v_kp_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_){
_start:
{
lean_object* v_toGoalState_6226_; lean_object* v_split_6227_; lean_object* v_mvarId_6228_; lean_object* v_candidates_6229_; lean_object* v___f_6230_; lean_object* v___f_6231_; lean_object* v___x_6232_; 
v_toGoalState_6226_ = lean_ctor_get(v_goal_6213_, 0);
v_split_6227_ = lean_ctor_get(v_toGoalState_6226_, 14);
v_mvarId_6228_ = lean_ctor_get(v_goal_6213_, 1);
lean_inc(v_mvarId_6228_);
v_candidates_6229_ = lean_ctor_get(v_split_6227_, 1);
lean_inc(v_candidates_6229_);
v___f_6230_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6231_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6231_, 0, v_goal_6213_);
v___x_6232_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6228_, v___f_6231_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_);
if (lean_obj_tag(v___x_6232_) == 0)
{
lean_object* v_a_6233_; lean_object* v_fst_6234_; 
v_a_6233_ = lean_ctor_get(v___x_6232_, 0);
lean_inc(v_a_6233_);
lean_dec_ref_known(v___x_6232_, 1);
v_fst_6234_ = lean_ctor_get(v_a_6233_, 0);
if (lean_obj_tag(v_fst_6234_) == 1)
{
lean_object* v_snd_6235_; lean_object* v_c_6236_; lean_object* v_numCases_6237_; uint8_t v_isRec_6238_; lean_object* v___y_6240_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; uint8_t v___x_6253_; 
lean_inc_ref(v_fst_6234_);
v_snd_6235_ = lean_ctor_get(v_a_6233_, 1);
lean_inc(v_snd_6235_);
lean_dec(v_a_6233_);
v_c_6236_ = lean_ctor_get(v_fst_6234_, 0);
lean_inc_ref(v_c_6236_);
v_numCases_6237_ = lean_ctor_get(v_fst_6234_, 1);
lean_inc(v_numCases_6237_);
v_isRec_6238_ = lean_ctor_get_uint8(v_fst_6234_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6234_, 2);
v___x_6248_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6236_);
v___x_6249_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6235_, v___x_6248_);
lean_dec_ref(v___x_6248_);
v___x_6250_ = lean_unsigned_to_nat(1u);
v___x_6253_ = lean_nat_dec_lt(v___x_6250_, v_numCases_6237_);
if (v___x_6253_ == 0)
{
if (v_isRec_6238_ == 0)
{
v___y_6240_ = v___x_6249_;
goto v___jp_6239_;
}
else
{
goto v___jp_6251_;
}
}
else
{
goto v___jp_6251_;
}
v___jp_6239_:
{
lean_object* v___f_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; 
v___f_6241_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6241_, 0, v___y_6240_);
lean_closure_set(v___f_6241_, 1, v___f_6230_);
v___x_6242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6242_, 0, v_candidates_6229_);
v___x_6243_ = lean_box(v_isRec_6238_);
v___x_6244_ = lean_box(v_stopAtFirstFailure_6211_);
v___x_6245_ = lean_box(v_compress_6212_);
v___x_6246_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6246_, 0, v_c_6236_);
lean_closure_set(v___x_6246_, 1, v_numCases_6237_);
lean_closure_set(v___x_6246_, 2, v___x_6243_);
lean_closure_set(v___x_6246_, 3, v___x_6244_);
lean_closure_set(v___x_6246_, 4, v___x_6245_);
lean_closure_set(v___x_6246_, 5, v___x_6242_);
v___x_6247_ = l_Lean_Meta_Grind_Action_andThen(v___x_6246_, v___f_6241_, v_snd_6235_, v_kna_6214_, v_kp_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_);
return v___x_6247_;
}
v___jp_6251_:
{
lean_object* v___x_6252_; 
v___x_6252_ = lean_nat_add(v___x_6249_, v___x_6250_);
lean_dec(v___x_6249_);
v___y_6240_ = v___x_6252_;
goto v___jp_6239_;
}
}
else
{
lean_object* v_snd_6254_; lean_object* v___x_6255_; 
lean_dec(v_candidates_6229_);
lean_dec_ref(v_kp_6215_);
v_snd_6254_ = lean_ctor_get(v_a_6233_, 1);
lean_inc(v_snd_6254_);
lean_dec(v_a_6233_);
lean_inc(v_a_6224_);
lean_inc_ref(v_a_6223_);
lean_inc(v_a_6222_);
lean_inc_ref(v_a_6221_);
lean_inc(v_a_6220_);
lean_inc_ref(v_a_6219_);
lean_inc(v_a_6218_);
lean_inc_ref(v_a_6217_);
lean_inc(v_a_6216_);
v___x_6255_ = lean_apply_11(v_kna_6214_, v_snd_6254_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_, lean_box(0));
return v___x_6255_;
}
}
else
{
lean_object* v_a_6256_; lean_object* v___x_6258_; uint8_t v_isShared_6259_; uint8_t v_isSharedCheck_6263_; 
lean_dec(v_candidates_6229_);
lean_dec_ref(v_kp_6215_);
lean_dec_ref(v_kna_6214_);
v_a_6256_ = lean_ctor_get(v___x_6232_, 0);
v_isSharedCheck_6263_ = !lean_is_exclusive(v___x_6232_);
if (v_isSharedCheck_6263_ == 0)
{
v___x_6258_ = v___x_6232_;
v_isShared_6259_ = v_isSharedCheck_6263_;
goto v_resetjp_6257_;
}
else
{
lean_inc(v_a_6256_);
lean_dec(v___x_6232_);
v___x_6258_ = lean_box(0);
v_isShared_6259_ = v_isSharedCheck_6263_;
goto v_resetjp_6257_;
}
v_resetjp_6257_:
{
lean_object* v___x_6261_; 
if (v_isShared_6259_ == 0)
{
v___x_6261_ = v___x_6258_;
goto v_reusejp_6260_;
}
else
{
lean_object* v_reuseFailAlloc_6262_; 
v_reuseFailAlloc_6262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6262_, 0, v_a_6256_);
v___x_6261_ = v_reuseFailAlloc_6262_;
goto v_reusejp_6260_;
}
v_reusejp_6260_:
{
return v___x_6261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6264_, lean_object* v_compress_6265_, lean_object* v_goal_6266_, lean_object* v_kna_6267_, lean_object* v_kp_6268_, lean_object* v_a_6269_, lean_object* v_a_6270_, lean_object* v_a_6271_, lean_object* v_a_6272_, lean_object* v_a_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_, lean_object* v_a_6276_, lean_object* v_a_6277_, lean_object* v_a_6278_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6279_; uint8_t v_compress_boxed_6280_; lean_object* v_res_6281_; 
v_stopAtFirstFailure_boxed_6279_ = lean_unbox(v_stopAtFirstFailure_6264_);
v_compress_boxed_6280_ = lean_unbox(v_compress_6265_);
v_res_6281_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6279_, v_compress_boxed_6280_, v_goal_6266_, v_kna_6267_, v_kp_6268_, v_a_6269_, v_a_6270_, v_a_6271_, v_a_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_);
lean_dec(v_a_6277_);
lean_dec_ref(v_a_6276_);
lean_dec(v_a_6275_);
lean_dec_ref(v_a_6274_);
lean_dec(v_a_6273_);
lean_dec_ref(v_a_6272_);
lean_dec(v_a_6271_);
lean_dec_ref(v_a_6270_);
lean_dec(v_a_6269_);
return v_res_6281_;
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
