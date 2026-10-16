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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
if (v_isRec_58_ == 0)
{
return v_isRec_58_;
}
else
{
v___y_64_ = v_isRec_58_;
goto v___jp_63_;
}
}
}
v___jp_63_:
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
lean_object* v___x_153_; 
lean_inc_ref(v_c_142_);
v___x_153_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; uint8_t v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = lean_unbox(v_a_154_);
lean_dec(v_a_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_169_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_169_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_a_157_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; uint8_t v___x_165_; lean_object* v___x_167_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___x_164_ = lean_unbox(v_a_157_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_164_);
v___x_165_ = lean_unbox(v_a_157_);
lean_dec(v_a_157_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1 + 1, v___x_165_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_163_);
v___x_167_ = v___x_159_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_163_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_del_object(v___x_159_);
lean_dec(v_a_157_);
goto v___jp_150_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_156_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_156_);
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
else
{
lean_dec_ref(v_c_142_);
goto v___jp_150_;
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_c_142_);
v_a_178_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_153_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_153_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object* v_c_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* v_c_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v_c_195_, v_a_196_, v_a_200_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* v_c_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(v_c_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* v_e_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_234_; 
lean_inc_ref(v_e_221_);
v___x_234_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_221_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; uint8_t v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = lean_unbox(v_a_235_);
lean_dec(v_a_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_a_222_);
v___x_237_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_221_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_251_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_251_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_251_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; 
v___x_242_ = lean_unbox(v_a_238_);
lean_dec(v_a_238_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_box(1);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
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
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_237_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_237_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec_ref(v_e_221_);
v___x_260_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_222_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; uint8_t v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = lean_unbox(v_a_261_);
lean_dec(v_a_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_276_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_276_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_a_264_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_274_; 
v___x_269_ = lean_unsigned_to_nat(2u);
v___x_270_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = lean_unbox(v_a_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_271_);
v___x_272_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1 + 1, v___x_272_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_274_ = v___x_266_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_270_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_del_object(v___x_266_);
lean_dec(v_a_264_);
goto v___jp_231_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_263_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_263_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_dec_ref(v_b_223_);
goto v___jp_231_;
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_b_223_);
v_a_285_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_260_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_260_);
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
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_b_223_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_221_);
v_a_293_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_234_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_234_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
v___jp_231_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* v_e_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_301_, v_a_302_, v_b_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* v_e_312_, lean_object* v_a_313_, lean_object* v_b_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_312_, v_a_313_, v_b_314_, v_a_315_, v_a_319_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_b_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(v_e_327_, v_a_328_, v_b_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec(v_a_330_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* v_e_342_, lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_355_; 
lean_inc_ref(v_e_342_);
v___x_355_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_342_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_417_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_417_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_417_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_417_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = lean_unbox(v_a_356_);
lean_dec(v_a_356_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_del_object(v___x_358_);
v___x_361_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_342_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_404_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_404_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_404_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_404_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; 
v___x_366_ = lean_unbox(v_a_362_);
lean_dec(v_a_362_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v___x_367_ = lean_box(1);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_371_; 
lean_del_object(v___x_364_);
v___x_371_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_343_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; uint8_t v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_unbox(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; lean_object* v___x_385_; 
v___x_380_ = lean_unsigned_to_nat(2u);
v___x_381_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_unbox(v_a_375_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_382_);
v___x_383_ = lean_unbox(v_a_375_);
lean_dec(v_a_375_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1 + 1, v___x_383_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_381_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_381_);
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
lean_del_object(v___x_377_);
lean_dec(v_a_375_);
goto v___jp_352_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_374_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_374_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_dec_ref(v_b_344_);
goto v___jp_352_;
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_b_344_);
v_a_396_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_371_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_371_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
v_a_405_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_361_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_361_);
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
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
v___x_413_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_413_);
v___x_415_ = v___x_358_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_b_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_e_342_);
v_a_418_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_355_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_355_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_b_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_426_, v_a_427_, v_b_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_437_, v_a_438_, v_b_439_, v_a_440_, v_a_444_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* v_e_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(v_e_452_, v_a_453_, v_b_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec(v_a_455_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
uint8_t v_a_478_; uint8_t v_a_511_; lean_object* v___x_543_; 
lean_inc_ref(v_e_467_);
v___x_543_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_467_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; uint8_t v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_467_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_578_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_578_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_578_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_578_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v___x_552_ = lean_box(1);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v___x_556_; 
lean_del_object(v___x_549_);
lean_inc_ref(v_a_468_);
v___x_556_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; uint8_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
if (v___x_558_ == 0)
{
goto v___jp_485_;
}
else
{
lean_object* v___x_559_; 
lean_inc_ref(v_b_469_);
v___x_559_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; uint8_t v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_unbox(v_a_560_);
lean_dec(v_a_560_);
if (v___x_561_ == 0)
{
goto v___jp_485_;
}
else
{
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
goto v___jp_482_;
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_562_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_559_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_570_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_556_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_556_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_579_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_546_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_546_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v_e_467_);
lean_inc_ref(v_a_468_);
v___x_587_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; uint8_t v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_unbox(v_a_588_);
lean_dec(v_a_588_);
if (v___x_589_ == 0)
{
goto v___jp_518_;
}
else
{
lean_object* v___x_590_; 
lean_inc_ref(v_b_469_);
v___x_590_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; uint8_t v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_unbox(v_a_591_);
lean_dec(v_a_591_);
if (v___x_592_ == 0)
{
goto v___jp_518_;
}
else
{
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
goto v___jp_515_;
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_593_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_590_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_590_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_a_601_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_587_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_587_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
lean_dec_ref(v_e_467_);
v_a_609_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_543_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_543_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v_a_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1 + 1, v_a_478_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
v___jp_482_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; uint8_t v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = lean_unbox(v_a_487_);
if (v___x_488_ == 0)
{
uint8_t v___x_489_; 
lean_dec_ref(v_b_469_);
v___x_489_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
v_a_478_ = v___x_489_;
goto v___jp_477_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_a_487_);
v___x_490_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
v_a_478_ = v___x_493_;
goto v___jp_477_;
}
else
{
lean_dec(v_a_491_);
goto v___jp_482_;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_490_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_b_469_);
v_a_502_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_486_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_486_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(2u);
v___x_513_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*1, v_a_511_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*1 + 1, v_a_511_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
v___jp_515_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
v___jp_518_:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; uint8_t v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unbox(v_a_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; 
lean_dec_ref(v_b_469_);
v___x_522_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
v_a_511_ = v___x_522_;
goto v___jp_510_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_a_520_);
v___x_523_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint8_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unbox(v_a_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = lean_unbox(v_a_524_);
lean_dec(v_a_524_);
v_a_511_ = v___x_526_;
goto v___jp_510_;
}
else
{
lean_dec(v_a_524_);
goto v___jp_515_;
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_523_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_523_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_b_469_);
v_a_535_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_519_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_519_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_617_, v_a_618_, v_b_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_628_, v_a_629_, v_b_630_, v_a_631_, v_a_635_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* v_e_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(v_e_643_, v_a_644_, v_b_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* v_c_658_, uint8_t v___x_659_, uint8_t v_d_660_, lean_object* v_a_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
if (v_d_660_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_st_ref_get(v___y_663_);
v___x_675_ = l_Lean_Expr_isApp(v_a_661_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_674_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_c_658_);
v___x_676_ = lean_box(v_d_660_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
else
{
uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Meta_Grind_Goal_isCongruent(v___x_674_, v_c_658_, v_a_661_);
lean_dec(v___x_674_);
v___x_679_ = lean_box(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_a_661_);
lean_dec_ref(v_c_658_);
v___x_681_ = lean_box(v___x_659_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* v_c_683_, lean_object* v___x_684_, lean_object* v_d_685_, lean_object* v_a_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_7896__boxed_699_; uint8_t v_d_boxed_700_; lean_object* v_res_701_; 
v___x_7896__boxed_699_ = lean_unbox(v___x_684_);
v_d_boxed_700_ = lean_unbox(v_d_685_);
v_res_701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(v_c_683_, v___x_7896__boxed_699_, v_d_boxed_700_, v_a_686_, v_x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(lean_object* v_f_702_, lean_object* v_keys_703_, lean_object* v_vals_704_, lean_object* v_i_705_, lean_object* v_acc_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_array_get_size(v_keys_703_);
v___x_719_ = lean_nat_dec_lt(v_i_705_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_i_705_);
lean_dec_ref(v_f_702_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_acc_706_);
return v___x_720_;
}
else
{
lean_object* v_k_721_; lean_object* v_v_722_; lean_object* v___x_723_; 
v_k_721_ = lean_array_fget_borrowed(v_keys_703_, v_i_705_);
v_v_722_ = lean_array_fget_borrowed(v_vals_704_, v_i_705_);
lean_inc_ref(v_f_702_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc(v___y_707_);
lean_inc(v_v_722_);
lean_inc(v_k_721_);
v___x_723_ = lean_apply_14(v_f_702_, v_acc_706_, v_k_721_, v_v_722_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, lean_box(0));
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_i_705_, v___x_725_);
lean_dec(v_i_705_);
v_i_705_ = v___x_726_;
v_acc_706_ = v_a_724_;
goto _start;
}
else
{
lean_dec(v_i_705_);
lean_dec_ref(v_f_702_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_728_, lean_object* v_keys_729_, lean_object* v_vals_730_, lean_object* v_i_731_, lean_object* v_acc_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_728_, v_keys_729_, v_vals_730_, v_i_731_, v_acc_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v_vals_730_);
lean_dec_ref(v_keys_729_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* v_f_745_, lean_object* v_as_746_, size_t v_i_747_, size_t v_stop_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_a_762_; lean_object* v___y_767_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_747_, v_stop_748_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_array_uget_borrowed(v_as_746_, v_i_747_);
switch(lean_obj_tag(v___x_770_))
{
case 0:
{
lean_object* v_key_771_; lean_object* v_val_772_; lean_object* v___x_773_; 
v_key_771_ = lean_ctor_get(v___x_770_, 0);
v_val_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc_ref(v_f_745_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v_val_772_);
lean_inc(v_key_771_);
v___x_773_ = lean_apply_14(v_f_745_, v_b_749_, v_key_771_, v_val_772_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, lean_box(0));
v___y_767_ = v___x_773_;
goto v___jp_766_;
}
case 1:
{
lean_object* v_node_774_; lean_object* v___x_775_; 
v_node_774_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_node_774_);
lean_inc_ref(v_f_745_);
v___x_775_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_745_, v_node_774_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_767_ = v___x_775_;
goto v___jp_766_;
}
default: 
{
v_a_762_ = v_b_749_;
goto v___jp_761_;
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v_f_745_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_749_);
return v___x_776_;
}
v___jp_761_:
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_747_, v___x_763_);
v_i_747_ = v___x_764_;
v_b_749_ = v_a_762_;
goto _start;
}
v___jp_766_:
{
if (lean_obj_tag(v___y_767_) == 0)
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___y_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___y_767_, 1);
v_a_762_ = v_a_768_;
goto v___jp_761_;
}
else
{
lean_dec_ref(v_f_745_);
return v___y_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* v_f_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_es_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_es_791_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_804_ == 0)
{
v___x_793_ = v_x_778_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_es_791_);
lean_dec(v_x_778_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_es_791_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_es_791_);
lean_dec_ref(v_f_777_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_x_779_);
v___x_799_ = v___x_793_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_x_779_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_793_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_796_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_777_, v_es_791_, v___x_801_, v___x_802_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_es_791_);
return v___x_803_;
}
}
}
else
{
lean_object* v_ks_805_; lean_object* v_vs_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_ks_805_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_ks_805_);
v_vs_806_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_vs_806_);
lean_dec_ref_known(v_x_778_, 2);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_777_, v_ks_805_, v_vs_806_, v___x_807_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_vs_806_);
lean_dec_ref(v_ks_805_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* v_f_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_809_, v_x_810_, v_x_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_824_, lean_object* v_as_825_, lean_object* v_i_826_, lean_object* v_stop_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
size_t v_i_boxed_840_; size_t v_stop_boxed_841_; lean_object* v_res_842_; 
v_i_boxed_840_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_stop_boxed_841_ = lean_unbox_usize(v_stop_827_);
lean_dec(v_stop_827_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_824_, v_as_825_, v_i_boxed_840_, v_stop_boxed_841_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v_as_825_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Expr_isApp(v_c_843_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_c_843_);
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v_toGoalState_861_; lean_object* v_split_862_; lean_object* v_resolved_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_858_ = lean_box(v___x_855_);
v___f_859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 16, 2);
lean_closure_set(v___f_859_, 0, v_c_843_);
lean_closure_set(v___f_859_, 1, v___x_858_);
v___x_860_ = lean_st_ref_get(v_a_844_);
v_toGoalState_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_toGoalState_861_);
lean_dec(v___x_860_);
v_split_862_ = lean_ctor_get(v_toGoalState_861_, 15);
lean_inc_ref(v_split_862_);
lean_dec_ref(v_toGoalState_861_);
v_resolved_863_ = lean_ctor_get(v_split_862_, 3);
lean_inc_ref(v_resolved_863_);
lean_dec_ref(v_split_862_);
v___x_864_ = 0;
v___x_865_ = lean_box(v___x_864_);
v___x_866_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v___f_859_, v_resolved_863_, v___x_865_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___boxed(lean_object* v_c_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_c_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec(v_a_868_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* v_map_880_, lean_object* v_f_881_, lean_object* v_init_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_881_, v_map_880_, v_init_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* v_map_895_, lean_object* v_f_896_, lean_object* v_init_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(v_map_895_, v_f_896_, v_init_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* v_00_u03c3_910_, lean_object* v_00_u03b2_911_, lean_object* v_map_912_, lean_object* v_f_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_913_, v_map_912_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* v_00_u03c3_927_, lean_object* v_00_u03b2_928_, lean_object* v_map_929_, lean_object* v_f_930_, lean_object* v_init_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(v_00_u03c3_927_, v_00_u03b2_928_, v_map_929_, v_f_930_, v_init_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec(v___y_932_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* v_00_u03c3_944_, lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_f_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(v_f_947_, v_x_948_, v_x_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_962_ = _args[0];
lean_object* v_00_u03b1_963_ = _args[1];
lean_object* v_00_u03b2_964_ = _args[2];
lean_object* v_f_965_ = _args[3];
lean_object* v_x_966_ = _args[4];
lean_object* v_x_967_ = _args[5];
lean_object* v___y_968_ = _args[6];
lean_object* v___y_969_ = _args[7];
lean_object* v___y_970_ = _args[8];
lean_object* v___y_971_ = _args[9];
lean_object* v___y_972_ = _args[10];
lean_object* v___y_973_ = _args[11];
lean_object* v___y_974_ = _args[12];
lean_object* v___y_975_ = _args[13];
lean_object* v___y_976_ = _args[14];
lean_object* v___y_977_ = _args[15];
lean_object* v___y_978_ = _args[16];
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(v_00_u03c3_962_, v_00_u03b1_963_, v_00_u03b2_964_, v_f_965_, v_x_966_, v_x_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_00_u03c3_982_, lean_object* v_f_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(v_f_983_, v_as_984_, v_i_985_, v_stop_986_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_1000_ = _args[0];
lean_object* v_00_u03b2_1001_ = _args[1];
lean_object* v_00_u03c3_1002_ = _args[2];
lean_object* v_f_1003_ = _args[3];
lean_object* v_as_1004_ = _args[4];
lean_object* v_i_1005_ = _args[5];
lean_object* v_stop_1006_ = _args[6];
lean_object* v_b_1007_ = _args[7];
lean_object* v___y_1008_ = _args[8];
lean_object* v___y_1009_ = _args[9];
lean_object* v___y_1010_ = _args[10];
lean_object* v___y_1011_ = _args[11];
lean_object* v___y_1012_ = _args[12];
lean_object* v___y_1013_ = _args[13];
lean_object* v___y_1014_ = _args[14];
lean_object* v___y_1015_ = _args[15];
lean_object* v___y_1016_ = _args[16];
lean_object* v___y_1017_ = _args[17];
lean_object* v___y_1018_ = _args[18];
_start:
{
size_t v_i_boxed_1019_; size_t v_stop_boxed_1020_; lean_object* v_res_1021_; 
v_i_boxed_1019_ = lean_unbox_usize(v_i_1005_);
lean_dec(v_i_1005_);
v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1006_);
lean_dec(v_stop_1006_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(v_00_u03b1_1000_, v_00_u03b2_1001_, v_00_u03c3_1002_, v_f_1003_, v_as_1004_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v_as_1004_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_1022_, lean_object* v_00_u03b1_1023_, lean_object* v_00_u03b2_1024_, lean_object* v_f_1025_, lean_object* v_keys_1026_, lean_object* v_vals_1027_, lean_object* v_heq_1028_, lean_object* v_i_1029_, lean_object* v_acc_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___redArg(v_f_1025_, v_keys_1026_, v_vals_1027_, v_i_1029_, v_acc_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_1043_ = _args[0];
lean_object* v_00_u03b1_1044_ = _args[1];
lean_object* v_00_u03b2_1045_ = _args[2];
lean_object* v_f_1046_ = _args[3];
lean_object* v_keys_1047_ = _args[4];
lean_object* v_vals_1048_ = _args[5];
lean_object* v_heq_1049_ = _args[6];
lean_object* v_i_1050_ = _args[7];
lean_object* v_acc_1051_ = _args[8];
lean_object* v___y_1052_ = _args[9];
lean_object* v___y_1053_ = _args[10];
lean_object* v___y_1054_ = _args[11];
lean_object* v___y_1055_ = _args[12];
lean_object* v___y_1056_ = _args[13];
lean_object* v___y_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
lean_object* v___y_1061_ = _args[18];
lean_object* v___y_1062_ = _args[19];
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__2(v_00_u03c3_1043_, v_00_u03b1_1044_, v_00_u03b2_1045_, v_f_1046_, v_keys_1047_, v_vals_1048_, v_heq_1049_, v_i_1050_, v_acc_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v_vals_1048_);
lean_dec_ref(v_keys_1047_);
return v_res_1063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
lean_ctor_set(v___x_1070_, 4, v___x_1068_);
lean_ctor_set(v___x_1070_, 5, v___x_1068_);
lean_ctor_set(v___x_1070_, 6, v___x_1068_);
lean_ctor_set(v___x_1070_, 7, v___x_1068_);
lean_ctor_set(v___x_1070_, 8, v___x_1068_);
lean_ctor_set(v___x_1070_, 9, v___x_1068_);
lean_ctor_set(v___x_1070_, 10, v___x_1068_);
lean_ctor_set(v___x_1070_, 11, v___x_1067_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(32u);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((size_t)5ULL);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_unsigned_to_nat(32u);
v___x_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1075_);
lean_ctor_set(v___x_1079_, 3, v___x_1075_);
lean_ctor_set_usize(v___x_1079_, 4, v___x_1074_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(1);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v___x_1080_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1105_, lean_object* v_declHint_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_env_1111_; uint8_t v___x_1112_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_st_ref_get(v___y_1107_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Name_isAnonymous(v_declHint_1106_);
if (v___x_1112_ == 0)
{
uint8_t v_isExporting_1113_; 
v_isExporting_1113_ = lean_ctor_get_uint8(v_env_1111_, sizeof(void*)*13);
if (v_isExporting_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_msg_1105_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
lean_inc_ref(v_env_1111_);
v___x_1115_ = l_Lean_Environment_setExporting(v_env_1111_, v___x_1112_);
lean_inc(v_declHint_1106_);
lean_inc_ref(v___x_1115_);
v___x_1116_ = l_Lean_Environment_contains(v___x_1115_, v_declHint_1106_, v_isExporting_1113_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_msg_1105_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_c_1123_; lean_object* v___x_1124_; 
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_1119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1120_ = l_Lean_Options_empty;
v___x_1121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1115_);
lean_ctor_set(v___x_1121_, 1, v___x_1118_);
lean_ctor_set(v___x_1121_, 2, v___x_1119_);
lean_ctor_set(v___x_1121_, 3, v___x_1120_);
lean_inc(v_declHint_1106_);
v___x_1122_ = l_Lean_MessageData_ofConstName(v_declHint_1106_, v___x_1112_);
v_c_1123_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1123_, 0, v___x_1121_);
lean_ctor_set(v_c_1123_, 1, v___x_1122_);
v___x_1124_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1111_, v_declHint_1106_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v_c_1123_);
v___x_1127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_MessageData_note(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_msg_1105_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1166_; 
v_val_1132_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1134_ = v___x_1124_;
v_isShared_1135_ = v_isSharedCheck_1166_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v___x_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1166_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v_moduleNames_1137_; lean_object* v_mod_1138_; uint8_t v___x_1139_; 
v___x_1136_ = l_Lean_Environment_header(v_env_1111_);
lean_dec_ref(v_env_1111_);
v_moduleNames_1137_ = lean_ctor_get(v___x_1136_, 4);
lean_inc_ref(v_moduleNames_1137_);
lean_dec_ref(v___x_1136_);
v_mod_1138_ = lean_array_get(v___x_1109_, v_moduleNames_1137_, v_val_1132_);
lean_dec(v_val_1132_);
lean_dec_ref(v_moduleNames_1137_);
v___x_1139_ = l_Lean_isPrivateName(v_declHint_1106_);
lean_dec(v_declHint_1106_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_c_1123_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_ofName(v_mod_1138_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_note(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_msg_1105_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1149_);
v___x_1151_ = v___x_1134_;
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
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_c_1123_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_ofName(v_mod_1138_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_MessageData_note(v___x_1160_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_msg_1105_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1162_);
v___x_1164_ = v___x_1134_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1167_; 
lean_dec_ref(v_env_1111_);
lean_dec(v_declHint_1106_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_msg_1105_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1168_, lean_object* v_declHint_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1168_, v_declHint_1169_, v___y_1170_);
lean_dec(v___y_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1173_, lean_object* v_declHint_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1196_; 
v___x_1186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1173_, v_declHint_1174_, v___y_1184_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = l_Lean_unknownIdentifierMessageTag;
v___x_1192_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1197_, lean_object* v_declHint_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1197_, v_declHint_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(lean_object* v_msgData_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_env_1218_; uint8_t v___x_1219_; lean_object* v_env_1220_; lean_object* v___x_1221_; lean_object* v_toCold_1222_; lean_object* v_mctx_1223_; lean_object* v_lctx_1224_; lean_object* v_options_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1217_ = lean_st_ref_get(v___y_1215_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = 0;
v_env_1220_ = l_Lean_Environment_setRecordingDeps(v_env_1218_, v___x_1219_);
v___x_1221_ = lean_st_ref_get(v___y_1213_);
v_toCold_1222_ = lean_ctor_get(v___y_1214_, 0);
v_mctx_1223_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref(v_mctx_1223_);
lean_dec(v___x_1221_);
v_lctx_1224_ = lean_ctor_get(v___y_1212_, 2);
v_options_1225_ = lean_ctor_get(v_toCold_1222_, 2);
lean_inc_ref(v_options_1225_);
lean_inc_ref(v_lctx_1224_);
v___x_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1226_, 0, v_env_1220_);
lean_ctor_set(v___x_1226_, 1, v_mctx_1223_);
lean_ctor_set(v___x_1226_, 2, v_lctx_1224_);
lean_ctor_set(v___x_1226_, 3, v_options_1225_);
v___x_1227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_msgData_1211_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2___boxed(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msgData_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_ref_1242_; lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1252_; 
v_ref_1242_ = lean_ctor_get(v___y_1239_, 2);
v___x_1243_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1252_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_inc(v_ref_1242_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_ref_1242_);
lean_ctor_set(v___x_1248_, 1, v_a_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1248_);
v___x_1250_ = v___x_1246_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_msg_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1260_, lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_toCold_1273_; lean_object* v_currRecDepth_1274_; lean_object* v_ref_1275_; uint16_t v_optionFlags_1276_; uint8_t v_suppressElabErrors_1277_; uint8_t v_isRecordingDeps_1278_; lean_object* v_ref_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_toCold_1273_ = lean_ctor_get(v___y_1270_, 0);
v_currRecDepth_1274_ = lean_ctor_get(v___y_1270_, 1);
v_ref_1275_ = lean_ctor_get(v___y_1270_, 2);
v_optionFlags_1276_ = lean_ctor_get_uint16(v___y_1270_, sizeof(void*)*3);
v_suppressElabErrors_1277_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1278_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 3);
v_ref_1279_ = l_Lean_replaceRef(v_ref_1260_, v_ref_1275_);
lean_inc(v_currRecDepth_1274_);
lean_inc_ref(v_toCold_1273_);
v___x_1280_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1280_, 0, v_toCold_1273_);
lean_ctor_set(v___x_1280_, 1, v_currRecDepth_1274_);
lean_ctor_set(v___x_1280_, 2, v_ref_1279_);
lean_ctor_set_uint16(v___x_1280_, sizeof(void*)*3, v_optionFlags_1276_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 2, v_suppressElabErrors_1277_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 3, v_isRecordingDeps_1278_);
v___x_1281_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1261_, v___y_1268_, v___y_1269_, v___x_1280_, v___y_1271_);
lean_dec_ref_known(v___x_1280_, 3);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1282_, v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v_ref_1282_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1296_, lean_object* v_msg_1297_, lean_object* v_declHint_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_a_1311_; lean_object* v___x_1312_; 
v___x_1310_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1297_, v_declHint_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1296_, v_a_1311_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1313_, lean_object* v_msg_1314_, lean_object* v_declHint_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1313_, v_msg_1314_, v_declHint_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v_ref_1313_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1334_, lean_object* v_constName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1347_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1348_ = 0;
lean_inc(v_constName_1335_);
v___x_1349_ = l_Lean_MessageData_ofConstName(v_constName_1335_, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1347_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1334_, v___x_1352_, v_constName_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1354_, lean_object* v_constName_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1354_, v_constName_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v_ref_1354_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_ref_1380_; lean_object* v___x_1381_; 
v_ref_1380_ = lean_ctor_get(v___y_1377_, 2);
v___x_1381_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1380_, v_constName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
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
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; lean_object* v_env_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = lean_st_ref_get(v___y_1405_);
v_env_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_env_1408_);
lean_dec(v___x_1407_);
v___x_1409_ = 0;
lean_inc(v_constName_1395_);
v___x_1410_ = l_Lean_Environment_find_x3f(v_env_1408_, v_constName_1395_, v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_constName_1395_);
v_val_1412_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1410_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_val_1412_);
lean_dec(v___x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 0);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_val_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0___boxed(lean_object* v_constName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_constName_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
return v_res_1432_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1433_; double v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_float_of_nat(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(lean_object* v_cls_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_ref_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1492_; 
v_ref_1445_ = lean_ctor_get(v___y_1442_, 2);
v___x_1446_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1_spec__2(v_msg_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1492_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1492_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v_traceState_1452_; lean_object* v_env_1453_; lean_object* v_nextMacroScope_1454_; lean_object* v_ngen_1455_; lean_object* v_auxDeclNGen_1456_; lean_object* v_cache_1457_; lean_object* v_recordedDeps_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1491_; 
v___x_1451_ = lean_st_ref_take(v___y_1443_);
v_traceState_1452_ = lean_ctor_get(v___x_1451_, 4);
v_env_1453_ = lean_ctor_get(v___x_1451_, 0);
v_nextMacroScope_1454_ = lean_ctor_get(v___x_1451_, 1);
v_ngen_1455_ = lean_ctor_get(v___x_1451_, 2);
v_auxDeclNGen_1456_ = lean_ctor_get(v___x_1451_, 3);
v_cache_1457_ = lean_ctor_get(v___x_1451_, 5);
v_recordedDeps_1458_ = lean_ctor_get(v___x_1451_, 6);
v_messages_1459_ = lean_ctor_get(v___x_1451_, 7);
v_infoState_1460_ = lean_ctor_get(v___x_1451_, 8);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1451_, 9);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1463_ = v___x_1451_;
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_recordedDeps_1458_);
lean_inc(v_cache_1457_);
lean_inc(v_traceState_1452_);
lean_inc(v_auxDeclNGen_1456_);
lean_inc(v_ngen_1455_);
lean_inc(v_nextMacroScope_1454_);
lean_inc(v_env_1453_);
lean_dec(v___x_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1491_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint64_t v_tid_1465_; lean_object* v_traces_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_tid_1465_ = lean_ctor_get_uint64(v_traceState_1452_, sizeof(void*)*1);
v_traces_1466_ = lean_ctor_get(v_traceState_1452_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_traceState_1452_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v_traceState_1452_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_traces_1466_);
lean_dec(v_traceState_1452_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; double v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__0);
v___x_1473_ = 0;
v___x_1474_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__1));
v___x_1475_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1475_, 0, v_cls_1438_);
lean_ctor_set(v___x_1475_, 1, v___x_1471_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3, v___x_1472_);
lean_ctor_set_float(v___x_1475_, sizeof(void*)*3 + 8, v___x_1472_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*3 + 16, v___x_1473_);
v___x_1476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___closed__2));
v___x_1477_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v_a_1447_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
lean_inc(v_ref_1445_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_ref_1445_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_PersistentArray_push___redArg(v_traces_1466_, v___x_1478_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1479_);
v___x_1481_ = v___x_1468_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1479_);
lean_ctor_set_uint64(v_reuseFailAlloc_1489_, sizeof(void*)*1, v_tid_1465_);
v___x_1481_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1481_);
v___x_1483_ = v___x_1463_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_env_1453_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_nextMacroScope_1454_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_ngen_1455_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_auxDeclNGen_1456_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_cache_1457_);
lean_ctor_set(v_reuseFailAlloc_1488_, 6, v_recordedDeps_1458_);
lean_ctor_set(v_reuseFailAlloc_1488_, 7, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1488_, 8, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1488_, 9, v_snapshotTasks_1461_);
v___x_1483_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_st_ref_put(v___y_1443_, v___x_1483_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1470_);
v___x_1486_ = v___x_1449_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1470_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg___boxed(lean_object* v_cls_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_1519_ = l_Lean_Name_append(v___x_1518_, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___x_1793_; 
lean_inc_ref(v_e_1532_);
v___x_1793_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1532_, v_a_1540_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1822_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1822_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1822_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = l_Lean_Expr_cleanupAnnotations(v_a_1794_);
v___x_1799_ = l_Lean_Expr_isApp(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v_arg_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_arg_1800_ = lean_ctor_get(v___x_1798_, 1);
lean_inc_ref(v_arg_1800_);
v___x_1801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1798_);
v___x_1802_ = l_Lean_Expr_isApp(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_arg_1800_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v_arg_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_arg_1803_ = lean_ctor_get(v___x_1801_, 1);
lean_inc_ref(v_arg_1803_);
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1801_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1808_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Lean_Expr_isApp(v___x_1804_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1800_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1804_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1812_ = l_Lean_Expr_isConstOf(v___x_1810_, v___x_1811_);
lean_dec_ref(v___x_1810_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1800_);
lean_del_object(v___x_1796_);
v___y_1673_ = v_a_1533_;
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
goto v___jp_1672_;
}
else
{
uint8_t v___x_1813_; 
lean_inc_ref(v_e_1532_);
v___x_1813_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1532_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_arg_1800_);
lean_dec_ref(v_e_1532_);
v___x_1814_ = lean_unsigned_to_nat(2u);
v___x_1815_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*1, v___x_1813_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*1 + 1, v___x_1813_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1815_);
v___x_1817_ = v___x_1796_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v___x_1819_; 
lean_del_object(v___x_1796_);
v___x_1819_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1800_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1819_;
}
}
}
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1796_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1800_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v___x_1804_);
lean_del_object(v___x_1796_);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1532_, v_arg_1803_, v_arg_1800_, v_a_1533_, v_a_1537_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_e_1532_);
v_a_1823_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1793_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1793_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
v___jp_1547_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
v___jp_1550_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
v___jp_1553_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = l_Lean_Expr_getAppNumArgs(v_e_1532_);
v___x_1562_ = lean_nat_sub(v___x_1561_, v___x_1560_);
lean_dec(v___x_1561_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v___x_1560_);
lean_dec(v___x_1562_);
v___x_1564_ = l_Lean_Expr_getRevArg_x21(v_e_1532_, v___x_1563_);
lean_dec_ref(v_e_1532_);
v___x_1565_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1564_, v___y_1554_, v___y_1557_, v___y_1555_, v___y_1556_, v___y_1559_, v___y_1558_);
return v___x_1565_;
}
v___jp_1566_:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_Expr_isFVar(v_e_1532_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec_ref(v_e_1532_);
v___x_1579_ = lean_box(1);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc_ref(v_e_1532_);
v___x_1581_ = lean_infer_type(v_e_1532_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Meta_whnfD(v_a_1582_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_n(v_a_1584_, 2);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1586_ = l_Lean_MessageData_ofExpr(v_e_1532_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_indentExpr(v_a_1584_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Expr_getAppFn(v_a_1584_);
lean_dec(v_a_1584_);
if (lean_obj_tag(v___x_1592_) == 4)
{
lean_object* v_declName_1593_; lean_object* v___x_1594_; 
v_declName_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_declName_1593_);
lean_dec_ref_known(v___x_1592_, 2);
v___x_1594_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1593_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1627_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1627_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
if (lean_obj_tag(v_a_1595_) == 5)
{
lean_object* v_val_1599_; lean_object* v_ctors_1600_; uint8_t v_isRec_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1591_, 2);
v_val_1599_ = lean_ctor_get(v_a_1595_, 0);
lean_inc_ref(v_val_1599_);
lean_dec_ref_known(v_a_1595_, 1);
v_ctors_1600_ = lean_ctor_get(v_val_1599_, 4);
lean_inc(v_ctors_1600_);
v_isRec_1601_ = lean_ctor_get_uint8(v_val_1599_, sizeof(void*)*6);
lean_dec_ref(v_val_1599_);
v___x_1602_ = l_List_lengthTR___redArg(v_ctors_1600_);
lean_dec(v_ctors_1600_);
v___x_1603_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1, v_isRec_1601_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1 + 1, v___y_1567_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1603_);
v___x_1605_ = v___x_1597_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v___x_1607_; 
lean_del_object(v___x_1597_);
lean_dec(v_a_1595_);
v___x_1607_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; uint8_t v_verbose_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_verbose_1609_ = lean_ctor_get_uint8(v_a_1608_, 0);
lean_dec(v_a_1608_);
if (v_verbose_1609_ == 0)
{
lean_dec_ref_known(v___x_1591_, 2);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Sym_reportIssue(v___x_1591_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_dec_ref_known(v___x_1610_, 1);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1619_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1607_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1607_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1628_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1594_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1594_);
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
else
{
lean_object* v___x_1636_; 
lean_dec_ref(v___x_1592_);
v___x_1636_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1572_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; uint8_t v_verbose_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v_verbose_1638_ = lean_ctor_get_uint8(v_a_1637_, 0);
lean_dec(v_a_1637_);
if (v_verbose_1638_ == 0)
{
lean_dec_ref_known(v___x_1591_, 2);
goto v___jp_1550_;
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Sym_reportIssue(v___x_1591_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref_known(v___x_1639_, 1);
goto v___jp_1550_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref_known(v___x_1591_, 2);
v_a_1648_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1636_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1636_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_e_1532_);
v_a_1656_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1583_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1583_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_e_1532_);
v_a_1664_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1581_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1581_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
v___jp_1672_:
{
uint8_t v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Grind_isIte(v_e_1532_);
if (v___x_1683_ == 0)
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_isDIte(v_e_1532_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1532_, v___y_1673_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; uint8_t v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_inc_ref(v_e_1532_);
v___x_1688_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1532_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1748_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1748_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1748_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_unbox(v_a_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v_env_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_st_ref_get(v___y_1682_);
v_env_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc_ref(v_env_1695_);
lean_dec(v___x_1694_);
v___x_1696_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1695_, v_e_1532_);
if (lean_obj_tag(v___x_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1703_; 
lean_dec_ref(v_e_1532_);
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1697_);
lean_dec(v_val_1697_);
v___x_1699_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
v___x_1700_ = lean_unbox(v_a_1689_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*1, v___x_1700_);
v___x_1701_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*1 + 1, v___x_1701_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1699_);
v___x_1703_ = v___x_1691_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1699_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; 
lean_dec(v___x_1696_);
lean_del_object(v___x_1691_);
v___x_1705_ = l_Lean_Expr_getAppFn(v_e_1532_);
if (lean_obj_tag(v___x_1705_) == 4)
{
lean_object* v_declName_1706_; lean_object* v___x_1707_; 
v_declName_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_declName_1706_);
lean_dec_ref_known(v___x_1705_, 2);
v___x_1707_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1706_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
if (lean_obj_tag(v_a_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1710_; 
v_val_1709_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1708_, 1);
lean_inc_ref(v_e_1532_);
v___x_1710_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1532_, v___y_1673_, v___y_1677_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
if (v___x_1715_ == 0)
{
uint8_t v___x_1716_; 
lean_del_object(v___x_1713_);
lean_dec(v_val_1709_);
v___x_1716_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1716_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
else
{
lean_object* v_ctors_1717_; uint8_t v_isRec_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1723_; 
lean_dec_ref(v_e_1532_);
v_ctors_1717_ = lean_ctor_get(v_val_1709_, 4);
lean_inc(v_ctors_1717_);
v_isRec_1718_ = lean_ctor_get_uint8(v_val_1709_, sizeof(void*)*6);
lean_dec(v_val_1709_);
v___x_1719_ = l_List_lengthTR___redArg(v_ctors_1717_);
lean_dec(v_ctors_1717_);
v___x_1720_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*1, v_isRec_1718_);
v___x_1721_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*1 + 1, v___x_1721_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1720_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1720_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_val_1709_);
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v_a_1726_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1710_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1710_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
uint8_t v___x_1734_; 
lean_dec(v_a_1708_);
v___x_1734_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1734_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v_a_1735_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1707_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1707_);
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
uint8_t v___x_1743_; 
lean_dec_ref(v___x_1705_);
v___x_1743_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
v___y_1567_ = v___x_1743_;
v___y_1568_ = v___y_1673_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_e_1532_);
v___x_1744_ = lean_box(0);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1744_);
v___x_1746_ = v___x_1691_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref(v_e_1532_);
v_a_1749_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1688_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1688_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_toCold_1757_; lean_object* v_options_1758_; uint8_t v_hasTrace_1759_; 
v_toCold_1757_ = lean_ctor_get(v___y_1681_, 0);
v_options_1758_ = lean_ctor_get(v_toCold_1757_, 2);
v_hasTrace_1759_ = lean_ctor_get_uint8(v_options_1758_, sizeof(void*)*1);
if (v_hasTrace_1759_ == 0)
{
lean_dec_ref(v_e_1532_);
goto v___jp_1544_;
}
else
{
lean_object* v_inheritedTraceOptions_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_inheritedTraceOptions_1760_ = lean_ctor_get(v_toCold_1757_, 11);
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1760_, v_options_1758_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec_ref(v_e_1532_);
goto v___jp_1544_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_Grind_updateLastTag(v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1766_ = l_Lean_MessageData_ofExpr(v_e_1532_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1761_, v___x_1767_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_dec_ref_known(v___x_1768_, 1);
goto v___jp_1544_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
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
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v_e_1532_);
v_a_1777_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1764_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1764_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v_e_1532_);
v_a_1785_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1685_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1685_);
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
v___y_1554_ = v___y_1673_;
v___y_1555_ = v___y_1679_;
v___y_1556_ = v___y_1680_;
v___y_1557_ = v___y_1677_;
v___y_1558_ = v___y_1682_;
v___y_1559_ = v___y_1681_;
goto v___jp_1553_;
}
}
else
{
v___y_1554_ = v___y_1673_;
v___y_1555_ = v___y_1679_;
v___y_1556_ = v___y_1680_;
v___y_1557_ = v___y_1677_;
v___y_1558_ = v___y_1682_;
v___y_1559_ = v___y_1681_;
goto v___jp_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_a_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1844_, lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1844_, v_msg_1845_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1858_, lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1858_, v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1872_, lean_object* v_constName_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_constName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1886_, v_constName_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1900_, lean_object* v_ref_1901_, lean_object* v_constName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1901_, v_constName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_ref_1916_, lean_object* v_constName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1915_, v_ref_1916_, v_constName_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v_ref_1916_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1930_, lean_object* v_ref_1931_, lean_object* v_msg_1932_, lean_object* v_declHint_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1931_, v_msg_1932_, v_declHint_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_ref_1947_, lean_object* v_msg_1948_, lean_object* v_declHint_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1946_, v_ref_1947_, v_msg_1948_, v_declHint_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
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
lean_dec(v_ref_1947_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1962_, lean_object* v_declHint_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1962_, v_declHint_1963_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1976_, lean_object* v_declHint_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1976_, v_declHint_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1990_, lean_object* v_ref_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1991_, v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_ref_2006_, lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2005_, v_ref_2006_, v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
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
lean_dec(v_ref_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2020_, lean_object* v_msg_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2021_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_msg_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2034_, v_msg_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v___y_2036_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2048_, lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_box(0);
return v___x_2050_;
}
else
{
lean_object* v_key_2051_; lean_object* v_value_2052_; lean_object* v_tail_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v_fst_2056_; lean_object* v_snd_2057_; uint8_t v___x_2058_; 
v_key_2051_ = lean_ctor_get(v_x_2049_, 0);
v_value_2052_ = lean_ctor_get(v_x_2049_, 1);
v_tail_2053_ = lean_ctor_get(v_x_2049_, 2);
v_fst_2054_ = lean_ctor_get(v_key_2051_, 0);
v_snd_2055_ = lean_ctor_get(v_key_2051_, 1);
v_fst_2056_ = lean_ctor_get(v_a_2048_, 0);
v_snd_2057_ = lean_ctor_get(v_a_2048_, 1);
v___x_2058_ = lean_expr_eqv(v_fst_2054_, v_fst_2056_);
if (v___x_2058_ == 0)
{
v_x_2049_ = v_tail_2053_;
goto _start;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_expr_eqv(v_snd_2055_, v_snd_2057_);
if (v___x_2060_ == 0)
{
v_x_2049_ = v_tail_2053_;
goto _start;
}
else
{
lean_object* v___x_2062_; 
lean_inc(v_value_2052_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_value_2052_);
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2063_, v_x_2064_);
lean_dec(v_x_2064_);
lean_dec_ref(v_a_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_buckets_2068_; lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v_fold_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_buckets_2068_ = lean_ctor_get(v_m_2066_, 1);
v_fst_2069_ = lean_ctor_get(v_a_2067_, 0);
v_snd_2070_ = lean_ctor_get(v_a_2067_, 1);
v___x_2071_ = lean_array_get_size(v_buckets_2068_);
v___x_2072_ = l_Lean_Expr_hash(v_fst_2069_);
v___x_2073_ = l_Lean_Expr_hash(v_snd_2070_);
v___x_2074_ = lean_uint64_mix_hash(v___x_2072_, v___x_2073_);
v___x_2075_ = 32ULL;
v___x_2076_ = lean_uint64_shift_right(v___x_2074_, v___x_2075_);
v_fold_2077_ = lean_uint64_xor(v___x_2074_, v___x_2076_);
v___x_2078_ = 16ULL;
v___x_2079_ = lean_uint64_shift_right(v_fold_2077_, v___x_2078_);
v___x_2080_ = lean_uint64_xor(v_fold_2077_, v___x_2079_);
v___x_2081_ = lean_uint64_to_usize(v___x_2080_);
v___x_2082_ = lean_usize_of_nat(v___x_2071_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_sub(v___x_2082_, v___x_2083_);
v___x_2085_ = lean_usize_land(v___x_2081_, v___x_2084_);
v___x_2086_ = lean_array_uget_borrowed(v_buckets_2068_, v___x_2085_);
v___x_2087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2067_, v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2088_, v_a_2089_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_m_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2091_, uint8_t v___x_2092_, lean_object* v_fst_2093_, lean_object* v_snd_2094_, lean_object* v___x_2095_, lean_object* v_____r_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2108_ = lean_unsigned_to_nat(2u);
v___x_2109_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1, v_a_2091_);
lean_ctor_set_uint8(v___x_2109_, sizeof(void*)*1 + 1, v___x_2092_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_fst_2093_);
lean_ctor_set(v___x_2111_, 1, v_snd_2094_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2095_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2110_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2116_ = _args[0];
lean_object* v___x_2117_ = _args[1];
lean_object* v_fst_2118_ = _args[2];
lean_object* v_snd_2119_ = _args[3];
lean_object* v___x_2120_ = _args[4];
lean_object* v_____r_2121_ = _args[5];
lean_object* v___y_2122_ = _args[6];
lean_object* v___y_2123_ = _args[7];
lean_object* v___y_2124_ = _args[8];
lean_object* v___y_2125_ = _args[9];
lean_object* v___y_2126_ = _args[10];
lean_object* v___y_2127_ = _args[11];
lean_object* v___y_2128_ = _args[12];
lean_object* v___y_2129_ = _args[13];
lean_object* v___y_2130_ = _args[14];
lean_object* v___y_2131_ = _args[15];
lean_object* v___y_2132_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2133_; uint8_t v___x_34318__boxed_2134_; lean_object* v_res_2135_; 
v_a_34317__boxed_2133_ = lean_unbox(v_a_2116_);
v___x_34318__boxed_2134_ = lean_unbox(v___x_2117_);
v_res_2135_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2133_, v___x_34318__boxed_2134_, v_fst_2118_, v_snd_2119_, v___x_2120_, v_____r_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec(v___y_2122_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2136_, lean_object* v_snd_2137_, lean_object* v___x_2138_, lean_object* v___x_2139_, lean_object* v_____r_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = l_Lean_Expr_appFn_x21(v_fst_2136_);
v___x_2153_ = l_Lean_Expr_appFn_x21(v_snd_2137_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2138_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2139_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2159_, lean_object* v_snd_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v_____r_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2159_, v_snd_2160_, v___x_2161_, v___x_2162_, v_____r_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v_snd_2160_);
lean_dec(v_fst_2159_);
return v_res_2175_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___f_2177_; 
v___x_2176_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2177_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2177_, 0, v___x_2176_);
return v___f_2177_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2183_ = l_Lean_Name_append(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2202_, lean_object* v___y_2203_, lean_object* v_eq_2204_, lean_object* v_a_2205_, lean_object* v_b_2206_, lean_object* v_a_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___y_2220_; lean_object* v_snd_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2362_; 
v_snd_2240_ = lean_ctor_get(v_a_2207_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2207_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v_a_2207_, 0);
lean_dec(v_unused_2363_);
v___x_2242_ = v_a_2207_;
v_isShared_2243_ = v_isSharedCheck_2362_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snd_2240_);
lean_dec(v_a_2207_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2362_;
goto v_resetjp_2241_;
}
v___jp_2219_:
{
if (lean_obj_tag(v___y_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2231_; 
v_a_2221_ = lean_ctor_get(v___y_2220_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___y_2220_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2223_ = v___y_2220_;
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___y_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
if (lean_obj_tag(v_a_2221_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; 
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2225_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v_a_2221_, 1);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_a_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v_a_2229_; 
lean_del_object(v___x_2223_);
v_a_2229_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v_a_2221_, 1);
v_a_2207_ = v_a_2229_;
goto _start;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2232_ = lean_ctor_get(v___y_2220_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2220_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___y_2220_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___y_2220_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
v_resetjp_2241_:
{
lean_object* v_snd_2244_; lean_object* v_fst_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2361_; 
v_snd_2244_ = lean_ctor_get(v_snd_2240_, 1);
v_fst_2245_ = lean_ctor_get(v_snd_2240_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2240_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2247_ = v_snd_2240_;
v_isShared_2248_ = v_isSharedCheck_2361_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2245_);
lean_dec(v_snd_2240_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2361_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_fst_2249_; lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2360_; 
v_fst_2249_ = lean_ctor_get(v_snd_2244_, 0);
v_snd_2250_ = lean_ctor_get(v_snd_2244_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_snd_2244_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2252_ = v_snd_2244_;
v_isShared_2253_ = v_isSharedCheck_2360_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_inc(v_fst_2249_);
lean_dec(v_snd_2244_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2360_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
uint8_t v___y_2255_; uint8_t v___x_2269_; 
v___x_2269_ = l_Lean_Expr_isApp(v_fst_2249_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v___y_2255_ = v_a_2202_;
goto v___jp_2254_;
}
else
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Expr_isApp(v_snd_2250_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v___y_2255_ = v___x_2270_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; uint8_t v___x_2275_; 
lean_del_object(v___x_2252_);
lean_del_object(v___x_2247_);
lean_del_object(v___x_2242_);
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_sub(v_fst_2245_, v___x_2272_);
lean_dec(v_fst_2245_);
v___f_2274_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2203_);
lean_inc(v___x_2273_);
v___x_2275_ = l_List_elem___redArg(v___f_2274_, v___x_2273_, v___y_2203_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_Expr_appArg_x21(v_fst_2249_);
v___x_2277_ = l_Lean_Expr_appArg_x21(v_snd_2250_);
v___x_2278_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2276_, v___x_2277_, v___y_2208_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; uint8_t v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = lean_unbox(v_a_2279_);
if (v___x_2280_ == 0)
{
lean_object* v_toCold_2281_; lean_object* v_options_2282_; lean_object* v_inheritedTraceOptions_2283_; uint8_t v_hasTrace_2284_; 
v_toCold_2281_ = lean_ctor_get(v___y_2216_, 0);
v_options_2282_ = lean_ctor_get(v_toCold_2281_, 2);
v_inheritedTraceOptions_2283_ = lean_ctor_get(v_toCold_2281_, 11);
v_hasTrace_2284_ = lean_ctor_get_uint8(v_options_2282_, sizeof(void*)*1);
if (v_hasTrace_2284_ == 0)
{
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
goto v___jp_2285_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2291_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2283_, v_options_2282_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
goto v___jp_2285_;
}
else
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Meta_Grind_updateLastTag(v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2292_, 1);
v___x_2293_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2204_, v___y_2208_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2205_);
v___x_2296_ = l_Lean_MessageData_ofExpr(v_a_2205_);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
lean_inc_ref(v_b_2206_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v_b_2206_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
lean_inc_ref(v_eq_2204_);
v___x_2304_ = l_Lean_MessageData_ofExpr(v_eq_2204_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_ofExpr(v___x_2276_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_MessageData_ofExpr(v___x_2277_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Nat_reprFast(v_a_2294_);
v___x_2317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
v___x_2318_ = l_Lean_MessageData_ofFormat(v___x_2317_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2315_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2289_, v___x_2319_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = lean_unbox(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2323_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2322_, v___x_2270_, v_fst_2249_, v_snd_2250_, v___x_2273_, v_a_2321_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2220_ = v___x_2323_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2279_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2324_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2320_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2320_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2332_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2293_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2293_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2340_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2292_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2292_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_unbox(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2288_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2287_, v___x_2270_, v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2286_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
v___y_2220_ = v___x_2288_;
goto v___jp_2219_;
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
v___x_2348_ = lean_box(0);
v___x_2349_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2271_, v___x_2348_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
v___y_2220_ = v___x_2349_;
goto v___jp_2219_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2273_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
lean_dec_ref(v_b_2206_);
lean_dec_ref(v_a_2205_);
lean_dec_ref(v_eq_2204_);
lean_dec(v___y_2203_);
v_a_2350_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2278_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2278_);
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
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2249_, v_snd_2250_, v___x_2273_, v___x_2271_, v___x_2358_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v_snd_2250_);
lean_dec(v_fst_2249_);
v___y_2220_ = v___x_2359_;
goto v___jp_2219_;
}
}
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1, v___y_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1 + 1, v___y_2255_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
if (v_isShared_2253_ == 0)
{
v___x_2260_ = v___x_2252_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_fst_2249_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_snd_2250_);
v___x_2260_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v___x_2260_);
v___x_2262_ = v___x_2247_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2245_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v___x_2262_);
lean_ctor_set(v___x_2242_, 0, v___x_2258_);
v___x_2264_ = v___x_2242_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
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
lean_object* v_a_2364_ = _args[0];
lean_object* v___y_2365_ = _args[1];
lean_object* v_eq_2366_ = _args[2];
lean_object* v_a_2367_ = _args[3];
lean_object* v_b_2368_ = _args[4];
lean_object* v_a_2369_ = _args[5];
lean_object* v___y_2370_ = _args[6];
lean_object* v___y_2371_ = _args[7];
lean_object* v___y_2372_ = _args[8];
lean_object* v___y_2373_ = _args[9];
lean_object* v___y_2374_ = _args[10];
lean_object* v___y_2375_ = _args[11];
lean_object* v___y_2376_ = _args[12];
lean_object* v___y_2377_ = _args[13];
lean_object* v___y_2378_ = _args[14];
lean_object* v___y_2379_ = _args[15];
lean_object* v___y_2380_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2381_; lean_object* v_res_2382_; 
v_a_34491__boxed_2381_ = lean_unbox(v_a_2364_);
v_res_2382_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2381_, v___y_2365_, v_eq_2366_, v_a_2367_, v_b_2368_, v_a_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2383_, lean_object* v_b_2384_, lean_object* v_eq_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2400_; 
lean_inc_ref(v_eq_2385_);
v___x_2400_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2385_, v_a_2386_, v_a_2390_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; uint8_t v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_unbox(v_a_2401_);
lean_dec(v_a_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; 
lean_inc_ref(v_eq_2385_);
v___x_2403_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2385_, v_a_2386_, v_a_2390_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; uint8_t v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = lean_unbox(v_a_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___y_2408_; lean_object* v_toGoalState_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2453_; 
v___x_2406_ = lean_st_ref_get(v_a_2386_);
v_toGoalState_2441_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2406_, 1);
lean_dec(v_unused_2454_);
v___x_2443_ = v___x_2406_;
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_toGoalState_2441_);
lean_dec(v___x_2406_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2409_ = l_Lean_Expr_getAppNumArgs(v_a_2383_);
v___x_2410_ = lean_box(0);
lean_inc_ref(v_b_2384_);
lean_inc_ref(v_a_2383_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_a_2383_);
lean_ctor_set(v___x_2411_, 1, v_b_2384_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2409_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_unbox(v_a_2404_);
v___x_2415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2414_, v___y_2408_, v_eq_2385_, v_a_2383_, v_b_2384_, v___x_2413_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2432_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2432_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2432_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_fst_2420_; 
v_fst_2420_ = lean_ctor_get(v_a_2416_, 0);
lean_inc(v_fst_2420_);
lean_dec(v_a_2416_);
if (lean_obj_tag(v_fst_2420_) == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2426_; 
v___x_2421_ = lean_unsigned_to_nat(2u);
v___x_2422_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
v___x_2423_ = lean_unbox(v_a_2404_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1, v___x_2423_);
v___x_2424_ = lean_unbox(v_a_2404_);
lean_dec(v_a_2404_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*1 + 1, v___x_2424_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2422_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2422_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
else
{
lean_object* v_val_2428_; lean_object* v___x_2430_; 
lean_dec(v_a_2404_);
v_val_2428_ = lean_ctor_get(v_fst_2420_, 0);
lean_inc(v_val_2428_);
lean_dec_ref_known(v_fst_2420_, 1);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v_val_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_val_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_a_2404_);
v_a_2433_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2415_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2415_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
v_resetjp_2442_:
{
lean_object* v_split_2445_; lean_object* v_argPosMap_2446_; lean_object* v___x_2448_; 
v_split_2445_ = lean_ctor_get(v_toGoalState_2441_, 15);
lean_inc_ref(v_split_2445_);
lean_dec_ref(v_toGoalState_2441_);
v_argPosMap_2446_ = lean_ctor_get(v_split_2445_, 6);
lean_inc_ref(v_argPosMap_2446_);
lean_dec_ref(v_split_2445_);
lean_inc_ref(v_b_2384_);
lean_inc_ref(v_a_2383_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v_b_2384_);
lean_ctor_set(v___x_2443_, 0, v_a_2383_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2383_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_b_2384_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2446_, v___x_2448_);
lean_dec_ref(v___x_2448_);
lean_dec_ref(v_argPosMap_2446_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_box(0);
v___y_2408_ = v___x_2450_;
goto v___jp_2407_;
}
else
{
lean_object* v_val_2451_; 
v_val_2451_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2449_, 1);
v___y_2408_ = v_val_2451_;
goto v___jp_2407_;
}
}
}
}
else
{
lean_dec(v_a_2404_);
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
goto v___jp_2397_;
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
v_a_2455_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2403_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2403_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
goto v___jp_2397_;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v_eq_2385_);
lean_dec_ref(v_b_2384_);
lean_dec_ref(v_a_2383_);
v_a_2463_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2400_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2400_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_box(0);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2471_, lean_object* v_b_2472_, lean_object* v_eq_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2471_, v_b_2472_, v_eq_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec(v_a_2474_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2486_, lean_object* v___y_2487_, lean_object* v_eq_2488_, lean_object* v_a_2489_, lean_object* v_b_2490_, lean_object* v_inst_2491_, lean_object* v_a_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2486_, v___y_2487_, v_eq_2488_, v_a_2489_, v_b_2490_, v_a_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2505_ = _args[0];
lean_object* v___y_2506_ = _args[1];
lean_object* v_eq_2507_ = _args[2];
lean_object* v_a_2508_ = _args[3];
lean_object* v_b_2509_ = _args[4];
lean_object* v_inst_2510_ = _args[5];
lean_object* v_a_2511_ = _args[6];
lean_object* v___y_2512_ = _args[7];
lean_object* v___y_2513_ = _args[8];
lean_object* v___y_2514_ = _args[9];
lean_object* v___y_2515_ = _args[10];
lean_object* v___y_2516_ = _args[11];
lean_object* v___y_2517_ = _args[12];
lean_object* v___y_2518_ = _args[13];
lean_object* v___y_2519_ = _args[14];
lean_object* v___y_2520_ = _args[15];
lean_object* v___y_2521_ = _args[16];
lean_object* v___y_2522_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2523_; lean_object* v_res_2524_; 
v_a_34972__boxed_2523_ = lean_unbox(v_a_2505_);
v_res_2524_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2523_, v___y_2506_, v_eq_2507_, v_a_2508_, v_b_2509_, v_inst_2510_, v_a_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec(v___y_2512_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2525_, lean_object* v_m_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2526_, v_a_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2529_, lean_object* v_m_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2529_, v_m_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_m_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2533_, lean_object* v_a_2534_, lean_object* v_x_2535_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2534_, v_x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2537_, lean_object* v_a_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2537_, v_a_2538_, v_x_2539_);
lean_dec(v_x_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2555_; 
lean_inc_ref(v_imp_2541_);
v___x_2555_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2572_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
uint8_t v___x_2563_; 
v___x_2563_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_box(1);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2564_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_box(0);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2568_);
v___x_2570_ = v___x_2561_;
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
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2558_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2558_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_binderType_2581_; lean_object* v_body_2582_; lean_object* v___x_2583_; 
v_binderType_2581_ = lean_ctor_get(v_imp_2541_, 1);
lean_inc_ref_n(v_binderType_2581_, 2);
v_body_2582_ = lean_ctor_get(v_imp_2541_, 2);
lean_inc_ref(v_body_2582_);
lean_dec_ref(v_imp_2541_);
v___x_2583_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2581_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = lean_unbox(v_a_2584_);
lean_dec(v_a_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2581_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2623_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2623_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2623_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_unbox(v_a_2587_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_Expr_hasLooseBVars(v_body_2582_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
lean_inc_ref(v_body_2582_);
v___x_2601_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2582_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; uint8_t v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = lean_unbox(v_a_2602_);
lean_dec(v_a_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2582_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; uint8_t v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
if (v___x_2606_ == 0)
{
goto v___jp_2591_;
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
goto v___jp_2549_;
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
v_a_2607_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2604_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2604_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
goto v___jp_2549_;
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
v_a_2615_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2601_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2601_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_dec_ref(v_body_2582_);
goto v___jp_2591_;
}
}
else
{
lean_del_object(v___x_2589_);
lean_dec(v_a_2587_);
lean_dec_ref(v_body_2582_);
goto v___jp_2552_;
}
v___jp_2591_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2597_; 
v___x_2592_ = lean_unsigned_to_nat(2u);
v___x_2593_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
v___x_2594_ = lean_unbox(v_a_2587_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1, v___x_2594_);
v___x_2595_ = lean_unbox(v_a_2587_);
lean_dec(v_a_2587_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1 + 1, v___x_2595_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2597_ = v___x_2589_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2593_);
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
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_body_2582_);
v_a_2624_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2586_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2586_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_dec_ref(v_body_2582_);
lean_dec_ref(v_binderType_2581_);
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_body_2582_);
lean_dec_ref(v_binderType_2581_);
v_a_2632_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2583_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2583_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_imp_2541_);
v_a_2640_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2555_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2555_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
v___jp_2549_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
v___jp_2552_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2657_, lean_object* v_h_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2657_, v_a_2659_, v_a_2663_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2671_, lean_object* v_h_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2671_, v_h_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
switch(lean_obj_tag(v_s_2685_))
{
case 0:
{
lean_object* v_e_2697_; lean_object* v___x_2698_; 
v_e_2697_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_e_2697_);
lean_dec_ref_known(v_s_2685_, 2);
v___x_2698_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2697_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2698_;
}
case 1:
{
lean_object* v_e_2699_; lean_object* v___x_2700_; 
v_e_2699_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_e_2699_);
lean_dec_ref_known(v_s_2685_, 2);
v___x_2700_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2699_, v_a_2686_, v_a_2690_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2700_;
}
default: 
{
lean_object* v_a_2701_; lean_object* v_b_2702_; lean_object* v_eq_2703_; lean_object* v___x_2704_; 
v_a_2701_ = lean_ctor_get(v_s_2685_, 0);
lean_inc_ref(v_a_2701_);
v_b_2702_ = lean_ctor_get(v_s_2685_, 1);
lean_inc_ref(v_b_2702_);
v_eq_2703_ = lean_ctor_get(v_s_2685_, 3);
lean_inc_ref(v_eq_2703_);
lean_dec_ref_known(v_s_2685_, 5);
v___x_2704_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2701_, v_b_2702_, v_eq_2703_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec(v_a_2706_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_tag_nat(v_x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2720_);
lean_dec(v_x_2720_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2722_, lean_object* v_k_2723_){
_start:
{
if (lean_obj_tag(v_t_2722_) == 0)
{
return v_k_2723_;
}
else
{
lean_object* v_c_2724_; lean_object* v_numCases_2725_; uint8_t v_isRec_2726_; uint8_t v_tryPostpone_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_c_2724_ = lean_ctor_get(v_t_2722_, 0);
lean_inc_ref(v_c_2724_);
v_numCases_2725_ = lean_ctor_get(v_t_2722_, 1);
lean_inc(v_numCases_2725_);
v_isRec_2726_ = lean_ctor_get_uint8(v_t_2722_, sizeof(void*)*2);
v_tryPostpone_2727_ = lean_ctor_get_uint8(v_t_2722_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2722_, 2);
v___x_2728_ = lean_box(v_isRec_2726_);
v___x_2729_ = lean_box(v_tryPostpone_2727_);
v___x_2730_ = lean_apply_4(v_k_2723_, v_c_2724_, v_numCases_2725_, v___x_2728_, v___x_2729_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2731_, lean_object* v_ctorIdx_2732_, lean_object* v_t_2733_, lean_object* v_h_2734_, lean_object* v_k_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2733_, v_k_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2737_, lean_object* v_ctorIdx_2738_, lean_object* v_t_2739_, lean_object* v_h_2740_, lean_object* v_k_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2737_, v_ctorIdx_2738_, v_t_2739_, v_h_2740_, v_k_2741_);
lean_dec(v_ctorIdx_2738_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2743_, lean_object* v_none_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2743_, v_none_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2746_, lean_object* v_t_2747_, lean_object* v_h_2748_, lean_object* v_none_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2747_, v_none_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2751_, lean_object* v_some_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2751_, v_some_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2754_, lean_object* v_t_2755_, lean_object* v_h_2756_, lean_object* v_some_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2755_, v_some_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2759_, lean_object* v_as_2760_, size_t v_i_2761_, size_t v_stop_2762_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_eq(v_i_2761_, v_stop_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = lean_array_uget_borrowed(v_as_2760_, v_i_2761_);
v___x_2765_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2764_, v_a_2759_);
if (v___x_2765_ == 0)
{
size_t v___x_2766_; size_t v___x_2767_; 
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2761_, v___x_2766_);
v_i_2761_ = v___x_2767_;
goto _start;
}
else
{
return v___x_2765_;
}
}
else
{
uint8_t v___x_2769_; 
v___x_2769_ = 0;
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2770_, lean_object* v_as_2771_, lean_object* v_i_2772_, lean_object* v_stop_2773_){
_start:
{
uint64_t v_a_2507__boxed_2774_; size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_a_2507__boxed_2774_ = lean_unbox_uint64(v_a_2770_);
lean_dec_ref(v_a_2770_);
v_i_boxed_2775_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2773_);
lean_dec(v_stop_2773_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2774_, v_as_2771_, v_i_boxed_2775_, v_stop_boxed_2776_);
lean_dec_ref(v_as_2771_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2781_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2834_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2834_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2834_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
if (lean_obj_tag(v_a_2791_) == 1)
{
lean_object* v_val_2795_; lean_object* v___x_2796_; 
lean_del_object(v___x_2793_);
v_val_2795_ = lean_ctor_get(v_a_2791_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v_a_2791_, 1);
v___x_2796_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2820_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_array_get_size(v_val_2795_);
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_dec(v_a_2797_);
lean_dec(v_val_2795_);
v___x_2804_ = lean_box(v___x_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2804_);
v___x_2806_ = v___x_2799_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
if (v___x_2803_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_a_2797_);
lean_dec(v_val_2795_);
v___x_2808_ = lean_box(v___x_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2808_);
v___x_2810_ = v___x_2799_;
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
else
{
size_t v___x_2812_; size_t v___x_2813_; uint64_t v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2812_ = ((size_t)0ULL);
v___x_2813_ = lean_usize_of_nat(v___x_2802_);
v___x_2814_ = lean_unbox_uint64(v_a_2797_);
lean_dec(v_a_2797_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2814_, v_val_2795_, v___x_2812_, v___x_2813_);
lean_dec(v_val_2795_);
v___x_2816_ = lean_box(v___x_2815_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2816_);
v___x_2818_ = v___x_2799_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
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
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec(v_val_2795_);
v_a_2821_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2796_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2796_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_dec(v_a_2791_);
v___x_2829_ = 1;
v___x_2830_ = lean_box(v___x_2829_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2830_);
v___x_2832_ = v___x_2793_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_a_2835_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2790_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2790_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_c_2843_);
return v_res_2854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2857_ = l_Lean_stringToMessageData(v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2858_, lean_object* v_c_x3f_2859_, lean_object* v_cs_x27_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
if (lean_obj_tag(v_cs_2858_) == 0)
{
lean_object* v___x_2872_; lean_object* v_toGoalState_2873_; lean_object* v_split_2874_; lean_object* v_mvarId_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2985_; 
v___x_2872_ = lean_st_ref_take(v_a_2861_);
v_toGoalState_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc_ref(v_toGoalState_2873_);
v_split_2874_ = lean_ctor_get(v_toGoalState_2873_, 15);
lean_inc_ref(v_split_2874_);
v_mvarId_2875_ = lean_ctor_get(v___x_2872_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2986_);
v___x_2877_ = v___x_2872_;
v_isShared_2878_ = v_isSharedCheck_2985_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_mvarId_2875_);
lean_dec(v___x_2872_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2985_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_nextDeclIdx_2879_; lean_object* v_enodeMap_2880_; lean_object* v_exprs_2881_; lean_object* v_parents_2882_; lean_object* v_congrTable_2883_; lean_object* v_appMap_2884_; lean_object* v_indicesFound_2885_; lean_object* v_toProcess_2886_; lean_object* v_internalizing_2887_; uint8_t v_inconsistent_2888_; lean_object* v_nextIdx_2889_; lean_object* v_newRawFacts_2890_; lean_object* v_facts_2891_; lean_object* v_extThms_2892_; lean_object* v_ematch_2893_; lean_object* v_inj_2894_; lean_object* v_clean_2895_; lean_object* v_sstates_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2983_; 
v_nextDeclIdx_2879_ = lean_ctor_get(v_toGoalState_2873_, 0);
v_enodeMap_2880_ = lean_ctor_get(v_toGoalState_2873_, 1);
v_exprs_2881_ = lean_ctor_get(v_toGoalState_2873_, 2);
v_parents_2882_ = lean_ctor_get(v_toGoalState_2873_, 3);
v_congrTable_2883_ = lean_ctor_get(v_toGoalState_2873_, 4);
v_appMap_2884_ = lean_ctor_get(v_toGoalState_2873_, 5);
v_indicesFound_2885_ = lean_ctor_get(v_toGoalState_2873_, 6);
v_toProcess_2886_ = lean_ctor_get(v_toGoalState_2873_, 7);
v_internalizing_2887_ = lean_ctor_get(v_toGoalState_2873_, 8);
v_inconsistent_2888_ = lean_ctor_get_uint8(v_toGoalState_2873_, sizeof(void*)*18);
v_nextIdx_2889_ = lean_ctor_get(v_toGoalState_2873_, 9);
v_newRawFacts_2890_ = lean_ctor_get(v_toGoalState_2873_, 10);
v_facts_2891_ = lean_ctor_get(v_toGoalState_2873_, 11);
v_extThms_2892_ = lean_ctor_get(v_toGoalState_2873_, 12);
v_ematch_2893_ = lean_ctor_get(v_toGoalState_2873_, 13);
v_inj_2894_ = lean_ctor_get(v_toGoalState_2873_, 14);
v_clean_2895_ = lean_ctor_get(v_toGoalState_2873_, 16);
v_sstates_2896_ = lean_ctor_get(v_toGoalState_2873_, 17);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_toGoalState_2873_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_toGoalState_2873_, 15);
lean_dec(v_unused_2984_);
v___x_2898_ = v_toGoalState_2873_;
v_isShared_2899_ = v_isSharedCheck_2983_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_sstates_2896_);
lean_inc(v_clean_2895_);
lean_inc(v_inj_2894_);
lean_inc(v_ematch_2893_);
lean_inc(v_extThms_2892_);
lean_inc(v_facts_2891_);
lean_inc(v_newRawFacts_2890_);
lean_inc(v_nextIdx_2889_);
lean_inc(v_internalizing_2887_);
lean_inc(v_toProcess_2886_);
lean_inc(v_indicesFound_2885_);
lean_inc(v_appMap_2884_);
lean_inc(v_congrTable_2883_);
lean_inc(v_parents_2882_);
lean_inc(v_exprs_2881_);
lean_inc(v_enodeMap_2880_);
lean_inc(v_nextDeclIdx_2879_);
lean_dec(v_toGoalState_2873_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2983_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_num_2900_; lean_object* v_added_2901_; lean_object* v_resolved_2902_; lean_object* v_trace_2903_; lean_object* v_lookaheads_2904_; lean_object* v_argPosMap_2905_; lean_object* v_argsAt_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2981_; 
v_num_2900_ = lean_ctor_get(v_split_2874_, 0);
v_added_2901_ = lean_ctor_get(v_split_2874_, 2);
v_resolved_2902_ = lean_ctor_get(v_split_2874_, 3);
v_trace_2903_ = lean_ctor_get(v_split_2874_, 4);
v_lookaheads_2904_ = lean_ctor_get(v_split_2874_, 5);
v_argPosMap_2905_ = lean_ctor_get(v_split_2874_, 6);
v_argsAt_2906_ = lean_ctor_get(v_split_2874_, 7);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_split_2874_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_split_2874_, 1);
lean_dec(v_unused_2982_);
v___x_2908_ = v_split_2874_;
v_isShared_2909_ = v_isSharedCheck_2981_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_argsAt_2906_);
lean_inc(v_argPosMap_2905_);
lean_inc(v_lookaheads_2904_);
lean_inc(v_trace_2903_);
lean_inc(v_resolved_2902_);
lean_inc(v_added_2901_);
lean_inc(v_num_2900_);
lean_dec(v_split_2874_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2981_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_List_reverse___redArg(v_cs_x27_2860_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 1, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_num_2900_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_added_2901_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_resolved_2902_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_trace_2903_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_lookaheads_2904_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_argPosMap_2905_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_argsAt_2906_);
v___x_2912_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 15, v___x_2912_);
v___x_2914_ = v___x_2898_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_nextDeclIdx_2879_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_enodeMap_2880_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v_exprs_2881_);
lean_ctor_set(v_reuseFailAlloc_2979_, 3, v_parents_2882_);
lean_ctor_set(v_reuseFailAlloc_2979_, 4, v_congrTable_2883_);
lean_ctor_set(v_reuseFailAlloc_2979_, 5, v_appMap_2884_);
lean_ctor_set(v_reuseFailAlloc_2979_, 6, v_indicesFound_2885_);
lean_ctor_set(v_reuseFailAlloc_2979_, 7, v_toProcess_2886_);
lean_ctor_set(v_reuseFailAlloc_2979_, 8, v_internalizing_2887_);
lean_ctor_set(v_reuseFailAlloc_2979_, 9, v_nextIdx_2889_);
lean_ctor_set(v_reuseFailAlloc_2979_, 10, v_newRawFacts_2890_);
lean_ctor_set(v_reuseFailAlloc_2979_, 11, v_facts_2891_);
lean_ctor_set(v_reuseFailAlloc_2979_, 12, v_extThms_2892_);
lean_ctor_set(v_reuseFailAlloc_2979_, 13, v_ematch_2893_);
lean_ctor_set(v_reuseFailAlloc_2979_, 14, v_inj_2894_);
lean_ctor_set(v_reuseFailAlloc_2979_, 15, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2979_, 16, v_clean_2895_);
lean_ctor_set(v_reuseFailAlloc_2979_, 17, v_sstates_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2979_, sizeof(void*)*18, v_inconsistent_2888_);
v___x_2914_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2914_);
v___x_2916_ = v___x_2877_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_mvarId_2875_);
v___x_2916_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_st_ref_put(v_a_2861_, v___x_2916_);
if (lean_obj_tag(v_c_x3f_2859_) == 1)
{
lean_object* v___x_2918_; lean_object* v_toGoalState_2919_; lean_object* v_ematch_2920_; lean_object* v_mvarId_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2975_; 
v___x_2918_ = lean_st_ref_take(v_a_2861_);
v_toGoalState_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_toGoalState_2919_);
v_ematch_2920_ = lean_ctor_get(v_toGoalState_2919_, 13);
lean_inc_ref(v_ematch_2920_);
v_mvarId_2921_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v___x_2918_, 0);
lean_dec(v_unused_2976_);
v___x_2923_ = v___x_2918_;
v_isShared_2924_ = v_isSharedCheck_2975_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_mvarId_2921_);
lean_dec(v___x_2918_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2975_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_nextDeclIdx_2925_; lean_object* v_enodeMap_2926_; lean_object* v_exprs_2927_; lean_object* v_parents_2928_; lean_object* v_congrTable_2929_; lean_object* v_appMap_2930_; lean_object* v_indicesFound_2931_; lean_object* v_toProcess_2932_; lean_object* v_internalizing_2933_; uint8_t v_inconsistent_2934_; lean_object* v_nextIdx_2935_; lean_object* v_newRawFacts_2936_; lean_object* v_facts_2937_; lean_object* v_extThms_2938_; lean_object* v_inj_2939_; lean_object* v_split_2940_; lean_object* v_clean_2941_; lean_object* v_sstates_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2973_; 
v_nextDeclIdx_2925_ = lean_ctor_get(v_toGoalState_2919_, 0);
v_enodeMap_2926_ = lean_ctor_get(v_toGoalState_2919_, 1);
v_exprs_2927_ = lean_ctor_get(v_toGoalState_2919_, 2);
v_parents_2928_ = lean_ctor_get(v_toGoalState_2919_, 3);
v_congrTable_2929_ = lean_ctor_get(v_toGoalState_2919_, 4);
v_appMap_2930_ = lean_ctor_get(v_toGoalState_2919_, 5);
v_indicesFound_2931_ = lean_ctor_get(v_toGoalState_2919_, 6);
v_toProcess_2932_ = lean_ctor_get(v_toGoalState_2919_, 7);
v_internalizing_2933_ = lean_ctor_get(v_toGoalState_2919_, 8);
v_inconsistent_2934_ = lean_ctor_get_uint8(v_toGoalState_2919_, sizeof(void*)*18);
v_nextIdx_2935_ = lean_ctor_get(v_toGoalState_2919_, 9);
v_newRawFacts_2936_ = lean_ctor_get(v_toGoalState_2919_, 10);
v_facts_2937_ = lean_ctor_get(v_toGoalState_2919_, 11);
v_extThms_2938_ = lean_ctor_get(v_toGoalState_2919_, 12);
v_inj_2939_ = lean_ctor_get(v_toGoalState_2919_, 14);
v_split_2940_ = lean_ctor_get(v_toGoalState_2919_, 15);
v_clean_2941_ = lean_ctor_get(v_toGoalState_2919_, 16);
v_sstates_2942_ = lean_ctor_get(v_toGoalState_2919_, 17);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_toGoalState_2919_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v_toGoalState_2919_, 13);
lean_dec(v_unused_2974_);
v___x_2944_ = v_toGoalState_2919_;
v_isShared_2945_ = v_isSharedCheck_2973_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_sstates_2942_);
lean_inc(v_clean_2941_);
lean_inc(v_split_2940_);
lean_inc(v_inj_2939_);
lean_inc(v_extThms_2938_);
lean_inc(v_facts_2937_);
lean_inc(v_newRawFacts_2936_);
lean_inc(v_nextIdx_2935_);
lean_inc(v_internalizing_2933_);
lean_inc(v_toProcess_2932_);
lean_inc(v_indicesFound_2931_);
lean_inc(v_appMap_2930_);
lean_inc(v_congrTable_2929_);
lean_inc(v_parents_2928_);
lean_inc(v_exprs_2927_);
lean_inc(v_enodeMap_2926_);
lean_inc(v_nextDeclIdx_2925_);
lean_dec(v_toGoalState_2919_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2973_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v_thmMap_2946_; lean_object* v_gmt_2947_; lean_object* v_thms_2948_; lean_object* v_newThms_2949_; lean_object* v_numInstances_2950_; lean_object* v_numDelayedInstances_2951_; lean_object* v_preInstances_2952_; lean_object* v_nextThmIdx_2953_; lean_object* v_matchEqNames_2954_; lean_object* v_delayedThmInsts_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2971_; 
v_thmMap_2946_ = lean_ctor_get(v_ematch_2920_, 0);
v_gmt_2947_ = lean_ctor_get(v_ematch_2920_, 1);
v_thms_2948_ = lean_ctor_get(v_ematch_2920_, 2);
v_newThms_2949_ = lean_ctor_get(v_ematch_2920_, 3);
v_numInstances_2950_ = lean_ctor_get(v_ematch_2920_, 4);
v_numDelayedInstances_2951_ = lean_ctor_get(v_ematch_2920_, 5);
v_preInstances_2952_ = lean_ctor_get(v_ematch_2920_, 7);
v_nextThmIdx_2953_ = lean_ctor_get(v_ematch_2920_, 8);
v_matchEqNames_2954_ = lean_ctor_get(v_ematch_2920_, 9);
v_delayedThmInsts_2955_ = lean_ctor_get(v_ematch_2920_, 10);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_ematch_2920_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v_ematch_2920_, 6);
lean_dec(v_unused_2972_);
v___x_2957_ = v_ematch_2920_;
v_isShared_2958_ = v_isSharedCheck_2971_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_delayedThmInsts_2955_);
lean_inc(v_matchEqNames_2954_);
lean_inc(v_nextThmIdx_2953_);
lean_inc(v_preInstances_2952_);
lean_inc(v_numDelayedInstances_2951_);
lean_inc(v_numInstances_2950_);
lean_inc(v_newThms_2949_);
lean_inc(v_thms_2948_);
lean_inc(v_gmt_2947_);
lean_inc(v_thmMap_2946_);
lean_dec(v_ematch_2920_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2971_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 6, v___x_2959_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_thmMap_2946_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_gmt_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_thms_2948_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_newThms_2949_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_numInstances_2950_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v_numDelayedInstances_2951_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_preInstances_2952_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v_nextThmIdx_2953_);
lean_ctor_set(v_reuseFailAlloc_2970_, 9, v_matchEqNames_2954_);
lean_ctor_set(v_reuseFailAlloc_2970_, 10, v_delayedThmInsts_2955_);
v___x_2961_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2963_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 13, v___x_2961_);
v___x_2963_ = v___x_2944_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_nextDeclIdx_2925_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_enodeMap_2926_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_exprs_2927_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_parents_2928_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_congrTable_2929_);
lean_ctor_set(v_reuseFailAlloc_2969_, 5, v_appMap_2930_);
lean_ctor_set(v_reuseFailAlloc_2969_, 6, v_indicesFound_2931_);
lean_ctor_set(v_reuseFailAlloc_2969_, 7, v_toProcess_2932_);
lean_ctor_set(v_reuseFailAlloc_2969_, 8, v_internalizing_2933_);
lean_ctor_set(v_reuseFailAlloc_2969_, 9, v_nextIdx_2935_);
lean_ctor_set(v_reuseFailAlloc_2969_, 10, v_newRawFacts_2936_);
lean_ctor_set(v_reuseFailAlloc_2969_, 11, v_facts_2937_);
lean_ctor_set(v_reuseFailAlloc_2969_, 12, v_extThms_2938_);
lean_ctor_set(v_reuseFailAlloc_2969_, 13, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2969_, 14, v_inj_2939_);
lean_ctor_set(v_reuseFailAlloc_2969_, 15, v_split_2940_);
lean_ctor_set(v_reuseFailAlloc_2969_, 16, v_clean_2941_);
lean_ctor_set(v_reuseFailAlloc_2969_, 17, v_sstates_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, sizeof(void*)*18, v_inconsistent_2934_);
v___x_2963_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_2963_);
v___x_2965_ = v___x_2923_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_mvarId_2921_);
v___x_2965_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_st_ref_put(v_a_2861_, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_c_x3f_2859_);
return v___x_2967_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_c_x3f_2859_);
return v___x_2977_;
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
lean_object* v_head_2987_; lean_object* v_tail_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3208_; 
v_head_2987_ = lean_ctor_get(v_cs_2858_, 0);
v_tail_2988_ = lean_ctor_get(v_cs_2858_, 1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_cs_2858_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_2990_ = v_cs_2858_;
v_isShared_2991_ = v_isSharedCheck_3208_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_tail_2988_);
lean_inc(v_head_2987_);
lean_dec(v_cs_2858_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3208_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; uint8_t v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; uint8_t v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v___x_3100_; 
v___x_3100_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2987_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; uint8_t v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = lean_unbox(v_a_3101_);
lean_dec(v_a_3101_);
if (v___x_3102_ == 0)
{
lean_del_object(v___x_2990_);
lean_dec(v_head_2987_);
v_cs_2858_ = v_tail_2988_;
goto _start;
}
else
{
lean_object* v_toCold_3104_; lean_object* v_options_3105_; lean_object* v_inheritedTraceOptions_3106_; uint8_t v_hasTrace_3107_; uint8_t v___x_3108_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; 
v_toCold_3104_ = lean_ctor_get(v_a_2869_, 0);
v_options_3105_ = lean_ctor_get(v_toCold_3104_, 2);
v_inheritedTraceOptions_3106_ = lean_ctor_get(v_toCold_3104_, 11);
v_hasTrace_3107_ = lean_ctor_get_uint8(v_options_3105_, sizeof(void*)*1);
v___x_3108_ = 0;
if (v_hasTrace_3107_ == 0)
{
v___y_3134_ = v_a_2861_;
v___y_3135_ = v_a_2862_;
v___y_3136_ = v_a_2863_;
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_3176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_3177_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3106_, v_options_3105_, v___x_3176_);
if (v___x_3177_ == 0)
{
v___y_3134_ = v_a_2861_;
v___y_3135_ = v_a_2862_;
v___y_3136_ = v_a_2863_;
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_Grind_updateLastTag(v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref_known(v___x_3178_, 1);
v___x_3179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
v___x_3180_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_head_2987_);
v___x_3181_ = l_Lean_MessageData_ofExpr(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3175_, v___x_3182_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_dec_ref_known(v___x_3183_, 1);
v___y_3134_ = v_a_2861_;
v___y_3135_ = v_a_2862_;
v___y_3136_ = v_a_2863_;
v___y_3137_ = v_a_2864_;
v___y_3138_ = v_a_2865_;
v___y_3139_ = v_a_2866_;
v___y_3140_ = v_a_2867_;
v___y_3141_ = v_a_2868_;
v___y_3142_ = v_a_2869_;
v___y_3143_ = v_a_2870_;
goto v___jp_3133_;
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3192_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3178_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3178_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
v___jp_3109_:
{
if (lean_obj_tag(v_c_x3f_2859_) == 0)
{
lean_object* v___x_3124_; 
lean_del_object(v___x_2990_);
v___x_3124_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3124_, 0, v_head_2987_);
lean_ctor_set(v___x_3124_, 1, v___y_3113_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*2, v___y_3119_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*2 + 1, v___y_3115_);
v_cs_2858_ = v_tail_2988_;
v_c_x3f_2859_ = v___x_3124_;
v_a_2861_ = v___y_3112_;
v_a_2862_ = v___y_3116_;
v_a_2863_ = v___y_3118_;
v_a_2864_ = v___y_3121_;
v_a_2865_ = v___y_3117_;
v_a_2866_ = v___y_3114_;
v_a_2867_ = v___y_3111_;
v_a_2868_ = v___y_3110_;
v_a_2869_ = v___y_3120_;
v_a_2870_ = v___y_3122_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3126_; 
v_tryPostpone_3126_ = lean_ctor_get_uint8(v_c_x3f_2859_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3126_ == 0)
{
if (v___y_3115_ == 0)
{
lean_object* v_c_3127_; lean_object* v_numCases_3128_; 
v_c_3127_ = lean_ctor_get(v_c_x3f_2859_, 0);
v_numCases_3128_ = lean_ctor_get(v_c_x3f_2859_, 1);
lean_inc_ref(v_c_3127_);
lean_inc(v_numCases_3128_);
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v_numCases_3128_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v_c_3127_;
v___y_3091_ = v___y_3117_;
v___y_3092_ = v___y_3118_;
v___y_3093_ = v___y_3119_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___x_3108_;
goto v___jp_3081_;
}
else
{
lean_dec(v___y_3113_);
v___y_2993_ = v___y_3117_;
v___y_2994_ = v___y_3110_;
v___y_2995_ = v___y_3118_;
v___y_2996_ = v___y_3120_;
v___y_2997_ = v___y_3111_;
v___y_2998_ = v___y_3112_;
v___y_2999_ = v___y_3121_;
v___y_3000_ = v___y_3122_;
v___y_3001_ = v___y_3114_;
v___y_3002_ = v___y_3116_;
goto v___jp_2992_;
}
}
else
{
if (v___y_3115_ == 0)
{
lean_object* v_c_3129_; 
lean_del_object(v___x_2990_);
v_c_3129_ = lean_ctor_get(v_c_x3f_2859_, 0);
lean_inc_ref(v_c_3129_);
lean_dec_ref_known(v_c_x3f_2859_, 2);
v___y_3008_ = v___y_3110_;
v___y_3009_ = v___y_3111_;
v___y_3010_ = v___y_3112_;
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v_c_3129_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
goto v___jp_3007_;
}
else
{
if (v___y_3123_ == 0)
{
lean_object* v_c_3130_; lean_object* v_numCases_3131_; 
v_c_3130_ = lean_ctor_get(v_c_x3f_2859_, 0);
v_numCases_3131_ = lean_ctor_get(v_c_x3f_2859_, 1);
lean_inc_ref(v_c_3130_);
lean_inc(v_numCases_3131_);
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___y_3112_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v_numCases_3131_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v_c_3130_;
v___y_3091_ = v___y_3117_;
v___y_3092_ = v___y_3118_;
v___y_3093_ = v___y_3119_;
v___y_3094_ = v___y_3120_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
goto v___jp_3081_;
}
else
{
lean_object* v_c_3132_; 
lean_del_object(v___x_2990_);
v_c_3132_ = lean_ctor_get(v_c_x3f_2859_, 0);
lean_inc_ref(v_c_3132_);
lean_dec_ref_known(v_c_x3f_2859_, 2);
v___y_3008_ = v___y_3110_;
v___y_3009_ = v___y_3111_;
v___y_3010_ = v___y_3112_;
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v___y_3115_;
v___y_3014_ = v___y_3116_;
v___y_3015_ = v_c_3132_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
goto v___jp_3007_;
}
}
}
}
}
v___jp_3133_:
{
lean_object* v___x_3144_; 
lean_inc(v_head_2987_);
v___x_3144_ = l_Lean_Meta_Grind_checkSplitStatus(v_head_2987_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
switch(lean_obj_tag(v_a_3145_))
{
case 0:
{
lean_del_object(v___x_2990_);
lean_dec(v_head_2987_);
v_cs_2858_ = v_tail_2988_;
v_a_2861_ = v___y_3134_;
v_a_2862_ = v___y_3135_;
v_a_2863_ = v___y_3136_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
goto _start;
}
case 1:
{
lean_object* v___x_3147_; 
lean_del_object(v___x_2990_);
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_head_2987_);
lean_ctor_set(v___x_3147_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2988_;
v_cs_x27_2860_ = v___x_3147_;
v_a_2861_ = v___y_3134_;
v_a_2862_ = v___y_3135_;
v_a_2863_ = v___y_3136_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
goto _start;
}
default: 
{
lean_object* v_numCases_3149_; uint8_t v_isRec_3150_; uint8_t v_tryPostpone_3151_; lean_object* v___x_3152_; 
v_numCases_3149_ = lean_ctor_get(v_a_3145_, 0);
lean_inc(v_numCases_3149_);
v_isRec_3150_ = lean_ctor_get_uint8(v_a_3145_, sizeof(void*)*1);
v_tryPostpone_3151_ = lean_ctor_get_uint8(v_a_3145_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_a_3145_, 1);
v___x_3152_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3136_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; uint8_t v___x_3154_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
if (v___x_3154_ == 0)
{
v___y_3110_ = v___y_3141_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3134_;
v___y_3113_ = v_numCases_3149_;
v___y_3114_ = v___y_3139_;
v___y_3115_ = v_tryPostpone_3151_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3138_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v_isRec_3150_;
v___y_3120_ = v___y_3142_;
v___y_3121_ = v___y_3137_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v___x_3108_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_dec_lt(v___x_3155_, v_numCases_3149_);
if (v___x_3156_ == 0)
{
v___y_3110_ = v___y_3141_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3134_;
v___y_3113_ = v_numCases_3149_;
v___y_3114_ = v___y_3139_;
v___y_3115_ = v_tryPostpone_3151_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3138_;
v___y_3118_ = v___y_3136_;
v___y_3119_ = v_isRec_3150_;
v___y_3120_ = v___y_3142_;
v___y_3121_ = v___y_3137_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v___x_3156_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3157_; 
lean_dec(v_numCases_3149_);
lean_del_object(v___x_2990_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_head_2987_);
lean_ctor_set(v___x_3157_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2988_;
v_cs_x27_2860_ = v___x_3157_;
v_a_2861_ = v___y_3134_;
v_a_2862_ = v___y_3135_;
v_a_2863_ = v___y_3136_;
v_a_2864_ = v___y_3137_;
v_a_2865_ = v___y_3138_;
v_a_2866_ = v___y_3139_;
v_a_2867_ = v___y_3140_;
v_a_2868_ = v___y_3141_;
v_a_2869_ = v___y_3142_;
v_a_2870_ = v___y_3143_;
goto _start;
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_numCases_3149_);
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3159_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3152_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3152_);
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
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3167_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3144_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3144_);
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
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3200_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3100_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3100_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
v___jp_2992_:
{
lean_object* v___x_3004_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 1, v_cs_x27_2860_);
v___x_3004_ = v___x_2990_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_head_2987_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_cs_x27_2860_);
v___x_3004_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
v_cs_2858_ = v_tail_2988_;
v_cs_x27_2860_ = v___x_3004_;
v_a_2861_ = v___y_2998_;
v_a_2862_ = v___y_3002_;
v_a_2863_ = v___y_2995_;
v_a_2864_ = v___y_2999_;
v_a_2865_ = v___y_2993_;
v_a_2866_ = v___y_3001_;
v_a_2867_ = v___y_2997_;
v_a_2868_ = v___y_2994_;
v_a_2869_ = v___y_2996_;
v_a_2870_ = v___y_3000_;
goto _start;
}
}
v___jp_3007_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3022_, 0, v_head_2987_);
lean_ctor_set(v___x_3022_, 1, v___y_3011_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*2, v___y_3018_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*2 + 1, v___y_3013_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___y_3015_);
lean_ctor_set(v___x_3023_, 1, v_cs_x27_2860_);
v_cs_2858_ = v_tail_2988_;
v_c_x3f_2859_ = v___x_3022_;
v_cs_x27_2860_ = v___x_3023_;
v_a_2861_ = v___y_3010_;
v_a_2862_ = v___y_3014_;
v_a_2863_ = v___y_3017_;
v_a_2864_ = v___y_3020_;
v_a_2865_ = v___y_3016_;
v_a_2866_ = v___y_3012_;
v_a_2867_ = v___y_3009_;
v_a_2868_ = v___y_3008_;
v_a_2869_ = v___y_3019_;
v_a_2870_ = v___y_3021_;
goto _start;
}
v___jp_3025_:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2987_, v___y_3028_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3034_, v___y_3028_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; uint8_t v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v___x_3045_ = lean_nat_dec_lt(v_a_3042_, v_a_3044_);
lean_dec(v_a_3044_);
lean_dec(v_a_3042_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_lt(v___y_3029_, v___y_3031_);
lean_dec(v___y_3031_);
if (v___x_3046_ == 0)
{
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3029_);
v___y_2993_ = v___y_3035_;
v___y_2994_ = v___y_3026_;
v___y_2995_ = v___y_3036_;
v___y_2996_ = v___y_3038_;
v___y_2997_ = v___y_3027_;
v___y_2998_ = v___y_3028_;
v___y_2999_ = v___y_3039_;
v___y_3000_ = v___y_3040_;
v___y_3001_ = v___y_3030_;
v___y_3002_ = v___y_3033_;
goto v___jp_2992_;
}
else
{
lean_del_object(v___x_2990_);
lean_dec(v_c_x3f_2859_);
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3028_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3032_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3034_;
v___y_3016_ = v___y_3035_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
goto v___jp_3007_;
}
}
else
{
lean_dec(v___y_3031_);
lean_del_object(v___x_2990_);
lean_dec(v_c_x3f_2859_);
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3028_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3030_;
v___y_3013_ = v___y_3032_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3034_;
v___y_3016_ = v___y_3035_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3039_;
v___y_3021_ = v___y_3040_;
goto v___jp_3007_;
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_3042_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3031_);
lean_dec(v___y_3029_);
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3047_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3043_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3043_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3031_);
lean_dec(v___y_3029_);
lean_del_object(v___x_2990_);
lean_dec(v_tail_2988_);
lean_dec(v_head_2987_);
lean_dec(v_cs_x27_2860_);
lean_dec(v_c_x3f_2859_);
v_a_3055_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3041_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3041_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
v___jp_3063_:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_unsigned_to_nat(1u);
v___x_3080_ = lean_nat_dec_lt(v___x_3079_, v___y_3069_);
if (v___x_3080_ == 0)
{
v___y_3026_ = v___y_3064_;
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
goto v___jp_3025_;
}
else
{
lean_dec(v___y_3069_);
lean_del_object(v___x_2990_);
lean_dec(v_c_x3f_2859_);
v___y_3008_ = v___y_3064_;
v___y_3009_ = v___y_3065_;
v___y_3010_ = v___y_3066_;
v___y_3011_ = v___y_3067_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3071_;
v___y_3015_ = v___y_3072_;
v___y_3016_ = v___y_3073_;
v___y_3017_ = v___y_3074_;
v___y_3018_ = v___y_3075_;
v___y_3019_ = v___y_3076_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3078_;
goto v___jp_3007_;
}
}
v___jp_3081_:
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = lean_unsigned_to_nat(1u);
v___x_3099_ = lean_nat_dec_eq(v___y_3085_, v___x_3098_);
if (v___x_3099_ == 0)
{
v___y_3026_ = v___y_3082_;
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
goto v___jp_3025_;
}
else
{
if (v___y_3093_ == 0)
{
v___y_3064_ = v___y_3082_;
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
goto v___jp_3063_;
}
else
{
if (v___y_3097_ == 0)
{
v___y_3026_ = v___y_3082_;
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
goto v___jp_3025_;
}
else
{
v___y_3064_ = v___y_3082_;
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
goto v___jp_3063_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___boxed(lean_object* v_cs_3209_, lean_object* v_c_x3f_3210_, lean_object* v_cs_x27_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_cs_3209_, v_c_x3f_3210_, v_cs_x27_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec(v_a_3212_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3224_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3271_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3271_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3271_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_unbox(v_a_3236_);
lean_dec(v_a_3236_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
lean_del_object(v___x_3238_);
v___x_3241_ = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_3224_, v_a_3226_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3258_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
uint8_t v___x_3246_; 
v___x_3246_ = lean_unbox(v_a_3242_);
lean_dec(v_a_3242_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v_toGoalState_3248_; lean_object* v_split_3249_; lean_object* v_candidates_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_del_object(v___x_3244_);
v___x_3247_ = lean_st_ref_get(v_a_3224_);
v_toGoalState_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_toGoalState_3248_);
lean_dec(v___x_3247_);
v_split_3249_ = lean_ctor_get(v_toGoalState_3248_, 15);
lean_inc_ref(v_split_3249_);
lean_dec_ref(v_toGoalState_3248_);
v_candidates_3250_ = lean_ctor_get(v_split_3249_, 1);
lean_inc(v_candidates_3250_);
lean_dec_ref(v_split_3249_);
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_box(0);
v___x_3253_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(v_candidates_3250_, v___x_3251_, v___x_3252_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3254_ = lean_box(0);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3254_);
v___x_3256_ = v___x_3244_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
v_a_3259_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3241_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3241_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
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
lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3267_ = lean_box(0);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3267_);
v___x_3269_ = v___x_3238_;
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
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_a_3272_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3235_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3235_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f___boxed(lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec(v_a_3280_);
return v_res_3291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_box(0);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3));
v___x_3301_ = l_Lean_mkConst(v___x_3300_, v___x_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* v_c_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
v___x_3304_ = l_Lean_Expr_app___override(v___x_3303_, v_c_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
v___x_3314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3));
v___x_3315_ = l_Lean_mkConst(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6));
v___x_3323_ = l_Lean_mkConst(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_box(0);
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9));
v___x_3331_ = l_Lean_mkConst(v___x_3330_, v___x_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* v_c_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___x_3393_; 
lean_inc_ref(v_c_3332_);
v___x_3393_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3332_, v_a_3340_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3466_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3466_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3466_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = l_Lean_Expr_cleanupAnnotations(v_a_3394_);
v___x_3399_ = l_Lean_Expr_isApp(v___x_3398_);
if (v___x_3399_ == 0)
{
lean_dec_ref(v___x_3398_);
lean_del_object(v___x_3396_);
v___y_3353_ = v_a_3333_;
v___y_3354_ = v_a_3334_;
v___y_3355_ = v_a_3335_;
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
goto v___jp_3352_;
}
else
{
lean_object* v_arg_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_arg_3400_ = lean_ctor_get(v___x_3398_, 1);
lean_inc_ref(v_arg_3400_);
v___x_3401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3398_);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3403_ = l_Lean_Expr_isConstOf(v___x_3401_, v___x_3402_);
if (v___x_3403_ == 0)
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_Expr_isApp(v___x_3401_);
if (v___x_3404_ == 0)
{
lean_dec_ref(v___x_3401_);
lean_dec_ref(v_arg_3400_);
lean_del_object(v___x_3396_);
v___y_3353_ = v_a_3333_;
v___y_3354_ = v_a_3334_;
v___y_3355_ = v_a_3335_;
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
goto v___jp_3352_;
}
else
{
lean_object* v_arg_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_arg_3405_ = lean_ctor_get(v___x_3401_, 1);
lean_inc_ref(v_arg_3405_);
v___x_3406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3401_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3408_ = l_Lean_Expr_isConstOf(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
v___x_3409_ = l_Lean_Expr_isApp(v___x_3406_);
if (v___x_3409_ == 0)
{
lean_dec_ref(v___x_3406_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
lean_del_object(v___x_3396_);
v___y_3353_ = v_a_3333_;
v___y_3354_ = v_a_3334_;
v___y_3355_ = v_a_3335_;
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3406_);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3412_ = l_Lean_Expr_isConstOf(v___x_3410_, v___x_3411_);
lean_dec_ref(v___x_3410_);
if (v___x_3412_ == 0)
{
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
lean_del_object(v___x_3396_);
v___y_3353_ = v_a_3333_;
v___y_3354_ = v_a_3334_;
v___y_3355_ = v_a_3335_;
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
goto v___jp_3352_;
}
else
{
uint8_t v___x_3413_; 
lean_inc_ref(v_c_3332_);
v___x_3413_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3332_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
v___x_3414_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3332_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3414_);
v___x_3416_ = v___x_3396_;
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
else
{
lean_object* v___x_3418_; 
lean_del_object(v___x_3396_);
lean_inc_ref(v_c_3332_);
v___x_3418_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3332_, v_a_3333_, v_a_3337_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; uint8_t v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = lean_unbox(v_a_3419_);
lean_dec(v_a_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3431_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3431_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3431_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3427_ = l_Lean_mkApp3(v___x_3426_, v_arg_3405_, v_arg_3400_, v_a_3422_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3427_);
v___x_3429_ = v___x_3424_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
else
{
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
return v___x_3421_;
}
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
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
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3438_ = l_Lean_mkApp3(v___x_3437_, v_arg_3405_, v_arg_3400_, v_a_3433_);
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
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
return v___x_3432_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
lean_dec_ref(v_c_3332_);
v_a_3443_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3418_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3418_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3451_; 
lean_dec_ref(v___x_3406_);
lean_del_object(v___x_3396_);
v___x_3451_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3461_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3461_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3457_ = l_Lean_mkApp3(v___x_3456_, v_arg_3405_, v_arg_3400_, v_a_3452_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3457_);
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_arg_3400_);
return v___x_3451_;
}
}
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec_ref(v___x_3401_);
lean_dec_ref(v_c_3332_);
v___x_3462_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3400_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3462_);
v___x_3464_ = v___x_3396_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3332_);
return v___x_3393_;
}
v___jp_3344_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = l_Lean_Expr_getAppNumArgs(v_c_3332_);
v___x_3347_ = lean_nat_sub(v___x_3346_, v___x_3345_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_nat_sub(v___x_3347_, v___x_3345_);
lean_dec(v___x_3347_);
v___x_3349_ = l_Lean_Expr_getRevArg_x21(v_c_3332_, v___x_3348_);
lean_dec_ref(v_c_3332_);
v___x_3350_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
v___jp_3352_:
{
uint8_t v___x_3363_; 
v___x_3363_ = l_Lean_Meta_Grind_isIte(v_c_3332_);
if (v___x_3363_ == 0)
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_Meta_Grind_isDIte(v_c_3332_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_inc_ref(v_c_3332_);
v___x_3365_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3332_, v___y_3353_, v___y_3357_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3384_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3384_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3384_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_unbox(v_a_3366_);
lean_dec(v_a_3366_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3372_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_c_3332_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_c_3332_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
else
{
lean_object* v___x_3374_; 
lean_del_object(v___x_3368_);
lean_inc_ref(v_c_3332_);
v___x_3374_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3332_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3383_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3383_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3383_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3379_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3332_, v_a_3375_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3379_);
v___x_3381_ = v___x_3377_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
else
{
lean_dec_ref(v_c_3332_);
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_c_3332_);
v_a_3385_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3365_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3365_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
goto v___jp_3344_;
}
}
else
{
goto v___jp_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec(v_a_3468_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3480_, lean_object* v_major_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3482_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; uint8_t v_trace_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v_trace_3491_ = lean_ctor_get_uint8(v_a_3490_, sizeof(void*)*14);
lean_dec(v_a_3490_);
if (v_trace_3491_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Meta_Grind_cases(v_mvarId_3480_, v_major_3481_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3492_;
}
else
{
lean_object* v___x_3493_; 
lean_inc(v_a_3487_);
lean_inc_ref(v_a_3486_);
lean_inc(v_a_3485_);
lean_inc_ref(v_a_3484_);
lean_inc_ref(v_major_3481_);
v___x_3493_ = lean_infer_type(v_major_3481_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l_Lean_Meta_whnfD(v_a_3494_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l_Lean_Expr_getAppFn(v_a_3496_);
lean_dec(v_a_3496_);
if (lean_obj_tag(v___x_3497_) == 4)
{
lean_object* v_declName_3498_; lean_object* v___x_3499_; 
v_declName_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_declName_3498_);
lean_dec_ref_known(v___x_3497_, 2);
v___x_3499_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3498_, v_a_3483_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v___x_3500_; 
lean_dec_ref_known(v___x_3499_, 1);
v___x_3500_ = l_Lean_Meta_Grind_cases(v_mvarId_3480_, v_major_3481_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3500_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v_major_3481_);
lean_dec(v_mvarId_3480_);
v_a_3501_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3499_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v___x_3509_; 
lean_dec_ref(v___x_3497_);
v___x_3509_ = l_Lean_Meta_Grind_cases(v_mvarId_3480_, v_major_3481_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
return v___x_3509_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_major_3481_);
lean_dec(v_mvarId_3480_);
v_a_3510_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3495_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3495_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v_major_3481_);
lean_dec(v_mvarId_3480_);
v_a_3518_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3493_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3493_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_major_3481_);
lean_dec(v_mvarId_3480_);
v_a_3526_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3489_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3489_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3534_, lean_object* v_major_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3534_, v_major_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3544_, lean_object* v_major_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3544_, v_major_3545_, v_a_3548_, v_a_3549_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3558_, lean_object* v_major_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3558_, v_major_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec(v_a_3560_);
return v_res_3571_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3572_){
_start:
{
uint64_t v_anchor_3573_; 
v_anchor_3573_ = lean_ctor_get_uint64(v_e_3572_, sizeof(void*)*3);
return v_anchor_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3574_){
_start:
{
uint64_t v_res_3575_; lean_object* v_r_3576_; 
v_res_3575_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3574_);
lean_dec_ref(v_e_3574_);
v_r_3576_ = lean_box_uint64(v_res_3575_);
return v_r_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3579_, lean_object* v_x_3580_){
_start:
{
if (lean_obj_tag(v_x_3580_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_box(0);
return v___x_3581_;
}
else
{
lean_object* v_key_3582_; lean_object* v_value_3583_; lean_object* v_tail_3584_; uint64_t v___x_3585_; uint8_t v___x_3586_; 
v_key_3582_ = lean_ctor_get(v_x_3580_, 0);
v_value_3583_ = lean_ctor_get(v_x_3580_, 1);
v_tail_3584_ = lean_ctor_get(v_x_3580_, 2);
v___x_3585_ = lean_unbox_uint64(v_key_3582_);
v___x_3586_ = lean_uint64_dec_eq(v___x_3585_, v_a_3579_);
if (v___x_3586_ == 0)
{
v_x_3580_ = v_tail_3584_;
goto _start;
}
else
{
lean_object* v___x_3588_; 
lean_inc(v_value_3583_);
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_value_3583_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3589_, lean_object* v_x_3590_){
_start:
{
uint64_t v_a_boxed_3591_; lean_object* v_res_3592_; 
v_a_boxed_3591_ = lean_unbox_uint64(v_a_3589_);
lean_dec_ref(v_a_3589_);
v_res_3592_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3591_, v_x_3590_);
lean_dec(v_x_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3593_, uint64_t v_a_3594_){
_start:
{
lean_object* v_buckets_3595_; lean_object* v___x_3596_; uint64_t v___x_3597_; uint64_t v___x_3598_; uint64_t v_fold_3599_; uint64_t v___x_3600_; uint64_t v___x_3601_; uint64_t v___x_3602_; size_t v___x_3603_; size_t v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_buckets_3595_ = lean_ctor_get(v_m_3593_, 1);
v___x_3596_ = lean_array_get_size(v_buckets_3595_);
v___x_3597_ = 32ULL;
v___x_3598_ = lean_uint64_shift_right(v_a_3594_, v___x_3597_);
v_fold_3599_ = lean_uint64_xor(v_a_3594_, v___x_3598_);
v___x_3600_ = 16ULL;
v___x_3601_ = lean_uint64_shift_right(v_fold_3599_, v___x_3600_);
v___x_3602_ = lean_uint64_xor(v_fold_3599_, v___x_3601_);
v___x_3603_ = lean_uint64_to_usize(v___x_3602_);
v___x_3604_ = lean_usize_of_nat(v___x_3596_);
v___x_3605_ = ((size_t)1ULL);
v___x_3606_ = lean_usize_sub(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_usize_land(v___x_3603_, v___x_3606_);
v___x_3608_ = lean_array_uget_borrowed(v_buckets_3595_, v___x_3607_);
v___x_3609_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3594_, v___x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3610_, lean_object* v_a_3611_){
_start:
{
uint64_t v_a_boxed_3612_; lean_object* v_res_3613_; 
v_a_boxed_3612_ = lean_unbox_uint64(v_a_3611_);
lean_dec_ref(v_a_3611_);
v_res_3613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3610_, v_a_boxed_3612_);
lean_dec_ref(v_m_3610_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
if (lean_obj_tag(v_x_3615_) == 0)
{
return v_x_3614_;
}
else
{
lean_object* v_key_3616_; lean_object* v_value_3617_; lean_object* v_tail_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3642_; 
v_key_3616_ = lean_ctor_get(v_x_3615_, 0);
v_value_3617_ = lean_ctor_get(v_x_3615_, 1);
v_tail_3618_ = lean_ctor_get(v_x_3615_, 2);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_x_3615_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3620_ = v_x_3615_;
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_tail_3618_);
lean_inc(v_value_3617_);
lean_inc(v_key_3616_);
lean_dec(v_x_3615_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; uint64_t v___x_3623_; uint64_t v___x_3624_; uint64_t v___x_3625_; uint64_t v___x_3626_; uint64_t v_fold_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v___x_3630_; size_t v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3622_ = lean_array_get_size(v_x_3614_);
v___x_3623_ = 32ULL;
v___x_3624_ = lean_unbox_uint64(v_key_3616_);
v___x_3625_ = lean_uint64_shift_right(v___x_3624_, v___x_3623_);
v___x_3626_ = lean_unbox_uint64(v_key_3616_);
v_fold_3627_ = lean_uint64_xor(v___x_3626_, v___x_3625_);
v___x_3628_ = 16ULL;
v___x_3629_ = lean_uint64_shift_right(v_fold_3627_, v___x_3628_);
v___x_3630_ = lean_uint64_xor(v_fold_3627_, v___x_3629_);
v___x_3631_ = lean_uint64_to_usize(v___x_3630_);
v___x_3632_ = lean_usize_of_nat(v___x_3622_);
v___x_3633_ = ((size_t)1ULL);
v___x_3634_ = lean_usize_sub(v___x_3632_, v___x_3633_);
v___x_3635_ = lean_usize_land(v___x_3631_, v___x_3634_);
v___x_3636_ = lean_array_uget_borrowed(v_x_3614_, v___x_3635_);
lean_inc(v___x_3636_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 2, v___x_3636_);
v___x_3638_ = v___x_3620_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_key_3616_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_value_3617_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_array_uset(v_x_3614_, v___x_3635_, v___x_3638_);
v_x_3614_ = v___x_3639_;
v_x_3615_ = v_tail_3618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3643_, lean_object* v_source_3644_, lean_object* v_target_3645_){
_start:
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = lean_array_get_size(v_source_3644_);
v___x_3647_ = lean_nat_dec_lt(v_i_3643_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_dec_ref(v_source_3644_);
lean_dec(v_i_3643_);
return v_target_3645_;
}
else
{
lean_object* v_es_3648_; lean_object* v___x_3649_; lean_object* v_source_3650_; lean_object* v_target_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v_es_3648_ = lean_array_fget(v_source_3644_, v_i_3643_);
v___x_3649_ = lean_box(0);
v_source_3650_ = lean_array_fset(v_source_3644_, v_i_3643_, v___x_3649_);
v_target_3651_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3645_, v_es_3648_);
v___x_3652_ = lean_unsigned_to_nat(1u);
v___x_3653_ = lean_nat_add(v_i_3643_, v___x_3652_);
lean_dec(v_i_3643_);
v_i_3643_ = v___x_3653_;
v_source_3644_ = v_source_3650_;
v_target_3645_ = v_target_3651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3655_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_nbuckets_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3656_ = lean_array_get_size(v_data_3655_);
v___x_3657_ = lean_unsigned_to_nat(2u);
v_nbuckets_3658_ = lean_nat_mul(v___x_3656_, v___x_3657_);
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_mk_array(v_nbuckets_3658_, v___x_3660_);
v___x_3662_ = lean_array_propagate_mark(v_data_3655_, v___x_3661_);
v___x_3663_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3659_, v_data_3655_, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3664_, lean_object* v_b_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
lean_dec(v_b_3665_);
return v_x_3666_;
}
else
{
lean_object* v_key_3667_; lean_object* v_value_3668_; lean_object* v_tail_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3683_; 
v_key_3667_ = lean_ctor_get(v_x_3666_, 0);
v_value_3668_ = lean_ctor_get(v_x_3666_, 1);
v_tail_3669_ = lean_ctor_get(v_x_3666_, 2);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3666_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3671_ = v_x_3666_;
v_isShared_3672_ = v_isSharedCheck_3683_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_tail_3669_);
lean_inc(v_value_3668_);
lean_inc(v_key_3667_);
lean_dec(v_x_3666_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3683_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
uint64_t v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = lean_unbox_uint64(v_key_3667_);
v___x_3674_ = lean_uint64_dec_eq(v___x_3673_, v_a_3664_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3664_, v_b_3665_, v_tail_3669_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 2, v___x_3675_);
v___x_3677_ = v___x_3671_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_key_3667_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_value_3668_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
lean_dec(v_value_3668_);
lean_dec(v_key_3667_);
v___x_3679_ = lean_box_uint64(v_a_3664_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v_b_3665_);
lean_ctor_set(v___x_3671_, 0, v___x_3679_);
v___x_3681_ = v___x_3671_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_b_3665_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_tail_3669_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3684_, lean_object* v_b_3685_, lean_object* v_x_3686_){
_start:
{
uint64_t v_a_boxed_3687_; lean_object* v_res_3688_; 
v_a_boxed_3687_ = lean_unbox_uint64(v_a_3684_);
lean_dec_ref(v_a_3684_);
v_res_3688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3687_, v_b_3685_, v_x_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3689_, lean_object* v_x_3690_){
_start:
{
if (lean_obj_tag(v_x_3690_) == 0)
{
uint8_t v___x_3691_; 
v___x_3691_ = 0;
return v___x_3691_;
}
else
{
lean_object* v_key_3692_; lean_object* v_tail_3693_; uint64_t v___x_3694_; uint8_t v___x_3695_; 
v_key_3692_ = lean_ctor_get(v_x_3690_, 0);
v_tail_3693_ = lean_ctor_get(v_x_3690_, 2);
v___x_3694_ = lean_unbox_uint64(v_key_3692_);
v___x_3695_ = lean_uint64_dec_eq(v___x_3694_, v_a_3689_);
if (v___x_3695_ == 0)
{
v_x_3690_ = v_tail_3693_;
goto _start;
}
else
{
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3697_, lean_object* v_x_3698_){
_start:
{
uint64_t v_a_boxed_3699_; uint8_t v_res_3700_; lean_object* v_r_3701_; 
v_a_boxed_3699_ = lean_unbox_uint64(v_a_3697_);
lean_dec_ref(v_a_3697_);
v_res_3700_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3699_, v_x_3698_);
lean_dec(v_x_3698_);
v_r_3701_ = lean_box(v_res_3700_);
return v_r_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3702_, uint64_t v_a_3703_, lean_object* v_b_3704_){
_start:
{
lean_object* v_size_3705_; lean_object* v_buckets_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3749_; 
v_size_3705_ = lean_ctor_get(v_m_3702_, 0);
v_buckets_3706_ = lean_ctor_get(v_m_3702_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_m_3702_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3708_ = v_m_3702_;
v_isShared_3709_ = v_isSharedCheck_3749_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_buckets_3706_);
lean_inc(v_size_3705_);
lean_dec(v_m_3702_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3749_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; uint64_t v___x_3711_; uint64_t v___x_3712_; uint64_t v_fold_3713_; uint64_t v___x_3714_; uint64_t v___x_3715_; uint64_t v___x_3716_; size_t v___x_3717_; size_t v___x_3718_; size_t v___x_3719_; size_t v___x_3720_; size_t v___x_3721_; lean_object* v_bkt_3722_; uint8_t v___x_3723_; 
v___x_3710_ = lean_array_get_size(v_buckets_3706_);
v___x_3711_ = 32ULL;
v___x_3712_ = lean_uint64_shift_right(v_a_3703_, v___x_3711_);
v_fold_3713_ = lean_uint64_xor(v_a_3703_, v___x_3712_);
v___x_3714_ = 16ULL;
v___x_3715_ = lean_uint64_shift_right(v_fold_3713_, v___x_3714_);
v___x_3716_ = lean_uint64_xor(v_fold_3713_, v___x_3715_);
v___x_3717_ = lean_uint64_to_usize(v___x_3716_);
v___x_3718_ = lean_usize_of_nat(v___x_3710_);
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_sub(v___x_3718_, v___x_3719_);
v___x_3721_ = lean_usize_land(v___x_3717_, v___x_3720_);
v_bkt_3722_ = lean_array_uget_borrowed(v_buckets_3706_, v___x_3721_);
v___x_3723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3703_, v_bkt_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; lean_object* v_size_x27_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v_buckets_x27_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3724_ = lean_unsigned_to_nat(1u);
v_size_x27_3725_ = lean_nat_add(v_size_3705_, v___x_3724_);
lean_dec(v_size_3705_);
v___x_3726_ = lean_box_uint64(v_a_3703_);
lean_inc(v_bkt_3722_);
v___x_3727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v_b_3704_);
lean_ctor_set(v___x_3727_, 2, v_bkt_3722_);
v_buckets_x27_3728_ = lean_array_uset(v_buckets_3706_, v___x_3721_, v___x_3727_);
v___x_3729_ = lean_unsigned_to_nat(4u);
v___x_3730_ = lean_nat_mul(v_size_x27_3725_, v___x_3729_);
v___x_3731_ = lean_unsigned_to_nat(3u);
v___x_3732_ = lean_nat_div(v___x_3730_, v___x_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_array_get_size(v_buckets_x27_3728_);
v___x_3734_ = lean_nat_dec_le(v___x_3732_, v___x_3733_);
lean_dec(v___x_3732_);
if (v___x_3734_ == 0)
{
lean_object* v_val_3735_; lean_object* v___x_3737_; 
v_val_3735_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3728_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v_val_3735_);
lean_ctor_set(v___x_3708_, 0, v_size_x27_3725_);
v___x_3737_ = v___x_3708_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_size_x27_3725_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_val_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
else
{
lean_object* v___x_3740_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v_buckets_x27_3728_);
lean_ctor_set(v___x_3708_, 0, v_size_x27_3725_);
v___x_3740_ = v___x_3708_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_size_x27_3725_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_buckets_x27_3728_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v_buckets_x27_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_inc(v_bkt_3722_);
v___x_3742_ = lean_box(0);
v_buckets_x27_3743_ = lean_array_uset(v_buckets_3706_, v___x_3721_, v___x_3742_);
v___x_3744_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3703_, v_b_3704_, v_bkt_3722_);
v___x_3745_ = lean_array_uset(v_buckets_x27_3743_, v___x_3721_, v___x_3744_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v___x_3745_);
v___x_3747_ = v___x_3708_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_size_3705_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3750_, lean_object* v_a_3751_, lean_object* v_b_3752_){
_start:
{
uint64_t v_a_boxed_3753_; lean_object* v_res_3754_; 
v_a_boxed_3753_ = lean_unbox_uint64(v_a_3751_);
lean_dec_ref(v_a_3751_);
v_res_3754_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3750_, v_a_boxed_3753_, v_b_3752_);
return v_res_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = lean_box(0);
v___x_3756_ = lean_unsigned_to_nat(16u);
v___x_3757_ = lean_mk_array(v___x_3756_, v___x_3755_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_found_3760_; 
v___x_3758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3759_ = lean_unsigned_to_nat(0u);
v_found_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3760_, 0, v___x_3759_);
lean_ctor_set(v_found_3760_, 1, v___x_3758_);
return v_found_3760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_found_3761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v_found_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3764_, lean_object* v_numDigits_3765_, lean_object* v_es_3766_, lean_object* v_as_3767_, size_t v_sz_3768_, size_t v_i_3769_, lean_object* v_b_3770_){
_start:
{
lean_object* v_a_3772_; uint8_t v___x_3776_; 
v___x_3776_ = lean_usize_dec_lt(v_i_3769_, v_sz_3768_);
if (v___x_3776_ == 0)
{
return v_b_3770_;
}
else
{
lean_object* v_snd_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3811_; 
v_snd_3777_ = lean_ctor_get(v_b_3770_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_b_3770_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_b_3770_, 0);
lean_dec(v_unused_3812_);
v___x_3779_ = v_b_3770_;
v_isShared_3780_ = v_isSharedCheck_3811_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_snd_3777_);
lean_dec(v_b_3770_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3811_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_a_3781_; uint64_t v_anchor_3782_; lean_object* v___x_3783_; uint64_t v___x_3784_; uint64_t v___x_3785_; lean_object* v___x_3786_; 
v_a_3781_ = lean_array_uget_borrowed(v_as_3767_, v_i_3769_);
v_anchor_3782_ = lean_ctor_get_uint64(v_a_3781_, sizeof(void*)*3);
v___x_3783_ = lean_box(0);
v___x_3784_ = lean_uint64_of_nat(v_shift_3764_);
v___x_3785_ = lean_uint64_shift_right(v_anchor_3782_, v___x_3784_);
v___x_3786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3777_, v___x_3785_);
if (lean_obj_tag(v___x_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3805_; 
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3805_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_val_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3805_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
uint64_t v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_unbox_uint64(v_val_3787_);
lean_dec(v_val_3787_);
v___x_3792_ = lean_uint64_dec_eq(v___x_3791_, v_anchor_3782_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_nat_add(v_numDigits_3765_, v___x_3793_);
v___x_3795_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3766_, v___x_3794_);
lean_dec(v___x_3794_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3795_);
v___x_3797_ = v___x_3789_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3799_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3797_);
v___x_3799_ = v___x_3779_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_snd_3777_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
else
{
lean_object* v___x_3803_; 
lean_del_object(v___x_3789_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3783_);
v___x_3803_ = v___x_3779_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_snd_3777_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
v_a_3772_ = v___x_3803_;
goto v___jp_3771_;
}
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_dec(v___x_3786_);
v___x_3806_ = lean_box_uint64(v_anchor_3782_);
v___x_3807_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3777_, v___x_3785_, v___x_3806_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 1, v___x_3807_);
lean_ctor_set(v___x_3779_, 0, v___x_3783_);
v___x_3809_ = v___x_3779_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
v_a_3772_ = v___x_3809_;
goto v___jp_3771_;
}
}
}
}
v___jp_3771_:
{
size_t v___x_3773_; size_t v___x_3774_; 
v___x_3773_ = ((size_t)1ULL);
v___x_3774_ = lean_usize_add(v_i_3769_, v___x_3773_);
v_i_3769_ = v___x_3774_;
v_b_3770_ = v_a_3772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3813_, lean_object* v_numDigits_3814_){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3815_ = lean_unsigned_to_nat(4u);
v___x_3816_ = lean_nat_mul(v___x_3815_, v_numDigits_3814_);
v___x_3817_ = lean_unsigned_to_nat(64u);
v___x_3818_ = lean_nat_dec_lt(v___x_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_dec(v___x_3816_);
lean_inc(v_numDigits_3814_);
return v_numDigits_3814_;
}
else
{
lean_object* v_shift_3819_; lean_object* v___x_3820_; size_t v_sz_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v_fst_3824_; 
v_shift_3819_ = lean_nat_sub(v___x_3817_, v___x_3816_);
lean_dec(v___x_3816_);
v___x_3820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3821_ = lean_array_size(v_es_3813_);
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3819_, v_numDigits_3814_, v_es_3813_, v_es_3813_, v_sz_3821_, v___x_3822_, v___x_3820_);
lean_dec(v_shift_3819_);
v_fst_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_fst_3824_);
lean_dec_ref(v___x_3823_);
if (lean_obj_tag(v_fst_3824_) == 0)
{
lean_inc(v_numDigits_3814_);
return v_numDigits_3814_;
}
else
{
lean_object* v_val_3825_; 
v_val_3825_ = lean_ctor_get(v_fst_3824_, 0);
lean_inc(v_val_3825_);
lean_dec_ref_known(v_fst_3824_, 1);
return v_val_3825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3826_, lean_object* v_numDigits_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3826_, v_numDigits_3827_);
lean_dec(v_numDigits_3827_);
lean_dec_ref(v_es_3826_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3829_, lean_object* v_numDigits_3830_, lean_object* v_es_3831_, lean_object* v_as_3832_, lean_object* v_sz_3833_, lean_object* v_i_3834_, lean_object* v_b_3835_){
_start:
{
size_t v_sz_boxed_3836_; size_t v_i_boxed_3837_; lean_object* v_res_3838_; 
v_sz_boxed_3836_ = lean_unbox_usize(v_sz_3833_);
lean_dec(v_sz_3833_);
v_i_boxed_3837_ = lean_unbox_usize(v_i_3834_);
lean_dec(v_i_3834_);
v_res_3838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3829_, v_numDigits_3830_, v_es_3831_, v_as_3832_, v_sz_boxed_3836_, v_i_boxed_3837_, v_b_3835_);
lean_dec_ref(v_as_3832_);
lean_dec_ref(v_es_3831_);
lean_dec(v_numDigits_3830_);
lean_dec(v_shift_3829_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3839_){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_unsigned_to_nat(4u);
v___x_3841_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3839_, v___x_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3842_);
lean_dec_ref(v_es_3842_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3844_, lean_object* v_as_3845_, size_t v_i_3846_, size_t v_stop_3847_, lean_object* v_b_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_a_3861_; uint8_t v___x_3865_; 
v___x_3865_ = lean_usize_dec_eq(v_i_3846_, v_stop_3847_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; lean_object* v_e_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_array_uget_borrowed(v_as_3845_, v_i_3846_);
v_e_3867_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3866_);
v___x_3868_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3866_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
lean_inc(v___x_3866_);
v___x_3870_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3866_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
if (lean_obj_tag(v_a_3871_) == 2)
{
lean_object* v_numCases_3872_; uint8_t v_isRec_3873_; lean_object* v___x_3874_; 
v_numCases_3872_ = lean_ctor_get(v_a_3871_, 0);
lean_inc(v_numCases_3872_);
v_isRec_3873_ = lean_ctor_get_uint8(v_a_3871_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3871_, 1);
lean_inc_ref(v_filter_3844_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
lean_inc(v___y_3856_);
lean_inc_ref(v___y_3855_);
lean_inc(v___y_3854_);
lean_inc_ref(v___y_3853_);
lean_inc(v___y_3852_);
lean_inc_ref(v___y_3851_);
lean_inc(v___y_3850_);
lean_inc(v___y_3849_);
lean_inc_ref(v_e_3867_);
v___x_3874_ = lean_apply_12(v_filter_3844_, v_e_3867_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, lean_box(0));
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; uint8_t v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = lean_unbox(v_a_3875_);
lean_dec(v_a_3875_);
if (v___x_3876_ == 0)
{
lean_dec(v_numCases_3872_);
lean_dec(v_a_3869_);
lean_dec_ref(v_e_3867_);
v_a_3861_ = v_b_3848_;
goto v___jp_3860_;
}
else
{
lean_object* v___x_3877_; uint64_t v___x_3878_; lean_object* v___x_3879_; 
lean_inc(v___x_3866_);
v___x_3877_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3877_, 0, v___x_3866_);
lean_ctor_set(v___x_3877_, 1, v_numCases_3872_);
lean_ctor_set(v___x_3877_, 2, v_e_3867_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*3 + 8, v_isRec_3873_);
v___x_3878_ = lean_unbox_uint64(v_a_3869_);
lean_dec(v_a_3869_);
lean_ctor_set_uint64(v___x_3877_, sizeof(void*)*3, v___x_3878_);
v___x_3879_ = lean_array_push(v_b_3848_, v___x_3877_);
v_a_3861_ = v___x_3879_;
goto v___jp_3860_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_numCases_3872_);
lean_dec(v_a_3869_);
lean_dec_ref(v_e_3867_);
lean_dec_ref(v_b_3848_);
lean_dec_ref(v_filter_3844_);
v_a_3880_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3874_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3874_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_dec(v_a_3871_);
lean_dec(v_a_3869_);
lean_dec_ref(v_e_3867_);
v_a_3861_ = v_b_3848_;
goto v___jp_3860_;
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_a_3869_);
lean_dec_ref(v_e_3867_);
lean_dec_ref(v_b_3848_);
lean_dec_ref(v_filter_3844_);
v_a_3888_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3870_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3870_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v_e_3867_);
lean_dec_ref(v_b_3848_);
lean_dec_ref(v_filter_3844_);
v_a_3896_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3868_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3868_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v___x_3904_; 
lean_dec_ref(v_filter_3844_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_b_3848_);
return v___x_3904_;
}
v___jp_3860_:
{
size_t v___x_3862_; size_t v___x_3863_; 
v___x_3862_ = ((size_t)1ULL);
v___x_3863_ = lean_usize_add(v_i_3846_, v___x_3862_);
v_i_3846_ = v___x_3863_;
v_b_3848_ = v_a_3861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3905_, lean_object* v_as_3906_, lean_object* v_i_3907_, lean_object* v_stop_3908_, lean_object* v_b_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
size_t v_i_boxed_3921_; size_t v_stop_boxed_3922_; lean_object* v_res_3923_; 
v_i_boxed_3921_ = lean_unbox_usize(v_i_3907_);
lean_dec(v_i_3907_);
v_stop_boxed_3922_ = lean_unbox_usize(v_stop_3908_);
lean_dec(v_stop_3908_);
v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3905_, v_as_3906_, v_i_boxed_3921_, v_stop_boxed_3922_, v_b_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v_as_3906_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3926_, lean_object* v_as_3927_, lean_object* v_start_3928_, lean_object* v_stop_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3941_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3942_ = lean_nat_dec_lt(v_start_3928_, v_stop_3929_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref(v_filter_3926_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
return v___x_3943_;
}
else
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = lean_array_get_size(v_as_3927_);
v___x_3945_ = lean_nat_dec_le(v_stop_3929_, v___x_3944_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_lt(v_start_3928_, v___x_3944_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec_ref(v_filter_3926_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3941_);
return v___x_3947_;
}
else
{
size_t v___x_3948_; size_t v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = lean_usize_of_nat(v_start_3928_);
v___x_3949_ = lean_usize_of_nat(v___x_3944_);
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3926_, v_as_3927_, v___x_3948_, v___x_3949_, v___x_3941_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3950_;
}
}
else
{
size_t v___x_3951_; size_t v___x_3952_; lean_object* v___x_3953_; 
v___x_3951_ = lean_usize_of_nat(v_start_3928_);
v___x_3952_ = lean_usize_of_nat(v_stop_3929_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3926_, v_as_3927_, v___x_3951_, v___x_3952_, v___x_3941_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3954_, lean_object* v_as_3955_, lean_object* v_start_3956_, lean_object* v_stop_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3954_, v_as_3955_, v_start_3956_, v_stop_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec(v_stop_3957_);
lean_dec(v_start_3956_);
lean_dec_ref(v_as_3955_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3970_, lean_object* v_candidates_x3f_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_candidates_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; 
if (lean_obj_tag(v_candidates_x3f_3971_) == 0)
{
lean_object* v___x_4017_; lean_object* v_toGoalState_4018_; lean_object* v_split_4019_; lean_object* v_candidates_4020_; 
v___x_4017_ = lean_st_ref_get(v_a_3972_);
v_toGoalState_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc_ref(v_toGoalState_4018_);
lean_dec(v___x_4017_);
v_split_4019_ = lean_ctor_get(v_toGoalState_4018_, 15);
lean_inc_ref(v_split_4019_);
lean_dec_ref(v_toGoalState_4018_);
v_candidates_4020_ = lean_ctor_get(v_split_4019_, 1);
lean_inc(v_candidates_4020_);
lean_dec_ref(v_split_4019_);
v_candidates_3984_ = v_candidates_4020_;
v___y_3985_ = v_a_3972_;
v___y_3986_ = v_a_3973_;
v___y_3987_ = v_a_3974_;
v___y_3988_ = v_a_3975_;
v___y_3989_ = v_a_3976_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
goto v___jp_3983_;
}
else
{
lean_object* v_val_4021_; 
v_val_4021_ = lean_ctor_get(v_candidates_x3f_3971_, 0);
lean_inc(v_val_4021_);
lean_dec_ref_known(v_candidates_x3f_3971_, 1);
v_candidates_3984_ = v_val_4021_;
v___y_3985_ = v_a_3972_;
v___y_3986_ = v_a_3973_;
v___y_3987_ = v_a_3974_;
v___y_3988_ = v_a_3975_;
v___y_3989_ = v_a_3976_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
goto v___jp_3983_;
}
v___jp_3983_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = lean_array_mk(v_candidates_3984_);
v___x_3996_ = lean_unsigned_to_nat(0u);
v___x_3997_ = lean_array_get_size(v___x_3995_);
v___x_3998_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3970_, v___x_3995_, v___x_3996_, v___x_3997_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec_ref(v___x_3995_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4008_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4008_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4008_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
v___x_4003_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_3999_);
v___x_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4004_, 0, v_a_3999_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4004_);
v___x_4006_ = v___x_4001_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_a_4009_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3998_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3998_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4022_, lean_object* v_candidates_x3f_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4022_, v_candidates_x3f_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec(v_a_4024_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4036_, lean_object* v_m_4037_, uint64_t v_a_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4037_, v_a_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4040_, lean_object* v_m_4041_, lean_object* v_a_4042_){
_start:
{
uint64_t v_a_boxed_4043_; lean_object* v_res_4044_; 
v_a_boxed_4043_ = lean_unbox_uint64(v_a_4042_);
lean_dec_ref(v_a_4042_);
v_res_4044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4040_, v_m_4041_, v_a_boxed_4043_);
lean_dec_ref(v_m_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4045_, lean_object* v_m_4046_, uint64_t v_a_4047_, lean_object* v_b_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4046_, v_a_4047_, v_b_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4050_, lean_object* v_m_4051_, lean_object* v_a_4052_, lean_object* v_b_4053_){
_start:
{
uint64_t v_a_boxed_4054_; lean_object* v_res_4055_; 
v_a_boxed_4054_ = lean_unbox_uint64(v_a_4052_);
lean_dec_ref(v_a_4052_);
v_res_4055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4050_, v_m_4051_, v_a_boxed_4054_, v_b_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4056_, uint64_t v_a_4057_, lean_object* v_x_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4057_, v_x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4060_, lean_object* v_a_4061_, lean_object* v_x_4062_){
_start:
{
uint64_t v_a_boxed_4063_; lean_object* v_res_4064_; 
v_a_boxed_4063_ = lean_unbox_uint64(v_a_4061_);
lean_dec_ref(v_a_4061_);
v_res_4064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4060_, v_a_boxed_4063_, v_x_4062_);
lean_dec(v_x_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4065_, uint64_t v_a_4066_, lean_object* v_x_4067_){
_start:
{
uint8_t v___x_4068_; 
v___x_4068_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4066_, v_x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4069_, lean_object* v_a_4070_, lean_object* v_x_4071_){
_start:
{
uint64_t v_a_boxed_4072_; uint8_t v_res_4073_; lean_object* v_r_4074_; 
v_a_boxed_4072_ = lean_unbox_uint64(v_a_4070_);
lean_dec_ref(v_a_4070_);
v_res_4073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4069_, v_a_boxed_4072_, v_x_4071_);
lean_dec(v_x_4071_);
v_r_4074_ = lean_box(v_res_4073_);
return v_r_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4075_, lean_object* v_data_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4078_, uint64_t v_a_4079_, lean_object* v_b_4080_, lean_object* v_x_4081_){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4079_, v_b_4080_, v_x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4083_, lean_object* v_a_4084_, lean_object* v_b_4085_, lean_object* v_x_4086_){
_start:
{
uint64_t v_a_boxed_4087_; lean_object* v_res_4088_; 
v_a_boxed_4087_ = lean_unbox_uint64(v_a_4084_);
lean_dec_ref(v_a_4084_);
v_res_4088_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4083_, v_a_boxed_4087_, v_b_4085_, v_x_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4089_, lean_object* v_i_4090_, lean_object* v_source_4091_, lean_object* v_target_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4090_, v_source_4091_, v_target_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4095_, v_x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
uint8_t v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = 1;
v___x_4111_ = lean_box(v___x_4110_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v_x_4113_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4126_, uint64_t v_a_4127_, lean_object* v_c_4128_, lean_object* v_numDigits_4129_, lean_object* v_as_4130_, size_t v_sz_4131_, size_t v_i_4132_, lean_object* v_b_4133_){
_start:
{
lean_object* v_a_4136_; uint8_t v___x_4140_; 
v___x_4140_ = lean_usize_dec_lt(v_i_4132_, v_sz_4131_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_dec(v_numDigits_4129_);
v___x_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4141_, 0, v_b_4133_);
return v___x_4141_;
}
else
{
lean_object* v_snd_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4168_; 
v_snd_4142_ = lean_ctor_get(v_b_4133_, 1);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_b_4133_);
if (v_isSharedCheck_4168_ == 0)
{
lean_object* v_unused_4169_; 
v_unused_4169_ = lean_ctor_get(v_b_4133_, 0);
lean_dec(v_unused_4169_);
v___x_4144_ = v_b_4133_;
v_isShared_4145_ = v_isSharedCheck_4168_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_snd_4142_);
lean_dec(v_b_4133_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4168_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v_a_4146_; lean_object* v_c_4147_; uint64_t v_anchor_4148_; lean_object* v___x_4149_; uint64_t v___x_4150_; uint64_t v___x_4151_; uint8_t v___x_4152_; 
v_a_4146_ = lean_array_uget_borrowed(v_as_4130_, v_i_4132_);
v_c_4147_ = lean_ctor_get(v_a_4146_, 0);
v_anchor_4148_ = lean_ctor_get_uint64(v_a_4146_, sizeof(void*)*3);
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_uint64_shift_right(v_anchor_4148_, v___x_4126_);
v___x_4151_ = lean_uint64_shift_right(v_a_4127_, v___x_4126_);
v___x_4152_ = lean_uint64_dec_eq(v___x_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4154_; 
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4149_);
v___x_4154_ = v___x_4144_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_snd_4142_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
v_a_4136_ = v___x_4154_;
goto v___jp_4135_;
}
}
else
{
uint8_t v___x_4156_; 
v___x_4156_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4147_, v_c_4128_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4157_ = lean_unsigned_to_nat(1u);
v___x_4158_ = lean_nat_add(v_snd_4142_, v___x_4157_);
lean_dec(v_snd_4142_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 1, v___x_4158_);
lean_ctor_set(v___x_4144_, 0, v___x_4149_);
v___x_4160_ = v___x_4144_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
v_a_4136_ = v___x_4160_;
goto v___jp_4135_;
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
lean_inc(v_snd_4142_);
v___x_4162_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4162_, 0, v_numDigits_4129_);
lean_ctor_set(v___x_4162_, 1, v_snd_4142_);
lean_ctor_set_uint64(v___x_4162_, sizeof(void*)*2, v_a_4127_);
v___x_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4163_);
v___x_4165_ = v___x_4144_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_snd_4142_);
v___x_4165_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
return v___x_4166_;
}
}
}
}
}
v___jp_4135_:
{
size_t v___x_4137_; size_t v___x_4138_; 
v___x_4137_ = ((size_t)1ULL);
v___x_4138_ = lean_usize_add(v_i_4132_, v___x_4137_);
v_i_4132_ = v___x_4138_;
v_b_4133_ = v_a_4136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4170_, lean_object* v_a_4171_, lean_object* v_c_4172_, lean_object* v_numDigits_4173_, lean_object* v_as_4174_, lean_object* v_sz_4175_, lean_object* v_i_4176_, lean_object* v_b_4177_, lean_object* v___y_4178_){
_start:
{
uint64_t v___x_7695__boxed_4179_; uint64_t v_a_7696__boxed_4180_; size_t v_sz_boxed_4181_; size_t v_i_boxed_4182_; lean_object* v_res_4183_; 
v___x_7695__boxed_4179_ = lean_unbox_uint64(v___x_4170_);
lean_dec_ref(v___x_4170_);
v_a_7696__boxed_4180_ = lean_unbox_uint64(v_a_4171_);
lean_dec_ref(v_a_4171_);
v_sz_boxed_4181_ = lean_unbox_usize(v_sz_4175_);
lean_dec(v_sz_4175_);
v_i_boxed_4182_ = lean_unbox_usize(v_i_4176_);
lean_dec(v_i_4176_);
v_res_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4179_, v_a_7696__boxed_4180_, v_c_4172_, v_numDigits_4173_, v_as_4174_, v_sz_boxed_4181_, v_i_boxed_4182_, v_b_4177_);
lean_dec_ref(v_as_4174_);
lean_dec_ref(v_c_4172_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4188_, lean_object* v_candidates_x3f_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v___f_4201_; lean_object* v___x_4202_; 
v___f_4201_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4202_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4201_, v_candidates_x3f_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v_candidates_4204_; lean_object* v_numDigits_4205_; lean_object* v___x_4206_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v_candidates_4204_ = lean_ctor_get(v_a_4203_, 0);
lean_inc_ref(v_candidates_4204_);
v_numDigits_4205_ = lean_ctor_get(v_a_4203_, 1);
lean_inc(v_numDigits_4205_);
lean_dec(v_a_4203_);
v___x_4206_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4188_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint64_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v_sz_4215_; size_t v___x_4216_; uint64_t v___x_4217_; lean_object* v___x_4218_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4208_ = lean_unsigned_to_nat(64u);
v___x_4209_ = lean_unsigned_to_nat(4u);
v___x_4210_ = lean_nat_mul(v___x_4209_, v_numDigits_4205_);
v___x_4211_ = lean_nat_sub(v___x_4208_, v___x_4210_);
lean_dec(v___x_4210_);
v___x_4212_ = lean_uint64_of_nat(v___x_4211_);
lean_dec(v___x_4211_);
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4214_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4215_ = lean_array_size(v_candidates_4204_);
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = lean_unbox_uint64(v_a_4207_);
lean_inc(v_numDigits_4205_);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4212_, v___x_4217_, v_c_4188_, v_numDigits_4205_, v_candidates_4204_, v_sz_4215_, v___x_4216_, v___x_4214_);
lean_dec_ref(v_candidates_4204_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4233_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4233_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4233_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v_fst_4223_; 
v_fst_4223_ = lean_ctor_get(v_a_4219_, 0);
lean_inc(v_fst_4223_);
lean_dec(v_a_4219_);
if (lean_obj_tag(v_fst_4223_) == 0)
{
lean_object* v___x_4224_; uint64_t v___x_4225_; lean_object* v___x_4227_; 
v___x_4224_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4224_, 0, v_numDigits_4205_);
lean_ctor_set(v___x_4224_, 1, v___x_4213_);
v___x_4225_ = lean_unbox_uint64(v_a_4207_);
lean_dec(v_a_4207_);
lean_ctor_set_uint64(v___x_4224_, sizeof(void*)*2, v___x_4225_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4224_);
v___x_4227_ = v___x_4221_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4224_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
else
{
lean_object* v_val_4229_; lean_object* v___x_4231_; 
lean_dec(v_a_4207_);
lean_dec(v_numDigits_4205_);
v_val_4229_ = lean_ctor_get(v_fst_4223_, 0);
lean_inc(v_val_4229_);
lean_dec_ref_known(v_fst_4223_, 1);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v_val_4229_);
v___x_4231_ = v___x_4221_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_val_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_a_4207_);
lean_dec(v_numDigits_4205_);
v_a_4234_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4218_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4218_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec(v_numDigits_4205_);
lean_dec_ref(v_candidates_4204_);
v_a_4242_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4206_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4206_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
v_a_4250_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4202_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4202_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4258_, lean_object* v_candidates_x3f_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4258_, v_candidates_x3f_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_c_4258_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4272_, uint64_t v_a_4273_, lean_object* v_c_4274_, lean_object* v_numDigits_4275_, lean_object* v_as_4276_, size_t v_sz_4277_, size_t v_i_4278_, lean_object* v_b_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4272_, v_a_4273_, v_c_4274_, v_numDigits_4275_, v_as_4276_, v_sz_4277_, v_i_4278_, v_b_4279_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4292_ = _args[0];
lean_object* v_a_4293_ = _args[1];
lean_object* v_c_4294_ = _args[2];
lean_object* v_numDigits_4295_ = _args[3];
lean_object* v_as_4296_ = _args[4];
lean_object* v_sz_4297_ = _args[5];
lean_object* v_i_4298_ = _args[6];
lean_object* v_b_4299_ = _args[7];
lean_object* v___y_4300_ = _args[8];
lean_object* v___y_4301_ = _args[9];
lean_object* v___y_4302_ = _args[10];
lean_object* v___y_4303_ = _args[11];
lean_object* v___y_4304_ = _args[12];
lean_object* v___y_4305_ = _args[13];
lean_object* v___y_4306_ = _args[14];
lean_object* v___y_4307_ = _args[15];
lean_object* v___y_4308_ = _args[16];
lean_object* v___y_4309_ = _args[17];
lean_object* v___y_4310_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4311_; uint64_t v_a_7895__boxed_4312_; size_t v_sz_boxed_4313_; size_t v_i_boxed_4314_; lean_object* v_res_4315_; 
v___x_7894__boxed_4311_ = lean_unbox_uint64(v___x_4292_);
lean_dec_ref(v___x_4292_);
v_a_7895__boxed_4312_ = lean_unbox_uint64(v_a_4293_);
lean_dec_ref(v_a_4293_);
v_sz_boxed_4313_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4314_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4311_, v_a_7895__boxed_4312_, v_c_4294_, v_numDigits_4295_, v_as_4296_, v_sz_boxed_4313_, v_i_boxed_4314_, v_b_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v_as_4296_);
lean_dec_ref(v_c_4294_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_numDigits_4343_; uint64_t v_anchor_4344_; lean_object* v_ordinal_4345_; lean_object* v___x_4346_; 
v_numDigits_4343_ = lean_ctor_get(v_info_4340_, 0);
v_anchor_4344_ = lean_ctor_get_uint64(v_info_4340_, sizeof(void*)*2);
v_ordinal_4345_ = lean_ctor_get(v_info_4340_, 1);
v___x_4346_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4343_, v_anchor_4344_, v_a_4341_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4383_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4349_ = v___x_4346_;
v_isShared_4350_ = v_isSharedCheck_4383_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4383_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = lean_nat_dec_eq(v_ordinal_4345_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v_ref_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v_ref_4353_ = lean_ctor_get(v_a_4341_, 2);
v___x_4354_ = l_Lean_SourceInfo_fromRef(v_ref_4353_, v___x_4352_);
v___x_4355_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4356_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4354_, 3);
v___x_4357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4354_);
lean_ctor_set(v___x_4357_, 1, v___x_4355_);
v___x_4358_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4359_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4354_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_nat_add(v_ordinal_4345_, v___x_4361_);
v___x_4363_ = l_Nat_reprFast(v___x_4362_);
v___x_4364_ = lean_box(2);
v___x_4365_ = l_Lean_Syntax_mkNumLit(v___x_4363_, v___x_4364_);
v___x_4366_ = l_Lean_Syntax_node3(v___x_4354_, v___x_4358_, v_a_4347_, v___x_4360_, v___x_4365_);
v___x_4367_ = l_Lean_Syntax_node2(v___x_4354_, v___x_4356_, v___x_4357_, v___x_4366_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4367_);
v___x_4369_ = v___x_4349_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
else
{
lean_object* v_ref_4371_; uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v_ref_4371_ = lean_ctor_get(v_a_4341_, 2);
v___x_4372_ = 0;
v___x_4373_ = l_Lean_SourceInfo_fromRef(v_ref_4371_, v___x_4372_);
v___x_4374_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4375_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4373_, 2);
v___x_4376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4373_);
lean_ctor_set(v___x_4376_, 1, v___x_4374_);
v___x_4377_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4378_ = l_Lean_Syntax_node1(v___x_4373_, v___x_4377_, v_a_4347_);
v___x_4379_ = l_Lean_Syntax_node2(v___x_4373_, v___x_4375_, v___x_4376_, v___x_4378_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4379_);
v___x_4381_ = v___x_4349_;
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
}
}
else
{
return v___x_4346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4384_, v_a_4385_);
lean_dec_ref(v_a_4385_);
lean_dec_ref(v_info_4384_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4388_, v_a_4389_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4393_, v_a_4394_, v_a_4395_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec_ref(v_info_4393_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v_p_4429_; lean_object* v___x_4432_; 
lean_inc_ref(v_proof_4410_);
v___x_4432_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4410_, v_a_4412_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4459_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4459_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4459_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = l_Lean_Expr_cleanupAnnotations(v_a_4433_);
v___x_4438_ = l_Lean_Expr_isApp(v___x_4437_);
if (v___x_4438_ == 0)
{
lean_dec_ref(v___x_4437_);
lean_del_object(v___x_4435_);
v___y_4417_ = v_a_4411_;
v___y_4418_ = v_a_4412_;
v___y_4419_ = v_a_4413_;
v___y_4420_ = v_a_4414_;
goto v___jp_4416_;
}
else
{
lean_object* v_arg_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v_arg_4439_ = lean_ctor_get(v___x_4437_, 1);
lean_inc_ref(v_arg_4439_);
v___x_4440_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4437_);
v___x_4441_ = l_Lean_Expr_isApp(v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec_ref(v___x_4440_);
lean_dec_ref(v_arg_4439_);
lean_del_object(v___x_4435_);
v___y_4417_ = v_a_4411_;
v___y_4418_ = v_a_4412_;
v___y_4419_ = v_a_4413_;
v___y_4420_ = v_a_4414_;
goto v___jp_4416_;
}
else
{
lean_object* v_arg_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; 
v_arg_4442_ = lean_ctor_get(v___x_4440_, 1);
lean_inc_ref(v_arg_4442_);
v___x_4443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4440_);
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4445_ = l_Lean_Expr_isConstOf(v___x_4443_, v___x_4444_);
if (v___x_4445_ == 0)
{
lean_object* v___x_4446_; uint8_t v___x_4447_; 
lean_dec_ref(v_arg_4442_);
lean_del_object(v___x_4435_);
v___x_4446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4447_ = l_Lean_Expr_isConstOf(v___x_4443_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4449_ = l_Lean_Expr_isConstOf(v___x_4443_, v___x_4448_);
lean_dec_ref(v___x_4443_);
if (v___x_4449_ == 0)
{
lean_dec_ref(v_arg_4439_);
v___y_4417_ = v_a_4411_;
v___y_4418_ = v_a_4412_;
v___y_4419_ = v_a_4413_;
v___y_4420_ = v_a_4414_;
goto v___jp_4416_;
}
else
{
lean_dec_ref(v_proof_4410_);
v_p_4429_ = v_arg_4439_;
goto v___jp_4428_;
}
}
else
{
lean_dec_ref(v___x_4443_);
lean_dec_ref(v_proof_4410_);
v_p_4429_ = v_arg_4439_;
goto v___jp_4428_;
}
}
else
{
uint8_t v___x_4450_; 
lean_dec_ref(v___x_4443_);
lean_dec_ref(v_proof_4410_);
v___x_4450_ = l_Lean_Expr_isFalse(v_arg_4442_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v___x_4453_; 
lean_dec_ref(v_arg_4439_);
v___x_4451_ = lean_box(0);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4451_);
v___x_4453_ = v___x_4435_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
else
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v_arg_4439_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4455_);
v___x_4457_ = v___x_4435_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v_proof_4410_);
v_a_4460_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4432_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4432_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
v___jp_4416_:
{
if (lean_obj_tag(v_proof_4410_) == 6)
{
lean_object* v_body_4421_; uint8_t v___x_4422_; 
v_body_4421_ = lean_ctor_get(v_proof_4410_, 2);
lean_inc_ref(v_body_4421_);
lean_dec_ref_known(v_proof_4410_, 3);
v___x_4422_ = l_Lean_Expr_hasLooseBVars(v_body_4421_);
if (v___x_4422_ == 0)
{
v_proof_4410_ = v_body_4421_;
v_a_4411_ = v___y_4417_;
v_a_4412_ = v___y_4418_;
v_a_4413_ = v___y_4419_;
v_a_4414_ = v___y_4420_;
goto _start;
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_dec_ref(v_body_4421_);
v___x_4424_ = lean_box(0);
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
return v___x_4425_;
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_dec_ref(v_proof_4410_);
v___x_4426_ = lean_box(0);
v___x_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
return v___x_4427_;
}
}
v___jp_4428_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4430_, 0, v_p_4429_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v___x_4478_; 
v___x_4478_ = l_Lean_Expr_hasMVar(v_e_4475_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v_e_4475_);
return v___x_4479_;
}
else
{
lean_object* v___x_4480_; lean_object* v_mctx_4481_; lean_object* v___x_4482_; lean_object* v_fst_4483_; lean_object* v_snd_4484_; lean_object* v___x_4485_; lean_object* v_cache_4486_; lean_object* v_zetaDeltaFVarIds_4487_; lean_object* v_postponed_4488_; lean_object* v_diag_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4498_; 
v___x_4480_ = lean_st_ref_get(v___y_4476_);
v_mctx_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc_ref(v_mctx_4481_);
lean_dec(v___x_4480_);
v___x_4482_ = l_Lean_instantiateMVarsCore(v_mctx_4481_, v_e_4475_);
v_fst_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_fst_4483_);
v_snd_4484_ = lean_ctor_get(v___x_4482_, 1);
lean_inc(v_snd_4484_);
lean_dec_ref(v___x_4482_);
v___x_4485_ = lean_st_ref_take(v___y_4476_);
v_cache_4486_ = lean_ctor_get(v___x_4485_, 1);
v_zetaDeltaFVarIds_4487_ = lean_ctor_get(v___x_4485_, 2);
v_postponed_4488_ = lean_ctor_get(v___x_4485_, 3);
v_diag_4489_ = lean_ctor_get(v___x_4485_, 4);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4485_, 0);
lean_dec(v_unused_4499_);
v___x_4491_ = v___x_4485_;
v_isShared_4492_ = v_isSharedCheck_4498_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_diag_4489_);
lean_inc(v_postponed_4488_);
lean_inc(v_zetaDeltaFVarIds_4487_);
lean_inc(v_cache_4486_);
lean_dec(v___x_4485_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4498_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v_snd_4484_);
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_snd_4484_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_cache_4486_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_zetaDeltaFVarIds_4487_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_postponed_4488_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v_diag_4489_);
v___x_4494_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_st_ref_put(v___y_4476_, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v_fst_4483_);
return v___x_4496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4500_, v___y_4501_);
lean_dec(v___y_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4504_, v___y_4506_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4518_, lean_object* v_x_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4518_, v_x_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4525_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
v_a_4534_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4525_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4525_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4542_, lean_object* v_x_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4542_, v_x_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4550_, lean_object* v_mvarId_4551_, lean_object* v_x_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4551_, v_x_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4559_, lean_object* v_mvarId_4560_, lean_object* v_x_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4559_, v_mvarId_4560_, v_x_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___x_4574_; lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4585_; 
v___x_4574_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4568_, v___y_4570_);
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4585_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4585_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
uint8_t v___x_4579_; 
v___x_4579_ = l_Lean_Expr_hasSyntheticSorry(v_a_4575_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
lean_del_object(v___x_4577_);
v___x_4580_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4575_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
lean_dec(v_a_4575_);
v___x_4581_ = lean_box(0);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4581_);
v___x_4583_ = v___x_4577_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; lean_object* v___f_4600_; lean_object* v___x_4601_; 
lean_inc(v_mvarId_4593_);
v___x_4599_ = l_Lean_mkMVar(v_mvarId_4593_);
v___f_4600_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4600_, 0, v___x_4599_);
v___x_4601_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4593_, v___f_4600_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
return v_res_4608_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4630_){
_start:
{
if (lean_obj_tag(v_x_4630_) == 0)
{
uint8_t v___x_4631_; 
v___x_4631_ = 1;
return v___x_4631_;
}
else
{
lean_object* v_head_4632_; lean_object* v_tail_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; 
v_head_4632_ = lean_ctor_get(v_x_4630_, 0);
lean_inc_n(v_head_4632_, 2);
v_tail_4633_ = lean_ctor_get(v_x_4630_, 1);
lean_inc(v_tail_4633_);
lean_dec_ref_known(v_x_4630_, 2);
v___x_4634_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4635_ = l_Lean_Syntax_isOfKind(v_head_4632_, v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4636_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4632_);
v___x_4637_ = l_Lean_Syntax_isOfKind(v_head_4632_, v___x_4636_);
if (v___x_4637_ == 0)
{
lean_dec(v_head_4632_);
v_x_4630_ = v_tail_4633_;
goto _start;
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4639_ = lean_unsigned_to_nat(1u);
v___x_4640_ = l_Lean_Syntax_getArg(v_head_4632_, v___x_4639_);
lean_dec(v_head_4632_);
v___x_4641_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4642_ = l_Lean_Syntax_isOfKind(v___x_4640_, v___x_4641_);
if (v___x_4642_ == 0)
{
v_x_4630_ = v_tail_4633_;
goto _start;
}
else
{
lean_dec(v_tail_4633_);
return v___x_4635_;
}
}
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4644_ = lean_unsigned_to_nat(3u);
v___x_4645_ = l_Lean_Syntax_getArg(v_head_4632_, v___x_4644_);
lean_dec(v_head_4632_);
v___x_4646_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4647_ = l_Lean_Syntax_isOfKind(v___x_4645_, v___x_4646_);
if (v___x_4647_ == 0)
{
v_x_4630_ = v_tail_4633_;
goto _start;
}
else
{
uint8_t v___x_4649_; 
lean_dec(v_tail_4633_);
v___x_4649_ = 0;
return v___x_4649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4650_){
_start:
{
uint8_t v_res_4651_; lean_object* v_r_4652_; 
v_res_4651_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4650_);
v_r_4652_ = lean_box(v_res_4651_);
return v_r_4652_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4653_){
_start:
{
uint8_t v___x_4654_; 
v___x_4654_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4655_){
_start:
{
uint8_t v_res_4656_; lean_object* v_r_4657_; 
v_res_4656_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4655_);
v_r_4657_ = lean_box(v_res_4656_);
return v_r_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4673_, lean_object* v_a_4674_){
_start:
{
if (lean_obj_tag(v_seq_4673_) == 0)
{
lean_object* v_ref_4676_; uint8_t v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v_ref_4676_ = lean_ctor_get(v_a_4674_, 2);
v___x_4677_ = 0;
v___x_4678_ = l_Lean_SourceInfo_fromRef(v_ref_4676_, v___x_4677_);
v___x_4679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4678_);
v___x_4681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4678_);
lean_ctor_set(v___x_4681_, 1, v___x_4679_);
v___x_4682_ = l_Lean_Syntax_node1(v___x_4678_, v___x_4680_, v___x_4681_);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
else
{
lean_object* v_tail_4684_; 
v_tail_4684_ = lean_ctor_get(v_seq_4673_, 1);
if (lean_obj_tag(v_tail_4684_) == 0)
{
lean_object* v_head_4685_; lean_object* v___x_4686_; 
v_head_4685_ = lean_ctor_get(v_seq_4673_, 0);
lean_inc(v_head_4685_);
lean_dec_ref_known(v_seq_4673_, 2);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_head_4685_);
return v___x_4686_;
}
else
{
lean_object* v_head_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4709_; 
lean_inc(v_tail_4684_);
v_head_4687_ = lean_ctor_get(v_seq_4673_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_seq_4673_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v_seq_4673_, 1);
lean_dec(v_unused_4710_);
v___x_4689_ = v_seq_4673_;
v_isShared_4690_ = v_isSharedCheck_4709_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_head_4687_);
lean_dec(v_seq_4673_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4709_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4708_; 
v___x_4691_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4684_, v_a_4674_);
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4708_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4708_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_ref_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
v_ref_4696_ = lean_ctor_get(v_a_4674_, 2);
v___x_4697_ = 0;
v___x_4698_ = l_Lean_SourceInfo_fromRef(v_ref_4696_, v___x_4697_);
v___x_4699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4698_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 2);
lean_ctor_set(v___x_4689_, 1, v___x_4700_);
lean_ctor_set(v___x_4689_, 0, v___x_4698_);
v___x_4702_ = v___x_4689_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v___x_4700_);
v___x_4702_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4703_ = l_Lean_Syntax_node3(v___x_4698_, v___x_4699_, v_head_4687_, v___x_4702_, v_a_4692_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4703_);
v___x_4705_ = v___x_4694_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4703_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4711_, v_a_4712_);
lean_dec_ref(v_a_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4715_, v_a_4716_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4720_, v_a_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4725_, lean_object* v_seq_4726_, lean_object* v_a_4727_){
_start:
{
if (lean_obj_tag(v_seq_4726_) == 0)
{
lean_object* v___x_4729_; 
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v_cases_4725_);
return v___x_4729_;
}
else
{
lean_object* v___x_4730_; lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4745_; 
v___x_4730_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4726_, v_a_4727_);
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4733_ = v___x_4730_;
v_isShared_4734_ = v_isSharedCheck_4745_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4730_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4745_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v_ref_4735_; uint8_t v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4743_; 
v_ref_4735_ = lean_ctor_get(v_a_4727_, 2);
v___x_4736_ = 0;
v___x_4737_ = l_Lean_SourceInfo_fromRef(v_ref_4735_, v___x_4736_);
v___x_4738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4737_);
v___x_4740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4737_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = l_Lean_Syntax_node3(v___x_4737_, v___x_4738_, v_cases_4725_, v___x_4740_, v_a_4731_);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 0, v___x_4741_);
v___x_4743_ = v___x_4733_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4746_, lean_object* v_seq_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4746_, v_seq_4747_, v_a_4748_);
lean_dec_ref(v_a_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4751_, lean_object* v_seq_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4751_, v_seq_4752_, v_a_4753_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4757_, lean_object* v_seq_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4757_, v_seq_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
return v_res_4762_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4763_, lean_object* v_x_4764_){
_start:
{
if (lean_obj_tag(v_x_4763_) == 0)
{
if (lean_obj_tag(v_x_4764_) == 0)
{
uint8_t v___x_4765_; 
v___x_4765_ = 1;
return v___x_4765_;
}
else
{
uint8_t v___x_4766_; 
v___x_4766_ = 0;
return v___x_4766_;
}
}
else
{
if (lean_obj_tag(v_x_4764_) == 0)
{
uint8_t v___x_4767_; 
v___x_4767_ = 0;
return v___x_4767_;
}
else
{
lean_object* v_head_4768_; lean_object* v_tail_4769_; lean_object* v_head_4770_; lean_object* v_tail_4771_; uint8_t v___x_4772_; 
v_head_4768_ = lean_ctor_get(v_x_4763_, 0);
v_tail_4769_ = lean_ctor_get(v_x_4763_, 1);
v_head_4770_ = lean_ctor_get(v_x_4764_, 0);
v_tail_4771_ = lean_ctor_get(v_x_4764_, 1);
v___x_4772_ = l_Lean_Syntax_structEq(v_head_4768_, v_head_4770_);
if (v___x_4772_ == 0)
{
return v___x_4772_;
}
else
{
v_x_4763_ = v_tail_4769_;
v_x_4764_ = v_tail_4771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4774_, lean_object* v_x_4775_){
_start:
{
uint8_t v_res_4776_; lean_object* v_r_4777_; 
v_res_4776_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4774_, v_x_4775_);
lean_dec(v_x_4775_);
lean_dec(v_x_4774_);
v_r_4777_ = lean_box(v_res_4776_);
return v_r_4777_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4778_, lean_object* v___x_4779_, lean_object* v_as_4780_, size_t v_i_4781_, size_t v_stop_4782_){
_start:
{
uint8_t v___x_4787_; 
v___x_4787_ = lean_usize_dec_eq(v_i_4781_, v_stop_4782_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = lean_array_uget_borrowed(v_as_4780_, v_i_4781_);
v___x_4789_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4788_, v_alt_4778_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; uint8_t v___x_4791_; 
v___x_4790_ = lean_unsigned_to_nat(0u);
v___x_4791_ = lean_nat_dec_lt(v___x_4790_, v___x_4779_);
if (v___x_4791_ == 0)
{
goto v___jp_4783_;
}
else
{
return v___x_4791_;
}
}
else
{
goto v___jp_4783_;
}
}
else
{
uint8_t v___x_4792_; 
v___x_4792_ = 0;
return v___x_4792_;
}
v___jp_4783_:
{
size_t v___x_4784_; size_t v___x_4785_; 
v___x_4784_ = ((size_t)1ULL);
v___x_4785_ = lean_usize_add(v_i_4781_, v___x_4784_);
v_i_4781_ = v___x_4785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4793_, lean_object* v___x_4794_, lean_object* v_as_4795_, lean_object* v_i_4796_, lean_object* v_stop_4797_){
_start:
{
size_t v_i_boxed_4798_; size_t v_stop_boxed_4799_; uint8_t v_res_4800_; lean_object* v_r_4801_; 
v_i_boxed_4798_ = lean_unbox_usize(v_i_4796_);
lean_dec(v_i_4796_);
v_stop_boxed_4799_ = lean_unbox_usize(v_stop_4797_);
lean_dec(v_stop_4797_);
v_res_4800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4793_, v___x_4794_, v_as_4795_, v_i_boxed_4798_, v_stop_boxed_4799_);
lean_dec_ref(v_as_4795_);
lean_dec(v___x_4794_);
lean_dec(v_alt_4793_);
v_r_4801_ = lean_box(v_res_4800_);
return v_r_4801_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4802_){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; 
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = lean_array_get_size(v_alts_4802_);
v___x_4805_ = lean_nat_dec_lt(v___x_4803_, v___x_4804_);
if (v___x_4805_ == 0)
{
uint8_t v___x_4806_; 
v___x_4806_ = 1;
return v___x_4806_;
}
else
{
lean_object* v_alt_4807_; uint8_t v___x_4808_; 
v_alt_4807_ = lean_array_fget_borrowed(v_alts_4802_, v___x_4803_);
lean_inc(v_alt_4807_);
v___x_4808_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4807_);
if (v___x_4808_ == 0)
{
return v___x_4808_;
}
else
{
if (v___x_4805_ == 0)
{
return v___x_4805_;
}
else
{
size_t v___x_4809_; size_t v___x_4810_; uint8_t v___x_4811_; 
v___x_4809_ = ((size_t)0ULL);
v___x_4810_ = lean_usize_of_nat(v___x_4804_);
v___x_4811_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4807_, v___x_4804_, v_alts_4802_, v___x_4809_, v___x_4810_);
if (v___x_4811_ == 0)
{
return v___x_4805_;
}
else
{
uint8_t v___x_4812_; 
v___x_4812_ = 0;
return v___x_4812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4813_){
_start:
{
uint8_t v_res_4814_; lean_object* v_r_4815_; 
v_res_4814_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4813_);
lean_dec_ref(v_alts_4813_);
v_r_4815_ = lean_box(v_res_4814_);
return v_r_4815_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4823_){
_start:
{
if (lean_obj_tag(v_alt_4823_) == 1)
{
lean_object* v_tail_4824_; 
v_tail_4824_ = lean_ctor_get(v_alt_4823_, 1);
if (lean_obj_tag(v_tail_4824_) == 0)
{
lean_object* v_head_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v_head_4825_ = lean_ctor_get(v_alt_4823_, 0);
lean_inc(v_head_4825_);
lean_dec_ref_known(v_alt_4823_, 2);
v___x_4826_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4827_ = l_Lean_Syntax_isOfKind(v_head_4825_, v___x_4826_);
return v___x_4827_;
}
else
{
uint8_t v___x_4828_; 
lean_dec_ref_known(v_alt_4823_, 2);
v___x_4828_ = 0;
return v___x_4828_;
}
}
else
{
uint8_t v___x_4829_; 
lean_dec(v_alt_4823_);
v___x_4829_ = 0;
return v___x_4829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4830_){
_start:
{
uint8_t v_res_4831_; lean_object* v_r_4832_; 
v_res_4831_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4830_);
v_r_4832_ = lean_box(v_res_4831_);
return v_r_4832_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4833_, lean_object* v_x_4834_, lean_object* v___y_4835_){
_start:
{
if (lean_obj_tag(v_x_4833_) == 0)
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = l_List_reverse___redArg(v_x_4834_);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
return v___x_4838_;
}
else
{
lean_object* v_head_4839_; lean_object* v_tail_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4858_; 
v_head_4839_ = lean_ctor_get(v_x_4833_, 0);
v_tail_4840_ = lean_ctor_get(v_x_4833_, 1);
v_isSharedCheck_4858_ = !lean_is_exclusive(v_x_4833_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4842_ = v_x_4833_;
v_isShared_4843_ = v_isSharedCheck_4858_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_tail_4840_);
lean_inc(v_head_4839_);
lean_dec(v_x_4833_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4858_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4839_, v___y_4835_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref_known(v___x_4844_, 1);
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 1, v_x_4834_);
lean_ctor_set(v___x_4842_, 0, v_a_4845_);
v___x_4847_ = v___x_4842_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4845_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v_x_4834_);
v___x_4847_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
v_x_4833_ = v_tail_4840_;
v_x_4834_ = v___x_4847_;
goto _start;
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_del_object(v___x_4842_);
lean_dec(v_tail_4840_);
lean_dec(v_x_4834_);
v_a_4850_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4844_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4844_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4859_, lean_object* v_x_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4859_, v_x_4860_, v___y_4861_);
lean_dec_ref(v___y_4861_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4864_, lean_object* v_alts_4865_, uint8_t v_compress_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_seq_4871_; 
if (v_compress_4866_ == 0)
{
goto v___jp_4874_;
}
else
{
uint8_t v___x_4884_; 
v___x_4884_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4865_);
if (v___x_4884_ == 0)
{
goto v___jp_4874_;
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = lean_array_get_size(v_alts_4865_);
v___x_4887_ = lean_nat_dec_lt(v___x_4885_, v___x_4886_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_dec_ref(v_alts_4865_);
v___x_4888_ = lean_box(0);
v___x_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_cases_4864_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
else
{
lean_object* v___x_4891_; lean_object* v_firstAlt_4892_; uint8_t v___x_4893_; 
v___x_4891_ = lean_box(0);
v_firstAlt_4892_ = lean_array_get(v___x_4891_, v_alts_4865_, v___x_4885_);
lean_dec_ref(v_alts_4865_);
lean_inc(v_firstAlt_4892_);
v___x_4893_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4903_; 
v___x_4894_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4864_, v_firstAlt_4892_, v_a_4867_);
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4899_, 0, v_a_4895_);
lean_ctor_set(v___x_4899_, 1, v___x_4891_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
lean_object* v___x_4904_; 
lean_dec(v_cases_4864_);
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v_firstAlt_4892_);
return v___x_4904_;
}
}
}
}
v___jp_4870_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4872_, 0, v_cases_4864_);
lean_ctor_set(v___x_4872_, 1, v_seq_4871_);
v___x_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
return v___x_4873_;
}
v___jp_4874_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; uint8_t v___x_4877_; 
v___x_4875_ = lean_array_get_size(v_alts_4865_);
v___x_4876_ = lean_unsigned_to_nat(1u);
v___x_4877_ = lean_nat_dec_eq(v___x_4875_, v___x_4876_);
if (v___x_4877_ == 0)
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = lean_array_to_list(v_alts_4865_);
v___x_4879_ = lean_box(0);
v___x_4880_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4878_, v___x_4879_, v_a_4867_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref_known(v___x_4880_, 1);
v_seq_4871_ = v_a_4881_;
goto v___jp_4870_;
}
else
{
lean_dec(v_cases_4864_);
return v___x_4880_;
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = lean_unsigned_to_nat(0u);
v___x_4883_ = lean_array_fget(v_alts_4865_, v___x_4882_);
lean_dec_ref(v_alts_4865_);
v_seq_4871_ = v___x_4883_;
goto v___jp_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4905_, lean_object* v_alts_4906_, lean_object* v_compress_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
uint8_t v_compress_boxed_4911_; lean_object* v_res_4912_; 
v_compress_boxed_4911_ = lean_unbox(v_compress_4907_);
v_res_4912_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4905_, v_alts_4906_, v_compress_boxed_4911_, v_a_4908_, v_a_4909_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4913_, lean_object* v_x_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4913_, v_x_4914_, v___y_4915_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4919_, lean_object* v_x_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4919_, v_x_4920_, v___y_4921_, v___y_4922_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___x_4928_; lean_object* v_env_4929_; uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4928_ = lean_st_ref_get(v___y_4926_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc_ref(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4930_ = l_Lean_Meta_isMatcherAppCore(v_env_4929_, v_e_4925_);
v___x_4931_ = lean_box(v___x_4930_);
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4933_, v___y_4934_);
lean_dec(v___y_4934_);
lean_dec_ref(v_e_4933_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4937_, v___y_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v_e_4950_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; 
lean_inc(v___y_4968_);
lean_inc_ref(v___y_4967_);
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
lean_inc(v___y_4964_);
v___x_4974_ = lean_apply_10(v_x_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, lean_box(0));
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4987_, lean_object* v_x_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___f_4999_; lean_object* v___x_5000_; 
lean_inc(v___y_4993_);
lean_inc_ref(v___y_4992_);
lean_inc(v___y_4991_);
lean_inc_ref(v___y_4990_);
lean_inc(v___y_4989_);
v___f_4999_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_4999_, 0, v_x_4988_);
lean_closure_set(v___f_4999_, 1, v___y_4989_);
lean_closure_set(v___f_4999_, 2, v___y_4990_);
lean_closure_set(v___f_4999_, 3, v___y_4991_);
lean_closure_set(v___f_4999_, 4, v___y_4992_);
lean_closure_set(v___f_4999_, 5, v___y_4993_);
v___x_5000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4987_, v___f_4999_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5000_) == 0)
{
return v___x_5000_;
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_5000_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_5000_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5009_, lean_object* v_x_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5009_, v_x_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
lean_dec(v___y_5011_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5022_, lean_object* v_mvarId_5023_, lean_object* v_x_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5023_, v_x_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5036_, lean_object* v_mvarId_5037_, lean_object* v_x_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5036_, v_mvarId_5037_, v_x_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_e_5050_, lean_object* v___y_5051_){
_start:
{
uint8_t v___x_5053_; 
v___x_5053_ = l_Lean_Expr_hasMVar(v_e_5050_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v_e_5050_);
return v___x_5054_;
}
else
{
lean_object* v___x_5055_; lean_object* v_mctx_5056_; lean_object* v___x_5057_; lean_object* v_fst_5058_; lean_object* v_snd_5059_; lean_object* v___x_5060_; lean_object* v_cache_5061_; lean_object* v_zetaDeltaFVarIds_5062_; lean_object* v_postponed_5063_; lean_object* v_diag_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5073_; 
v___x_5055_ = lean_st_ref_get(v___y_5051_);
v_mctx_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc_ref(v_mctx_5056_);
lean_dec(v___x_5055_);
v___x_5057_ = l_Lean_instantiateMVarsCore(v_mctx_5056_, v_e_5050_);
v_fst_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_fst_5058_);
v_snd_5059_ = lean_ctor_get(v___x_5057_, 1);
lean_inc(v_snd_5059_);
lean_dec_ref(v___x_5057_);
v___x_5060_ = lean_st_ref_take(v___y_5051_);
v_cache_5061_ = lean_ctor_get(v___x_5060_, 1);
v_zetaDeltaFVarIds_5062_ = lean_ctor_get(v___x_5060_, 2);
v_postponed_5063_ = lean_ctor_get(v___x_5060_, 3);
v_diag_5064_ = lean_ctor_get(v___x_5060_, 4);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5073_ == 0)
{
lean_object* v_unused_5074_; 
v_unused_5074_ = lean_ctor_get(v___x_5060_, 0);
lean_dec(v_unused_5074_);
v___x_5066_ = v___x_5060_;
v_isShared_5067_ = v_isSharedCheck_5073_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_diag_5064_);
lean_inc(v_postponed_5063_);
lean_inc(v_zetaDeltaFVarIds_5062_);
lean_inc(v_cache_5061_);
lean_dec(v___x_5060_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5073_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v_snd_5059_);
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_snd_5059_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v_cache_5061_);
lean_ctor_set(v_reuseFailAlloc_5072_, 2, v_zetaDeltaFVarIds_5062_);
lean_ctor_set(v_reuseFailAlloc_5072_, 3, v_postponed_5063_);
lean_ctor_set(v_reuseFailAlloc_5072_, 4, v_diag_5064_);
v___x_5069_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = lean_st_ref_put(v___y_5051_, v___x_5069_);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v_fst_5058_);
return v___x_5071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object* v_e_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5075_, v___y_5076_);
lean_dec(v___y_5076_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_e_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_e_5079_, v___y_5086_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object* v_e_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_e_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
lean_dec(v___y_5092_);
return v_res_5102_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5105_ = l_Lean_stringToMessageData(v___x_5104_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5106_, lean_object* v_c_5107_, lean_object* v_a_5108_, lean_object* v_numCases_5109_, uint8_t v_isRec_5110_, lean_object* v_anchorInfo_x3f_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_mvarIds_5124_; lean_object* v___x_5174_; 
v___x_5174_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5106_, v___y_5112_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___y_5177_; lean_object* v___x_5229_; uint8_t v___x_5232_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5174_, 1);
v___x_5229_ = lean_unsigned_to_nat(1u);
v___x_5232_ = lean_nat_dec_lt(v___x_5229_, v_numCases_5109_);
if (v___x_5232_ == 0)
{
if (v_isRec_5110_ == 0)
{
lean_inc(v_a_5175_);
v___y_5177_ = v_a_5175_;
goto v___jp_5176_;
}
else
{
goto v___jp_5230_;
}
}
else
{
goto v___jp_5230_;
}
v___jp_5176_:
{
lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5178_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5107_);
lean_inc_ref(v___x_5106_);
v___x_5179_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5106_, v___y_5177_, v_numCases_5109_, v___x_5178_, v___y_5115_, v___y_5118_, v___y_5120_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v___x_5180_; 
lean_dec_ref_known(v___x_5179_, 1);
lean_inc_ref(v___x_5106_);
v___x_5180_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5106_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_toCold_5181_; lean_object* v_options_5182_; uint8_t v_hasTrace_5183_; 
lean_dec_ref_known(v___x_5180_, 1);
v_toCold_5181_ = lean_ctor_get(v___y_5120_, 0);
v_options_5182_ = lean_ctor_get(v_toCold_5181_, 2);
v_hasTrace_5183_ = lean_ctor_get_uint8(v_options_5182_, sizeof(void*)*1);
if (v_hasTrace_5183_ == 0)
{
lean_dec(v_a_5175_);
goto v___jp_5127_;
}
else
{
lean_object* v_inheritedTraceOptions_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; uint8_t v___x_5187_; 
v_inheritedTraceOptions_5184_ = lean_ctor_get(v_toCold_5181_, 11);
v___x_5185_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5186_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5187_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5184_, v_options_5182_, v___x_5186_);
if (v___x_5187_ == 0)
{
lean_dec(v_a_5175_);
goto v___jp_5127_;
}
else
{
lean_object* v___x_5188_; 
v___x_5188_ = l_Lean_Meta_Grind_updateLastTag(v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
lean_dec_ref_known(v___x_5188_, 1);
lean_inc_ref(v___x_5106_);
v___x_5189_ = l_Lean_MessageData_ofExpr(v___x_5106_);
v___x_5190_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5189_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = l_Nat_reprFast(v_a_5175_);
v___x_5193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5192_);
v___x_5194_ = l_Lean_MessageData_ofFormat(v___x_5193_);
v___x_5195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5191_);
lean_ctor_set(v___x_5195_, 1, v___x_5194_);
v___x_5196_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5185_, v___x_5195_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_dec_ref_known(v___x_5196_, 1);
goto v___jp_5127_;
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_a_5108_);
lean_dec_ref(v_c_5107_);
lean_dec_ref(v___x_5106_);
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5196_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5196_);
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
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_dec(v_a_5175_);
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_a_5108_);
lean_dec_ref(v_c_5107_);
lean_dec_ref(v___x_5106_);
v_a_5205_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5188_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5188_);
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
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_dec(v_a_5175_);
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_a_5108_);
lean_dec_ref(v_c_5107_);
lean_dec_ref(v___x_5106_);
v_a_5213_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5180_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5180_);
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
lean_dec(v_a_5175_);
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_a_5108_);
lean_dec_ref(v_c_5107_);
lean_dec_ref(v___x_5106_);
v_a_5221_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5179_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5179_);
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
v___jp_5230_:
{
lean_object* v___x_5231_; 
v___x_5231_ = lean_nat_add(v_a_5175_, v___x_5229_);
v___y_5177_ = v___x_5231_;
goto v___jp_5176_;
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_numCases_5109_);
lean_dec(v_a_5108_);
lean_dec_ref(v_c_5107_);
lean_dec_ref(v___x_5106_);
v_a_5233_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5174_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5174_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
v___jp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5125_, 0, v_mvarIds_5124_);
lean_ctor_set(v___x_5125_, 1, v_anchorInfo_x3f_5111_);
v___x_5126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5126_, 0, v___x_5125_);
return v___x_5126_;
}
v___jp_5127_:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5106_, v___y_5121_);
if (lean_obj_tag(v_c_5107_) == 1)
{
lean_object* v_e_5129_; lean_object* v_binderType_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; 
lean_dec_ref(v___x_5128_);
lean_dec_ref(v___x_5106_);
v_e_5129_ = lean_ctor_get(v_c_5107_, 0);
lean_inc_ref(v_e_5129_);
lean_dec_ref_known(v_c_5107_, 2);
v_binderType_5130_ = lean_ctor_get(v_e_5129_, 1);
lean_inc_ref(v_binderType_5130_);
lean_dec_ref(v_e_5129_);
v___x_5131_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5130_);
v___x_5132_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5108_, v___x_5131_, v___y_5114_, v___y_5115_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v_mvarIds_5124_ = v_a_5133_;
goto v___jp_5123_;
}
else
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
lean_dec(v_anchorInfo_x3f_5111_);
v_a_5134_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5132_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5132_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
else
{
lean_object* v_a_5142_; uint8_t v___x_5143_; 
lean_dec_ref(v_c_5107_);
v_a_5142_ = lean_ctor_get(v___x_5128_, 0);
lean_inc(v_a_5142_);
lean_dec_ref(v___x_5128_);
v___x_5143_ = lean_unbox(v_a_5142_);
lean_dec(v_a_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5106_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5108_, v_a_5145_, v___y_5114_, v___y_5115_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v_mvarIds_5124_ = v_a_5147_;
goto v___jp_5123_;
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_dec(v_anchorInfo_x3f_5111_);
v_a_5148_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5146_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5146_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec(v_anchorInfo_x3f_5111_);
lean_dec(v_a_5108_);
v_a_5156_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5144_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5144_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v___x_5164_; 
v___x_5164_ = l_Lean_Meta_Grind_casesMatch(v_a_5108_, v___x_5106_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc(v_a_5165_);
lean_dec_ref_known(v___x_5164_, 1);
v_mvarIds_5124_ = v_a_5165_;
goto v___jp_5123_;
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5173_; 
lean_dec(v_anchorInfo_x3f_5111_);
v_a_5166_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5168_ = v___x_5164_;
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5164_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5241_ = _args[0];
lean_object* v_c_5242_ = _args[1];
lean_object* v_a_5243_ = _args[2];
lean_object* v_numCases_5244_ = _args[3];
lean_object* v_isRec_5245_ = _args[4];
lean_object* v_anchorInfo_x3f_5246_ = _args[5];
lean_object* v___y_5247_ = _args[6];
lean_object* v___y_5248_ = _args[7];
lean_object* v___y_5249_ = _args[8];
lean_object* v___y_5250_ = _args[9];
lean_object* v___y_5251_ = _args[10];
lean_object* v___y_5252_ = _args[11];
lean_object* v___y_5253_ = _args[12];
lean_object* v___y_5254_ = _args[13];
lean_object* v___y_5255_ = _args[14];
lean_object* v___y_5256_ = _args[15];
lean_object* v___y_5257_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5258_; lean_object* v_res_5259_; 
v_isRec_boxed_5258_ = lean_unbox(v_isRec_5245_);
v_res_5259_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5241_, v_c_5242_, v_a_5243_, v_numCases_5244_, v_isRec_boxed_5258_, v_anchorInfo_x3f_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec(v___y_5247_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5260_, uint8_t v_trace_5261_, lean_object* v___f_5262_, lean_object* v_c_5263_, lean_object* v_candidates_x3f_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v___x_5275_; lean_object* v___y_5277_; 
v___x_5275_ = lean_st_mk_ref(v_goal_5260_);
if (v_trace_5261_ == 0)
{
lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec(v_candidates_x3f_5264_);
v___x_5296_ = lean_box(0);
lean_inc(v___x_5275_);
v___x_5297_ = lean_apply_12(v___f_5262_, v___x_5296_, v___x_5275_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, lean_box(0));
v___y_5277_ = v___x_5297_;
goto v___jp_5276_;
}
else
{
lean_object* v___x_5298_; 
v___x_5298_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5263_, v_candidates_x3f_5264_, v___x_5275_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
if (lean_obj_tag(v___x_5298_) == 0)
{
lean_object* v_a_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref_known(v___x_5298_, 1);
v___x_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5300_, 0, v_a_5299_);
lean_inc(v___x_5275_);
v___x_5301_ = lean_apply_12(v___f_5262_, v___x_5300_, v___x_5275_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, lean_box(0));
v___y_5277_ = v___x_5301_;
goto v___jp_5276_;
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec(v___x_5275_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___f_5262_);
v_a_5302_ = lean_ctor_get(v___x_5298_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5298_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5298_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5298_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
v___jp_5276_:
{
if (lean_obj_tag(v___y_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5287_; 
v_a_5278_ = lean_ctor_get(v___y_5277_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___y_5277_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5280_ = v___y_5277_;
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___y_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5287_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5285_; 
v___x_5282_ = lean_st_ref_get(v___x_5275_);
lean_dec(v___x_5275_);
v___x_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5283_, 0, v_a_5278_);
lean_ctor_set(v___x_5283_, 1, v___x_5282_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5283_);
v___x_5285_ = v___x_5280_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_dec(v___x_5275_);
v_a_5288_ = lean_ctor_get(v___y_5277_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___y_5277_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___y_5277_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___y_5277_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5310_, lean_object* v_trace_5311_, lean_object* v___f_5312_, lean_object* v_c_5313_, lean_object* v_candidates_x3f_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
uint8_t v_trace_boxed_5325_; lean_object* v_res_5326_; 
v_trace_boxed_5325_ = lean_unbox(v_trace_5311_);
v_res_5326_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5310_, v_trace_boxed_5325_, v___f_5312_, v_c_5313_, v_candidates_x3f_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec_ref(v_c_5313_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_x_5327_, lean_object* v_x_5328_, lean_object* v_x_5329_, lean_object* v_x_5330_){
_start:
{
lean_object* v_ks_5331_; lean_object* v_vs_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5356_; 
v_ks_5331_ = lean_ctor_get(v_x_5327_, 0);
v_vs_5332_ = lean_ctor_get(v_x_5327_, 1);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_x_5327_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5334_ = v_x_5327_;
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_vs_5332_);
lean_inc(v_ks_5331_);
lean_dec(v_x_5327_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5336_; uint8_t v___x_5337_; 
v___x_5336_ = lean_array_get_size(v_ks_5331_);
v___x_5337_ = lean_nat_dec_lt(v_x_5328_, v___x_5336_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
lean_dec(v_x_5328_);
v___x_5338_ = lean_array_push(v_ks_5331_, v_x_5329_);
v___x_5339_ = lean_array_push(v_vs_5332_, v_x_5330_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 1, v___x_5339_);
lean_ctor_set(v___x_5334_, 0, v___x_5338_);
v___x_5341_ = v___x_5334_;
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
else
{
lean_object* v_k_x27_5343_; uint8_t v___x_5344_; 
v_k_x27_5343_ = lean_array_fget_borrowed(v_ks_5331_, v_x_5328_);
v___x_5344_ = l_Lean_instBEqMVarId_beq(v_x_5329_, v_k_x27_5343_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5346_; 
if (v_isShared_5335_ == 0)
{
v___x_5346_ = v___x_5334_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_ks_5331_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v_vs_5332_);
v___x_5346_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = lean_unsigned_to_nat(1u);
v___x_5348_ = lean_nat_add(v_x_5328_, v___x_5347_);
lean_dec(v_x_5328_);
v_x_5327_ = v___x_5346_;
v_x_5328_ = v___x_5348_;
goto _start;
}
}
else
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5354_; 
v___x_5351_ = lean_array_fset(v_ks_5331_, v_x_5328_, v_x_5329_);
v___x_5352_ = lean_array_fset(v_vs_5332_, v_x_5328_, v_x_5330_);
lean_dec(v_x_5328_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 1, v___x_5352_);
lean_ctor_set(v___x_5334_, 0, v___x_5351_);
v___x_5354_ = v___x_5334_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v___x_5352_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(lean_object* v_n_5357_, lean_object* v_k_5358_, lean_object* v_v_5359_){
_start:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; 
v___x_5360_ = lean_unsigned_to_nat(0u);
v___x_5361_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_n_5357_, v___x_5360_, v_k_5358_, v_v_5359_);
return v___x_5361_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(lean_object* v_x_5363_, size_t v_x_5364_, size_t v_x_5365_, lean_object* v_x_5366_, lean_object* v_x_5367_){
_start:
{
if (lean_obj_tag(v_x_5363_) == 0)
{
lean_object* v_es_5368_; size_t v___x_5369_; size_t v___x_5370_; lean_object* v_j_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; 
v_es_5368_ = lean_ctor_get(v_x_5363_, 0);
v___x_5369_ = ((size_t)31ULL);
v___x_5370_ = lean_usize_land(v_x_5364_, v___x_5369_);
v_j_5371_ = lean_usize_to_nat(v___x_5370_);
v___x_5372_ = lean_array_get_size(v_es_5368_);
v___x_5373_ = lean_nat_dec_lt(v_j_5371_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_dec(v_j_5371_);
lean_dec(v_x_5367_);
lean_dec(v_x_5366_);
return v_x_5363_;
}
else
{
lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5412_; 
lean_inc_ref(v_es_5368_);
v_isSharedCheck_5412_ = !lean_is_exclusive(v_x_5363_);
if (v_isSharedCheck_5412_ == 0)
{
lean_object* v_unused_5413_; 
v_unused_5413_ = lean_ctor_get(v_x_5363_, 0);
lean_dec(v_unused_5413_);
v___x_5375_ = v_x_5363_;
v_isShared_5376_ = v_isSharedCheck_5412_;
goto v_resetjp_5374_;
}
else
{
lean_dec(v_x_5363_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5412_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v_v_5377_; lean_object* v___x_5378_; lean_object* v_xs_x27_5379_; lean_object* v___y_5381_; 
v_v_5377_ = lean_array_fget(v_es_5368_, v_j_5371_);
v___x_5378_ = lean_box(0);
v_xs_x27_5379_ = lean_array_fset(v_es_5368_, v_j_5371_, v___x_5378_);
switch(lean_obj_tag(v_v_5377_))
{
case 0:
{
lean_object* v_key_5386_; lean_object* v_val_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5397_; 
v_key_5386_ = lean_ctor_get(v_v_5377_, 0);
v_val_5387_ = lean_ctor_get(v_v_5377_, 1);
v_isSharedCheck_5397_ = !lean_is_exclusive(v_v_5377_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5389_ = v_v_5377_;
v_isShared_5390_ = v_isSharedCheck_5397_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_val_5387_);
lean_inc(v_key_5386_);
lean_dec(v_v_5377_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5397_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
uint8_t v___x_5391_; 
v___x_5391_ = l_Lean_instBEqMVarId_beq(v_x_5366_, v_key_5386_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
lean_del_object(v___x_5389_);
v___x_5392_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5386_, v_val_5387_, v_x_5366_, v_x_5367_);
v___x_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___y_5381_ = v___x_5393_;
goto v___jp_5380_;
}
else
{
lean_object* v___x_5395_; 
lean_dec(v_val_5387_);
lean_dec(v_key_5386_);
if (v_isShared_5390_ == 0)
{
lean_ctor_set(v___x_5389_, 1, v_x_5367_);
lean_ctor_set(v___x_5389_, 0, v_x_5366_);
v___x_5395_ = v___x_5389_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_x_5366_);
lean_ctor_set(v_reuseFailAlloc_5396_, 1, v_x_5367_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
v___y_5381_ = v___x_5395_;
goto v___jp_5380_;
}
}
}
}
case 1:
{
lean_object* v_node_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5410_; 
v_node_5398_ = lean_ctor_get(v_v_5377_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v_v_5377_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5400_ = v_v_5377_;
v_isShared_5401_ = v_isSharedCheck_5410_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_node_5398_);
lean_dec(v_v_5377_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5410_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
size_t v___x_5402_; size_t v___x_5403_; size_t v___x_5404_; size_t v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5408_; 
v___x_5402_ = ((size_t)5ULL);
v___x_5403_ = lean_usize_shift_right(v_x_5364_, v___x_5402_);
v___x_5404_ = ((size_t)1ULL);
v___x_5405_ = lean_usize_add(v_x_5365_, v___x_5404_);
v___x_5406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_node_5398_, v___x_5403_, v___x_5405_, v_x_5366_, v_x_5367_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5406_);
v___x_5408_ = v___x_5400_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v___x_5406_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
v___y_5381_ = v___x_5408_;
goto v___jp_5380_;
}
}
}
default: 
{
lean_object* v___x_5411_; 
v___x_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5411_, 0, v_x_5366_);
lean_ctor_set(v___x_5411_, 1, v_x_5367_);
v___y_5381_ = v___x_5411_;
goto v___jp_5380_;
}
}
v___jp_5380_:
{
lean_object* v___x_5382_; lean_object* v___x_5384_; 
v___x_5382_ = lean_array_fset(v_xs_x27_5379_, v_j_5371_, v___y_5381_);
lean_dec(v_j_5371_);
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v___x_5382_);
v___x_5384_ = v___x_5375_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5382_);
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
else
{
lean_object* v_ks_5414_; lean_object* v_vs_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5433_; 
v_ks_5414_ = lean_ctor_get(v_x_5363_, 0);
v_vs_5415_ = lean_ctor_get(v_x_5363_, 1);
v_isSharedCheck_5433_ = !lean_is_exclusive(v_x_5363_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5417_ = v_x_5363_;
v_isShared_5418_ = v_isSharedCheck_5433_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_vs_5415_);
lean_inc(v_ks_5414_);
lean_dec(v_x_5363_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5433_;
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
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_ks_5414_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_vs_5415_);
v___x_5420_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
lean_object* v_newNode_5421_; size_t v___x_5422_; uint8_t v___x_5423_; 
v_newNode_5421_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v___x_5420_, v_x_5366_, v_x_5367_);
v___x_5422_ = ((size_t)7ULL);
v___x_5423_ = lean_usize_dec_le(v___x_5422_, v_x_5365_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; lean_object* v___x_5425_; uint8_t v___x_5426_; 
v___x_5424_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5421_);
v___x_5425_ = lean_unsigned_to_nat(4u);
v___x_5426_ = lean_nat_dec_lt(v___x_5424_, v___x_5425_);
lean_dec(v___x_5424_);
if (v___x_5426_ == 0)
{
lean_object* v_ks_5427_; lean_object* v_vs_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v_ks_5427_ = lean_ctor_get(v_newNode_5421_, 0);
lean_inc_ref(v_ks_5427_);
v_vs_5428_ = lean_ctor_get(v_newNode_5421_, 1);
lean_inc_ref(v_vs_5428_);
lean_dec_ref(v_newNode_5421_);
v___x_5429_ = lean_unsigned_to_nat(0u);
v___x_5430_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg___closed__0);
v___x_5431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_x_5365_, v_ks_5427_, v_vs_5428_, v___x_5429_, v___x_5430_);
lean_dec_ref(v_vs_5428_);
lean_dec_ref(v_ks_5427_);
return v___x_5431_;
}
else
{
return v_newNode_5421_;
}
}
else
{
return v_newNode_5421_;
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
size_t v_x_66986__boxed_5466_; size_t v_x_66987__boxed_5467_; lean_object* v_res_5468_; 
v_x_66986__boxed_5466_ = lean_unbox_usize(v_x_5462_);
lean_dec(v_x_5462_);
v_x_66987__boxed_5467_ = lean_unbox_usize(v_x_5463_);
lean_dec(v_x_5463_);
v_res_5468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_5461_, v_x_66986__boxed_5466_, v_x_66987__boxed_5467_, v_x_5464_, v_x_5465_);
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
lean_object* v___x_5480_; lean_object* v_mctx_5481_; lean_object* v_cache_5482_; lean_object* v_zetaDeltaFVarIds_5483_; lean_object* v_postponed_5484_; lean_object* v_diag_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5515_; 
v___x_5480_ = lean_st_ref_take(v___y_5478_);
v_mctx_5481_ = lean_ctor_get(v___x_5480_, 0);
v_cache_5482_ = lean_ctor_get(v___x_5480_, 1);
v_zetaDeltaFVarIds_5483_ = lean_ctor_get(v___x_5480_, 2);
v_postponed_5484_ = lean_ctor_get(v___x_5480_, 3);
v_diag_5485_ = lean_ctor_get(v___x_5480_, 4);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5487_ = v___x_5480_;
v_isShared_5488_ = v_isSharedCheck_5515_;
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
v_isShared_5488_ = v_isSharedCheck_5515_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v_depth_5489_; lean_object* v_levelAssignDepth_5490_; lean_object* v_lmvarCounter_5491_; lean_object* v_mvarCounter_5492_; lean_object* v_lDecls_5493_; lean_object* v_decls_5494_; lean_object* v_userNames_5495_; lean_object* v_lAssignment_5496_; lean_object* v_eAssignment_5497_; lean_object* v_dAssignment_5498_; lean_object* v_instanceTypedMVars_5499_; lean_object* v_synthNormMemo_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5514_; 
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
v_instanceTypedMVars_5499_ = lean_ctor_get(v_mctx_5481_, 10);
v_synthNormMemo_5500_ = lean_ctor_get(v_mctx_5481_, 11);
v_isSharedCheck_5514_ = !lean_is_exclusive(v_mctx_5481_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5502_ = v_mctx_5481_;
v_isShared_5503_ = v_isSharedCheck_5514_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_synthNormMemo_5500_);
lean_inc(v_instanceTypedMVars_5499_);
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
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5514_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
v___x_5504_ = lean_box(0);
v___x_5505_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_eAssignment_5497_, v_mvarId_5476_, v_val_5477_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 8, v___x_5505_);
v___x_5507_ = v___x_5502_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_depth_5489_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_levelAssignDepth_5490_);
lean_ctor_set(v_reuseFailAlloc_5513_, 2, v_lmvarCounter_5491_);
lean_ctor_set(v_reuseFailAlloc_5513_, 3, v_mvarCounter_5492_);
lean_ctor_set(v_reuseFailAlloc_5513_, 4, v_lDecls_5493_);
lean_ctor_set(v_reuseFailAlloc_5513_, 5, v_decls_5494_);
lean_ctor_set(v_reuseFailAlloc_5513_, 6, v_userNames_5495_);
lean_ctor_set(v_reuseFailAlloc_5513_, 7, v_lAssignment_5496_);
lean_ctor_set(v_reuseFailAlloc_5513_, 8, v___x_5505_);
lean_ctor_set(v_reuseFailAlloc_5513_, 9, v_dAssignment_5498_);
lean_ctor_set(v_reuseFailAlloc_5513_, 10, v_instanceTypedMVars_5499_);
lean_ctor_set(v_reuseFailAlloc_5513_, 11, v_synthNormMemo_5500_);
v___x_5507_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v___x_5507_);
v___x_5509_ = v___x_5487_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v_cache_5482_);
lean_ctor_set(v_reuseFailAlloc_5512_, 2, v_zetaDeltaFVarIds_5483_);
lean_ctor_set(v_reuseFailAlloc_5512_, 3, v_postponed_5484_);
lean_ctor_set(v_reuseFailAlloc_5512_, 4, v_diag_5485_);
v___x_5509_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = lean_st_ref_put(v___y_5478_, v___x_5509_);
v___x_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5504_);
return v___x_5511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_mvarId_5516_, lean_object* v_val_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_){
_start:
{
lean_object* v_res_5520_; 
v_res_5520_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5516_, v_val_5517_, v___y_5518_);
lean_dec(v___y_5518_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(lean_object* v_kp_5521_, lean_object* v_snd_5522_, uint8_t v_stopAtFirstFailure_5523_, lean_object* v_as_x27_5524_, lean_object* v_b_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
if (lean_obj_tag(v_as_x27_5524_) == 0)
{
lean_object* v___x_5536_; 
lean_dec_ref(v_snd_5522_);
lean_dec_ref(v_kp_5521_);
v___x_5536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_b_5525_);
return v___x_5536_;
}
else
{
lean_object* v_snd_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5643_; 
v_snd_5537_ = lean_ctor_get(v_b_5525_, 1);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_b_5525_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; 
v_unused_5644_ = lean_ctor_get(v_b_5525_, 0);
lean_dec(v_unused_5644_);
v___x_5539_ = v_b_5525_;
v_isShared_5540_ = v_isSharedCheck_5643_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_snd_5537_);
lean_dec(v_b_5525_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5643_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v_head_5541_; lean_object* v_tail_5542_; lean_object* v_fst_5543_; lean_object* v_snd_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5642_; 
v_head_5541_ = lean_ctor_get(v_as_x27_5524_, 0);
v_tail_5542_ = lean_ctor_get(v_as_x27_5524_, 1);
v_fst_5543_ = lean_ctor_get(v_snd_5537_, 0);
v_snd_5544_ = lean_ctor_get(v_snd_5537_, 1);
v_isSharedCheck_5642_ = !lean_is_exclusive(v_snd_5537_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5546_ = v_snd_5537_;
v_isShared_5547_ = v_isSharedCheck_5642_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_snd_5544_);
lean_inc(v_fst_5543_);
lean_dec(v_snd_5537_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5642_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5548_ = lean_box(0);
lean_inc_ref(v_kp_5521_);
lean_inc(v___y_5534_);
lean_inc_ref(v___y_5533_);
lean_inc(v___y_5532_);
lean_inc_ref(v___y_5531_);
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc(v___y_5528_);
lean_inc_ref(v___y_5527_);
lean_inc(v___y_5526_);
lean_inc(v_head_5541_);
v___x_5549_ = lean_apply_11(v_kp_5521_, v_head_5541_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, lean_box(0));
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5633_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5552_ = v___x_5549_;
v_isShared_5553_ = v_isSharedCheck_5633_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5549_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5633_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
if (lean_obj_tag(v_a_5550_) == 0)
{
lean_object* v_seq_5554_; lean_object* v_mvarId_5555_; lean_object* v___x_5556_; 
lean_del_object(v___x_5552_);
v_seq_5554_ = lean_ctor_get(v_a_5550_, 0);
v_mvarId_5555_ = lean_ctor_get(v_head_5541_, 1);
lean_inc(v_mvarId_5555_);
v___x_5556_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5555_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
if (lean_obj_tag(v___x_5556_) == 0)
{
lean_object* v_a_5557_; 
v_a_5557_ = lean_ctor_get(v___x_5556_, 0);
lean_inc(v_a_5557_);
lean_dec_ref_known(v___x_5556_, 1);
if (lean_obj_tag(v_a_5557_) == 1)
{
lean_object* v_val_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5589_; 
lean_dec_ref(v_kp_5521_);
v_val_5558_ = lean_ctor_get(v_a_5557_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_a_5557_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5560_ = v_a_5557_;
v_isShared_5561_ = v_isSharedCheck_5589_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_val_5558_);
lean_dec(v_a_5557_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5589_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v_mvarId_5562_; lean_object* v___x_5563_; 
v_mvarId_5562_ = lean_ctor_get(v_snd_5522_, 1);
lean_inc(v_mvarId_5562_);
lean_dec_ref(v_snd_5522_);
v___x_5563_ = l_Lean_MVarId_assignFalseProof(v_mvarId_5562_, v_val_5558_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5579_; 
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; 
v_unused_5580_ = lean_ctor_get(v___x_5563_, 0);
lean_dec(v_unused_5580_);
v___x_5565_ = v___x_5563_;
v_isShared_5566_ = v_isSharedCheck_5579_;
goto v_resetjp_5564_;
}
else
{
lean_dec(v___x_5563_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5579_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5568_; 
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 0, v_a_5550_);
v___x_5568_ = v___x_5560_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5550_);
v___x_5568_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5547_ == 0)
{
v___x_5570_ = v___x_5546_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_fst_5543_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v_snd_5544_);
v___x_5570_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5572_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v___x_5570_);
lean_ctor_set(v___x_5539_, 0, v___x_5568_);
v___x_5572_ = v___x_5539_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
lean_object* v___x_5574_; 
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 0, v___x_5572_);
v___x_5574_ = v___x_5565_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v___x_5572_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
lean_del_object(v___x_5560_);
lean_dec_ref_known(v_a_5550_, 1);
lean_del_object(v___x_5546_);
lean_dec(v_snd_5544_);
lean_dec(v_fst_5543_);
lean_del_object(v___x_5539_);
v_a_5581_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5563_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5563_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
}
}
else
{
uint8_t v___x_5590_; 
lean_inc(v_seq_5554_);
lean_dec(v_a_5557_);
lean_dec_ref_known(v_a_5550_, 1);
v___x_5590_ = l_List_isEmpty___redArg(v_seq_5554_);
if (v___x_5590_ == 0)
{
lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5591_ = lean_array_push(v_fst_5543_, v_seq_5554_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5591_);
v___x_5593_ = v___x_5546_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5598_, 1, v_snd_5544_);
v___x_5593_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
lean_object* v___x_5595_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v___x_5593_);
lean_ctor_set(v___x_5539_, 0, v___x_5548_);
v___x_5595_ = v___x_5539_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
v_as_x27_5524_ = v_tail_5542_;
v_b_5525_ = v___x_5595_;
goto _start;
}
}
}
else
{
lean_object* v___x_5600_; 
lean_dec(v_seq_5554_);
if (v_isShared_5547_ == 0)
{
v___x_5600_ = v___x_5546_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_fst_5543_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_snd_5544_);
v___x_5600_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5602_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v___x_5600_);
lean_ctor_set(v___x_5539_, 0, v___x_5548_);
v___x_5602_ = v___x_5539_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
v_as_x27_5524_ = v_tail_5542_;
v_b_5525_ = v___x_5602_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
lean_dec_ref_known(v_a_5550_, 1);
lean_del_object(v___x_5546_);
lean_dec(v_snd_5544_);
lean_dec(v_fst_5543_);
lean_del_object(v___x_5539_);
lean_dec_ref(v_snd_5522_);
lean_dec_ref(v_kp_5521_);
v_a_5606_ = lean_ctor_get(v___x_5556_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5556_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5556_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5556_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5523_ == 0)
{
lean_object* v_gs_5614_; lean_object* v___x_5615_; lean_object* v___x_5617_; 
lean_del_object(v___x_5552_);
v_gs_5614_ = lean_ctor_get(v_a_5550_, 0);
lean_inc(v_gs_5614_);
lean_dec_ref_known(v_a_5550_, 1);
v___x_5615_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5544_, v_gs_5614_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 1, v___x_5615_);
v___x_5617_ = v___x_5546_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_fst_5543_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
lean_object* v___x_5619_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v___x_5617_);
lean_ctor_set(v___x_5539_, 0, v___x_5548_);
v___x_5619_ = v___x_5539_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v___x_5617_);
v___x_5619_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
v_as_x27_5524_ = v_tail_5542_;
v_b_5525_ = v___x_5619_;
goto _start;
}
}
}
else
{
lean_object* v___x_5623_; lean_object* v___x_5625_; 
lean_dec_ref(v_snd_5522_);
lean_dec_ref(v_kp_5521_);
v___x_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5623_, 0, v_a_5550_);
if (v_isShared_5547_ == 0)
{
v___x_5625_ = v___x_5546_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_fst_5543_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_snd_5544_);
v___x_5625_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5627_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 1, v___x_5625_);
lean_ctor_set(v___x_5539_, 0, v___x_5623_);
v___x_5627_ = v___x_5539_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v___x_5625_);
v___x_5627_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
lean_object* v___x_5629_; 
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 0, v___x_5627_);
v___x_5629_ = v___x_5552_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
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
}
}
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
lean_del_object(v___x_5546_);
lean_dec(v_snd_5544_);
lean_dec(v_fst_5543_);
lean_del_object(v___x_5539_);
lean_dec_ref(v_snd_5522_);
lean_dec_ref(v_kp_5521_);
v_a_5634_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5636_ = v___x_5549_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5549_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg___boxed(lean_object* v_kp_5645_, lean_object* v_snd_5646_, lean_object* v_stopAtFirstFailure_5647_, lean_object* v_as_x27_5648_, lean_object* v_b_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5660_; lean_object* v_res_5661_; 
v_stopAtFirstFailure_boxed_5660_ = lean_unbox(v_stopAtFirstFailure_5647_);
v_res_5661_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5645_, v_snd_5646_, v_stopAtFirstFailure_boxed_5660_, v_as_x27_5648_, v_b_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec(v_as_x27_5648_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v_snd_5662_, lean_object* v_c_5663_, lean_object* v___x_5664_, lean_object* v___x_5665_, uint8_t v_isRec_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
if (lean_obj_tag(v_a_5667_) == 0)
{
lean_object* v___x_5669_; 
lean_dec(v___x_5665_);
lean_dec_ref(v___x_5664_);
lean_dec_ref(v_snd_5662_);
v___x_5669_ = lean_array_to_list(v_a_5668_);
return v___x_5669_;
}
else
{
lean_object* v_toGoalState_5670_; lean_object* v_split_5671_; lean_object* v_head_5672_; lean_object* v_tail_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5734_; 
v_toGoalState_5670_ = lean_ctor_get(v_snd_5662_, 0);
lean_inc_ref(v_toGoalState_5670_);
v_split_5671_ = lean_ctor_get(v_toGoalState_5670_, 15);
lean_inc_ref(v_split_5671_);
v_head_5672_ = lean_ctor_get(v_a_5667_, 0);
v_tail_5673_ = lean_ctor_get(v_a_5667_, 1);
v_isSharedCheck_5734_ = !lean_is_exclusive(v_a_5667_);
if (v_isSharedCheck_5734_ == 0)
{
v___x_5675_ = v_a_5667_;
v_isShared_5676_ = v_isSharedCheck_5734_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_tail_5673_);
lean_inc(v_head_5672_);
lean_dec(v_a_5667_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5734_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v_nextDeclIdx_5677_; lean_object* v_enodeMap_5678_; lean_object* v_exprs_5679_; lean_object* v_parents_5680_; lean_object* v_congrTable_5681_; lean_object* v_appMap_5682_; lean_object* v_indicesFound_5683_; lean_object* v_toProcess_5684_; lean_object* v_internalizing_5685_; uint8_t v_inconsistent_5686_; lean_object* v_nextIdx_5687_; lean_object* v_newRawFacts_5688_; lean_object* v_facts_5689_; lean_object* v_extThms_5690_; lean_object* v_ematch_5691_; lean_object* v_inj_5692_; lean_object* v_clean_5693_; lean_object* v_sstates_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5732_; 
v_nextDeclIdx_5677_ = lean_ctor_get(v_toGoalState_5670_, 0);
v_enodeMap_5678_ = lean_ctor_get(v_toGoalState_5670_, 1);
v_exprs_5679_ = lean_ctor_get(v_toGoalState_5670_, 2);
v_parents_5680_ = lean_ctor_get(v_toGoalState_5670_, 3);
v_congrTable_5681_ = lean_ctor_get(v_toGoalState_5670_, 4);
v_appMap_5682_ = lean_ctor_get(v_toGoalState_5670_, 5);
v_indicesFound_5683_ = lean_ctor_get(v_toGoalState_5670_, 6);
v_toProcess_5684_ = lean_ctor_get(v_toGoalState_5670_, 7);
v_internalizing_5685_ = lean_ctor_get(v_toGoalState_5670_, 8);
v_inconsistent_5686_ = lean_ctor_get_uint8(v_toGoalState_5670_, sizeof(void*)*18);
v_nextIdx_5687_ = lean_ctor_get(v_toGoalState_5670_, 9);
v_newRawFacts_5688_ = lean_ctor_get(v_toGoalState_5670_, 10);
v_facts_5689_ = lean_ctor_get(v_toGoalState_5670_, 11);
v_extThms_5690_ = lean_ctor_get(v_toGoalState_5670_, 12);
v_ematch_5691_ = lean_ctor_get(v_toGoalState_5670_, 13);
v_inj_5692_ = lean_ctor_get(v_toGoalState_5670_, 14);
v_clean_5693_ = lean_ctor_get(v_toGoalState_5670_, 16);
v_sstates_5694_ = lean_ctor_get(v_toGoalState_5670_, 17);
v_isSharedCheck_5732_ = !lean_is_exclusive(v_toGoalState_5670_);
if (v_isSharedCheck_5732_ == 0)
{
lean_object* v_unused_5733_; 
v_unused_5733_ = lean_ctor_get(v_toGoalState_5670_, 15);
lean_dec(v_unused_5733_);
v___x_5696_ = v_toGoalState_5670_;
v_isShared_5697_ = v_isSharedCheck_5732_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_sstates_5694_);
lean_inc(v_clean_5693_);
lean_inc(v_inj_5692_);
lean_inc(v_ematch_5691_);
lean_inc(v_extThms_5690_);
lean_inc(v_facts_5689_);
lean_inc(v_newRawFacts_5688_);
lean_inc(v_nextIdx_5687_);
lean_inc(v_internalizing_5685_);
lean_inc(v_toProcess_5684_);
lean_inc(v_indicesFound_5683_);
lean_inc(v_appMap_5682_);
lean_inc(v_congrTable_5681_);
lean_inc(v_parents_5680_);
lean_inc(v_exprs_5679_);
lean_inc(v_enodeMap_5678_);
lean_inc(v_nextDeclIdx_5677_);
lean_dec(v_toGoalState_5670_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5732_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v_num_5698_; lean_object* v_candidates_5699_; lean_object* v_added_5700_; lean_object* v_resolved_5701_; lean_object* v_trace_5702_; lean_object* v_lookaheads_5703_; lean_object* v_argPosMap_5704_; lean_object* v_argsAt_5705_; lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5731_; 
v_num_5698_ = lean_ctor_get(v_split_5671_, 0);
v_candidates_5699_ = lean_ctor_get(v_split_5671_, 1);
v_added_5700_ = lean_ctor_get(v_split_5671_, 2);
v_resolved_5701_ = lean_ctor_get(v_split_5671_, 3);
v_trace_5702_ = lean_ctor_get(v_split_5671_, 4);
v_lookaheads_5703_ = lean_ctor_get(v_split_5671_, 5);
v_argPosMap_5704_ = lean_ctor_get(v_split_5671_, 6);
v_argsAt_5705_ = lean_ctor_get(v_split_5671_, 7);
v_isSharedCheck_5731_ = !lean_is_exclusive(v_split_5671_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5707_ = v_split_5671_;
v_isShared_5708_ = v_isSharedCheck_5731_;
goto v_resetjp_5706_;
}
else
{
lean_inc(v_argsAt_5705_);
lean_inc(v_argPosMap_5704_);
lean_inc(v_lookaheads_5703_);
lean_inc(v_trace_5702_);
lean_inc(v_resolved_5701_);
lean_inc(v_added_5700_);
lean_inc(v_candidates_5699_);
lean_inc(v_num_5698_);
lean_dec(v_split_5671_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5731_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
lean_object* v___x_5709_; lean_object* v___y_5711_; lean_object* v___x_5729_; uint8_t v___x_5730_; 
v___x_5709_ = lean_array_get_size(v_a_5668_);
v___x_5729_ = lean_unsigned_to_nat(0u);
v___x_5730_ = lean_nat_dec_lt(v___x_5729_, v___x_5709_);
if (v___x_5730_ == 0)
{
if (v_isRec_5666_ == 0)
{
v___y_5711_ = v_num_5698_;
goto v___jp_5710_;
}
else
{
goto v___jp_5726_;
}
}
else
{
goto v___jp_5726_;
}
v___jp_5710_:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5715_; 
v___x_5712_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5663_);
lean_inc(v___x_5665_);
lean_inc_ref(v___x_5664_);
v___x_5713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5664_);
lean_ctor_set(v___x_5713_, 1, v___x_5709_);
lean_ctor_set(v___x_5713_, 2, v___x_5665_);
lean_ctor_set(v___x_5713_, 3, v___x_5712_);
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v_trace_5702_);
lean_ctor_set(v___x_5675_, 0, v___x_5713_);
v___x_5715_ = v___x_5675_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v___x_5713_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_trace_5702_);
v___x_5715_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
lean_object* v___x_5717_; 
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 4, v___x_5715_);
lean_ctor_set(v___x_5707_, 0, v___y_5711_);
v___x_5717_ = v___x_5707_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v___y_5711_);
lean_ctor_set(v_reuseFailAlloc_5724_, 1, v_candidates_5699_);
lean_ctor_set(v_reuseFailAlloc_5724_, 2, v_added_5700_);
lean_ctor_set(v_reuseFailAlloc_5724_, 3, v_resolved_5701_);
lean_ctor_set(v_reuseFailAlloc_5724_, 4, v___x_5715_);
lean_ctor_set(v_reuseFailAlloc_5724_, 5, v_lookaheads_5703_);
lean_ctor_set(v_reuseFailAlloc_5724_, 6, v_argPosMap_5704_);
lean_ctor_set(v_reuseFailAlloc_5724_, 7, v_argsAt_5705_);
v___x_5717_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
lean_object* v___x_5719_; 
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 15, v___x_5717_);
v___x_5719_ = v___x_5696_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_nextDeclIdx_5677_);
lean_ctor_set(v_reuseFailAlloc_5723_, 1, v_enodeMap_5678_);
lean_ctor_set(v_reuseFailAlloc_5723_, 2, v_exprs_5679_);
lean_ctor_set(v_reuseFailAlloc_5723_, 3, v_parents_5680_);
lean_ctor_set(v_reuseFailAlloc_5723_, 4, v_congrTable_5681_);
lean_ctor_set(v_reuseFailAlloc_5723_, 5, v_appMap_5682_);
lean_ctor_set(v_reuseFailAlloc_5723_, 6, v_indicesFound_5683_);
lean_ctor_set(v_reuseFailAlloc_5723_, 7, v_toProcess_5684_);
lean_ctor_set(v_reuseFailAlloc_5723_, 8, v_internalizing_5685_);
lean_ctor_set(v_reuseFailAlloc_5723_, 9, v_nextIdx_5687_);
lean_ctor_set(v_reuseFailAlloc_5723_, 10, v_newRawFacts_5688_);
lean_ctor_set(v_reuseFailAlloc_5723_, 11, v_facts_5689_);
lean_ctor_set(v_reuseFailAlloc_5723_, 12, v_extThms_5690_);
lean_ctor_set(v_reuseFailAlloc_5723_, 13, v_ematch_5691_);
lean_ctor_set(v_reuseFailAlloc_5723_, 14, v_inj_5692_);
lean_ctor_set(v_reuseFailAlloc_5723_, 15, v___x_5717_);
lean_ctor_set(v_reuseFailAlloc_5723_, 16, v_clean_5693_);
lean_ctor_set(v_reuseFailAlloc_5723_, 17, v_sstates_5694_);
lean_ctor_set_uint8(v_reuseFailAlloc_5723_, sizeof(void*)*18, v_inconsistent_5686_);
v___x_5719_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
lean_object* v___x_5720_; lean_object* v___x_5721_; 
v___x_5720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
lean_ctor_set(v___x_5720_, 1, v_head_5672_);
v___x_5721_ = lean_array_push(v_a_5668_, v___x_5720_);
v_a_5667_ = v_tail_5673_;
v_a_5668_ = v___x_5721_;
goto _start;
}
}
}
}
v___jp_5726_:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; 
v___x_5727_ = lean_unsigned_to_nat(1u);
v___x_5728_ = lean_nat_add(v_num_5698_, v___x_5727_);
lean_dec(v_num_5698_);
v___y_5711_ = v___x_5728_;
goto v___jp_5710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v_snd_5735_, lean_object* v_c_5736_, lean_object* v___x_5737_, lean_object* v___x_5738_, lean_object* v_isRec_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_){
_start:
{
uint8_t v_isRec_boxed_5742_; lean_object* v_res_5743_; 
v_isRec_boxed_5742_ = lean_unbox(v_isRec_5739_);
v_res_5743_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5735_, v_c_5736_, v___x_5737_, v___x_5738_, v_isRec_boxed_5742_, v_a_5740_, v_a_5741_);
lean_dec_ref(v_c_5736_);
return v_res_5743_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = lean_box(0);
v___x_5756_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__4));
v___x_5757_ = l_Lean_mkConst(v___x_5756_, v___x_5755_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_5758_, lean_object* v_numCases_5759_, uint8_t v_isRec_5760_, uint8_t v_stopAtFirstFailure_5761_, uint8_t v_compress_5762_, lean_object* v_candidates_x3f_5763_, lean_object* v_goal_5764_, lean_object* v_kp_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_){
_start:
{
lean_object* v___x_5776_; 
v___x_5776_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5767_);
if (lean_obj_tag(v___x_5776_) == 0)
{
lean_object* v_a_5777_; uint8_t v_trace_5778_; lean_object* v___x_5779_; 
v_a_5777_ = lean_ctor_get(v___x_5776_, 0);
lean_inc(v_a_5777_);
lean_dec_ref_known(v___x_5776_, 1);
v_trace_5778_ = lean_ctor_get_uint8(v_a_5777_, sizeof(void*)*14);
lean_dec(v_a_5777_);
lean_inc_ref(v_goal_5764_);
v___x_5779_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5764_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
if (lean_obj_tag(v___x_5779_) == 0)
{
lean_object* v_a_5780_; lean_object* v_mvarId_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___f_5784_; lean_object* v___x_5785_; lean_object* v___f_5786_; lean_object* v___x_5787_; 
v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
lean_inc_n(v_a_5780_, 2);
lean_dec_ref_known(v___x_5779_, 1);
v_mvarId_5781_ = lean_ctor_get(v_goal_5764_, 1);
lean_inc(v_mvarId_5781_);
v___x_5782_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5758_);
v___x_5783_ = lean_box(v_isRec_5760_);
lean_inc_ref_n(v_c_5758_, 2);
lean_inc_ref(v___x_5782_);
v___f_5784_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5784_, 0, v___x_5782_);
lean_closure_set(v___f_5784_, 1, v_c_5758_);
lean_closure_set(v___f_5784_, 2, v_a_5780_);
lean_closure_set(v___f_5784_, 3, v_numCases_5759_);
lean_closure_set(v___f_5784_, 4, v___x_5783_);
v___x_5785_ = lean_box(v_trace_5778_);
v___f_5786_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5786_, 0, v_goal_5764_);
lean_closure_set(v___f_5786_, 1, v___x_5785_);
lean_closure_set(v___f_5786_, 2, v___f_5784_);
lean_closure_set(v___f_5786_, 3, v_c_5758_);
lean_closure_set(v___f_5786_, 4, v_candidates_x3f_5763_);
v___x_5787_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5781_, v___f_5786_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v_a_5788_; lean_object* v_fst_5789_; lean_object* v_snd_5790_; lean_object* v_fst_5791_; lean_object* v_snd_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
lean_inc(v_a_5788_);
lean_dec_ref_known(v___x_5787_, 1);
v_fst_5789_ = lean_ctor_get(v_a_5788_, 0);
lean_inc(v_fst_5789_);
v_snd_5790_ = lean_ctor_get(v_a_5788_, 1);
lean_inc_n(v_snd_5790_, 3);
lean_dec(v_a_5788_);
v_fst_5791_ = lean_ctor_get(v_fst_5789_, 0);
lean_inc(v_fst_5791_);
v_snd_5792_ = lean_ctor_get(v_fst_5789_, 1);
lean_inc(v_snd_5792_);
lean_dec(v_fst_5789_);
v___x_5793_ = l_List_lengthTR___redArg(v_fst_5791_);
v___x_5794_ = lean_unsigned_to_nat(0u);
v___x_5795_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__0));
v___x_5796_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v_snd_5790_, v_c_5758_, v___x_5782_, v___x_5793_, v_isRec_5760_, v_fst_5791_, v___x_5795_);
lean_dec_ref(v_c_5758_);
v___x_5797_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__2));
v___x_5798_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5765_, v_snd_5790_, v_stopAtFirstFailure_5761_, v___x_5796_, v___x_5797_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
lean_dec(v___x_5796_);
if (lean_obj_tag(v___x_5798_) == 0)
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5882_; 
v_a_5799_ = lean_ctor_get(v___x_5798_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5798_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5801_ = v___x_5798_;
v_isShared_5802_ = v_isSharedCheck_5882_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5798_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5882_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v_fst_5803_; 
v_fst_5803_ = lean_ctor_get(v_a_5799_, 0);
if (lean_obj_tag(v_fst_5803_) == 0)
{
lean_object* v_snd_5804_; lean_object* v_fst_5805_; lean_object* v_snd_5806_; lean_object* v___y_5808_; lean_object* v___y_5809_; lean_object* v_mvarId_5856_; lean_object* v___x_5857_; 
v_snd_5804_ = lean_ctor_get(v_a_5799_, 1);
lean_inc(v_snd_5804_);
lean_dec(v_a_5799_);
v_fst_5805_ = lean_ctor_get(v_snd_5804_, 0);
lean_inc(v_fst_5805_);
v_snd_5806_ = lean_ctor_get(v_snd_5804_, 1);
lean_inc(v_snd_5806_);
lean_dec(v_snd_5804_);
v_mvarId_5856_ = lean_ctor_get(v_snd_5790_, 1);
lean_inc_n(v_mvarId_5856_, 2);
lean_dec(v_snd_5790_);
v___x_5857_ = l_Lean_MVarId_getType(v_mvarId_5856_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
if (lean_obj_tag(v___x_5857_) == 0)
{
lean_object* v_a_5858_; uint8_t v___x_5859_; 
v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
lean_inc(v_a_5858_);
lean_dec_ref_known(v___x_5857_, 1);
v___x_5859_ = l_Lean_Expr_isFalse(v_a_5858_);
if (v___x_5859_ == 0)
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v_a_5862_; lean_object* v___x_5863_; 
v___x_5860_ = l_Lean_mkMVar(v_a_5780_);
v___x_5861_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5860_, v_a_5772_);
v_a_5862_ = lean_ctor_get(v___x_5861_, 0);
lean_inc(v_a_5862_);
lean_dec_ref(v___x_5861_);
v___x_5863_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5856_, v_a_5862_, v_a_5772_);
lean_dec_ref(v___x_5863_);
v___y_5808_ = v_a_5773_;
v___y_5809_ = v_a_5774_;
goto v___jp_5807_;
}
else
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v_a_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5864_ = l_Lean_mkMVar(v_a_5780_);
v___x_5865_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v___x_5864_, v_a_5772_);
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref(v___x_5865_);
v___x_5867_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___closed__5);
v___x_5868_ = l_Lean_Meta_mkExpectedPropHint(v_a_5866_, v___x_5867_);
v___x_5869_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_5856_, v___x_5868_, v_a_5772_);
lean_dec_ref(v___x_5869_);
v___y_5808_ = v_a_5773_;
v___y_5809_ = v_a_5774_;
goto v___jp_5807_;
}
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec(v_mvarId_5856_);
lean_dec(v_snd_5806_);
lean_dec(v_fst_5805_);
lean_del_object(v___x_5801_);
lean_dec(v_snd_5792_);
lean_dec(v_a_5780_);
v_a_5870_ = lean_ctor_get(v___x_5857_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5857_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5857_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5857_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
v___jp_5807_:
{
lean_object* v___x_5810_; uint8_t v___x_5811_; 
v___x_5810_ = lean_array_get_size(v_snd_5806_);
v___x_5811_ = lean_nat_dec_eq(v___x_5810_, v___x_5794_);
if (v___x_5811_ == 0)
{
lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5815_; 
lean_dec(v_fst_5805_);
lean_dec(v_snd_5792_);
v___x_5812_ = lean_array_to_list(v_snd_5806_);
v___x_5813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5812_);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 0, v___x_5813_);
v___x_5815_ = v___x_5801_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
else
{
lean_dec(v_snd_5806_);
if (lean_obj_tag(v_snd_5792_) == 1)
{
lean_object* v_val_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5851_; 
lean_del_object(v___x_5801_);
v_val_5817_ = lean_ctor_get(v_snd_5792_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v_snd_5792_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5819_ = v_snd_5792_;
v_isShared_5820_ = v_isSharedCheck_5851_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_val_5817_);
lean_dec(v_snd_5792_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5851_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5821_; 
v___x_5821_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5817_, v___y_5808_);
lean_dec(v_val_5817_);
if (lean_obj_tag(v___x_5821_) == 0)
{
lean_object* v_a_5822_; lean_object* v___x_5823_; 
v_a_5822_ = lean_ctor_get(v___x_5821_, 0);
lean_inc(v_a_5822_);
lean_dec_ref_known(v___x_5821_, 1);
v___x_5823_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5822_, v_fst_5805_, v_compress_5762_, v___y_5808_, v___y_5809_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5834_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5834_ == 0)
{
v___x_5826_ = v___x_5823_;
v_isShared_5827_ = v_isSharedCheck_5834_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_a_5824_);
lean_dec(v___x_5823_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5834_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v___x_5829_; 
if (v_isShared_5820_ == 0)
{
lean_ctor_set_tag(v___x_5819_, 0);
lean_ctor_set(v___x_5819_, 0, v_a_5824_);
v___x_5829_ = v___x_5819_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v_a_5824_);
v___x_5829_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
lean_object* v___x_5831_; 
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 0, v___x_5829_);
v___x_5831_ = v___x_5826_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5829_);
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
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5842_; 
lean_del_object(v___x_5819_);
v_a_5835_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5837_ = v___x_5823_;
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5823_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5838_ == 0)
{
v___x_5840_ = v___x_5837_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
}
else
{
lean_object* v_a_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5850_; 
lean_del_object(v___x_5819_);
lean_dec(v_fst_5805_);
v_a_5843_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5850_ == 0)
{
v___x_5845_ = v___x_5821_;
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_a_5843_);
lean_dec(v___x_5821_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5848_; 
if (v_isShared_5846_ == 0)
{
v___x_5848_ = v___x_5845_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
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
}
else
{
lean_object* v___x_5852_; lean_object* v___x_5854_; 
lean_dec(v_fst_5805_);
lean_dec(v_snd_5792_);
v___x_5852_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___closed__3));
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 0, v___x_5852_);
v___x_5854_ = v___x_5801_;
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
}
else
{
lean_object* v_val_5878_; lean_object* v___x_5880_; 
lean_inc_ref(v_fst_5803_);
lean_dec(v_a_5799_);
lean_dec(v_snd_5792_);
lean_dec(v_snd_5790_);
lean_dec(v_a_5780_);
v_val_5878_ = lean_ctor_get(v_fst_5803_, 0);
lean_inc(v_val_5878_);
lean_dec_ref_known(v_fst_5803_, 1);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 0, v_val_5878_);
v___x_5880_ = v___x_5801_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_val_5878_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec(v_snd_5792_);
lean_dec(v_snd_5790_);
lean_dec(v_a_5780_);
v_a_5883_ = lean_ctor_get(v___x_5798_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5798_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5798_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5798_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_dec_ref(v___x_5782_);
lean_dec(v_a_5780_);
lean_dec_ref(v_kp_5765_);
lean_dec_ref(v_c_5758_);
v_a_5891_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5787_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5787_);
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
lean_object* v_a_5899_; lean_object* v___x_5901_; uint8_t v_isShared_5902_; uint8_t v_isSharedCheck_5906_; 
lean_dec_ref(v_kp_5765_);
lean_dec_ref(v_goal_5764_);
lean_dec(v_candidates_x3f_5763_);
lean_dec(v_numCases_5759_);
lean_dec_ref(v_c_5758_);
v_a_5899_ = lean_ctor_get(v___x_5779_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5779_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5901_ = v___x_5779_;
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
else
{
lean_inc(v_a_5899_);
lean_dec(v___x_5779_);
v___x_5901_ = lean_box(0);
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
v_resetjp_5900_:
{
lean_object* v___x_5904_; 
if (v_isShared_5902_ == 0)
{
v___x_5904_ = v___x_5901_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
v___x_5904_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
return v___x_5904_;
}
}
}
}
else
{
lean_object* v_a_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5914_; 
lean_dec_ref(v_kp_5765_);
lean_dec_ref(v_goal_5764_);
lean_dec(v_candidates_x3f_5763_);
lean_dec(v_numCases_5759_);
lean_dec_ref(v_c_5758_);
v_a_5907_ = lean_ctor_get(v___x_5776_, 0);
v_isSharedCheck_5914_ = !lean_is_exclusive(v___x_5776_);
if (v_isSharedCheck_5914_ == 0)
{
v___x_5909_ = v___x_5776_;
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5776_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v___x_5912_; 
if (v_isShared_5910_ == 0)
{
v___x_5912_ = v___x_5909_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_5915_ = _args[0];
lean_object* v_numCases_5916_ = _args[1];
lean_object* v_isRec_5917_ = _args[2];
lean_object* v_stopAtFirstFailure_5918_ = _args[3];
lean_object* v_compress_5919_ = _args[4];
lean_object* v_candidates_x3f_5920_ = _args[5];
lean_object* v_goal_5921_ = _args[6];
lean_object* v_kp_5922_ = _args[7];
lean_object* v_a_5923_ = _args[8];
lean_object* v_a_5924_ = _args[9];
lean_object* v_a_5925_ = _args[10];
lean_object* v_a_5926_ = _args[11];
lean_object* v_a_5927_ = _args[12];
lean_object* v_a_5928_ = _args[13];
lean_object* v_a_5929_ = _args[14];
lean_object* v_a_5930_ = _args[15];
lean_object* v_a_5931_ = _args[16];
lean_object* v_a_5932_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_5933_; uint8_t v_stopAtFirstFailure_boxed_5934_; uint8_t v_compress_boxed_5935_; lean_object* v_res_5936_; 
v_isRec_boxed_5933_ = lean_unbox(v_isRec_5917_);
v_stopAtFirstFailure_boxed_5934_ = lean_unbox(v_stopAtFirstFailure_5918_);
v_compress_boxed_5935_ = lean_unbox(v_compress_5919_);
v_res_5936_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5915_, v_numCases_5916_, v_isRec_boxed_5933_, v_stopAtFirstFailure_boxed_5934_, v_compress_boxed_5935_, v_candidates_x3f_5920_, v_goal_5921_, v_kp_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_);
lean_dec(v_a_5931_);
lean_dec_ref(v_a_5930_);
lean_dec(v_a_5929_);
lean_dec_ref(v_a_5928_);
lean_dec(v_a_5927_);
lean_dec_ref(v_a_5926_);
lean_dec(v_a_5925_);
lean_dec_ref(v_a_5924_);
lean_dec(v_a_5923_);
return v_res_5936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_5937_, lean_object* v_numCases_5938_, uint8_t v_isRec_5939_, uint8_t v_stopAtFirstFailure_5940_, uint8_t v_compress_5941_, lean_object* v_candidates_x3f_5942_, lean_object* v_goal_5943_, lean_object* v_x_5944_, lean_object* v_kp_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_){
_start:
{
lean_object* v___x_5956_; 
v___x_5956_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_5937_, v_numCases_5938_, v_isRec_5939_, v_stopAtFirstFailure_5940_, v_compress_5941_, v_candidates_x3f_5942_, v_goal_5943_, v_kp_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_5957_ = _args[0];
lean_object* v_numCases_5958_ = _args[1];
lean_object* v_isRec_5959_ = _args[2];
lean_object* v_stopAtFirstFailure_5960_ = _args[3];
lean_object* v_compress_5961_ = _args[4];
lean_object* v_candidates_x3f_5962_ = _args[5];
lean_object* v_goal_5963_ = _args[6];
lean_object* v_x_5964_ = _args[7];
lean_object* v_kp_5965_ = _args[8];
lean_object* v_a_5966_ = _args[9];
lean_object* v_a_5967_ = _args[10];
lean_object* v_a_5968_ = _args[11];
lean_object* v_a_5969_ = _args[12];
lean_object* v_a_5970_ = _args[13];
lean_object* v_a_5971_ = _args[14];
lean_object* v_a_5972_ = _args[15];
lean_object* v_a_5973_ = _args[16];
lean_object* v_a_5974_ = _args[17];
lean_object* v_a_5975_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_5976_; uint8_t v_stopAtFirstFailure_boxed_5977_; uint8_t v_compress_boxed_5978_; lean_object* v_res_5979_; 
v_isRec_boxed_5976_ = lean_unbox(v_isRec_5959_);
v_stopAtFirstFailure_boxed_5977_ = lean_unbox(v_stopAtFirstFailure_5960_);
v_compress_boxed_5978_ = lean_unbox(v_compress_5961_);
v_res_5979_ = l_Lean_Meta_Grind_Action_splitCore(v_c_5957_, v_numCases_5958_, v_isRec_boxed_5976_, v_stopAtFirstFailure_boxed_5977_, v_compress_boxed_5978_, v_candidates_x3f_5962_, v_goal_5963_, v_x_5964_, v_kp_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_);
lean_dec(v_a_5974_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec_ref(v_a_5971_);
lean_dec(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec_ref(v_a_5967_);
lean_dec(v_a_5966_);
lean_dec_ref(v_x_5964_);
return v_res_5979_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v_kp_5980_, lean_object* v_snd_5981_, uint8_t v_stopAtFirstFailure_5982_, lean_object* v_as_5983_, lean_object* v_as_x27_5984_, lean_object* v_b_5985_, lean_object* v_a_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___redArg(v_kp_5980_, v_snd_5981_, v_stopAtFirstFailure_5982_, v_as_x27_5984_, v_b_5985_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object** _args){
lean_object* v_kp_5998_ = _args[0];
lean_object* v_snd_5999_ = _args[1];
lean_object* v_stopAtFirstFailure_6000_ = _args[2];
lean_object* v_as_6001_ = _args[3];
lean_object* v_as_x27_6002_ = _args[4];
lean_object* v_b_6003_ = _args[5];
lean_object* v_a_6004_ = _args[6];
lean_object* v___y_6005_ = _args[7];
lean_object* v___y_6006_ = _args[8];
lean_object* v___y_6007_ = _args[9];
lean_object* v___y_6008_ = _args[10];
lean_object* v___y_6009_ = _args[11];
lean_object* v___y_6010_ = _args[12];
lean_object* v___y_6011_ = _args[13];
lean_object* v___y_6012_ = _args[14];
lean_object* v___y_6013_ = _args[15];
lean_object* v___y_6014_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6015_; lean_object* v_res_6016_; 
v_stopAtFirstFailure_boxed_6015_ = lean_unbox(v_stopAtFirstFailure_6000_);
v_res_6016_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_kp_5998_, v_snd_5999_, v_stopAtFirstFailure_boxed_6015_, v_as_6001_, v_as_x27_6002_, v_b_6003_, v_a_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec(v___y_6011_);
lean_dec_ref(v___y_6010_);
lean_dec(v___y_6009_);
lean_dec_ref(v___y_6008_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec(v_as_x27_6002_);
lean_dec(v_as_6001_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_mvarId_6017_, lean_object* v_val_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_){
_start:
{
lean_object* v___x_6029_; 
v___x_6029_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_mvarId_6017_, v_val_6018_, v___y_6025_);
return v___x_6029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_mvarId_6030_, lean_object* v_val_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v_res_6042_; 
v_res_6042_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_mvarId_6030_, v_val_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
lean_dec(v___y_6040_);
lean_dec_ref(v___y_6039_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec_ref(v___y_6035_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec(v___y_6032_);
return v_res_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5(lean_object* v_00_u03b2_6043_, lean_object* v_x_6044_, lean_object* v_x_6045_, lean_object* v_x_6046_){
_start:
{
lean_object* v___x_6047_; 
v___x_6047_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5___redArg(v_x_6044_, v_x_6045_, v_x_6046_);
return v___x_6047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(lean_object* v_00_u03b2_6048_, lean_object* v_x_6049_, size_t v_x_6050_, size_t v_x_6051_, lean_object* v_x_6052_, lean_object* v_x_6053_){
_start:
{
lean_object* v___x_6054_; 
v___x_6054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___redArg(v_x_6049_, v_x_6050_, v_x_6051_, v_x_6052_, v_x_6053_);
return v___x_6054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6___boxed(lean_object* v_00_u03b2_6055_, lean_object* v_x_6056_, lean_object* v_x_6057_, lean_object* v_x_6058_, lean_object* v_x_6059_, lean_object* v_x_6060_){
_start:
{
size_t v_x_67933__boxed_6061_; size_t v_x_67934__boxed_6062_; lean_object* v_res_6063_; 
v_x_67933__boxed_6061_ = lean_unbox_usize(v_x_6057_);
lean_dec(v_x_6057_);
v_x_67934__boxed_6062_ = lean_unbox_usize(v_x_6058_);
lean_dec(v_x_6058_);
v_res_6063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6(v_00_u03b2_6055_, v_x_6056_, v_x_67933__boxed_6061_, v_x_67934__boxed_6062_, v_x_6059_, v_x_6060_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_6064_, lean_object* v_n_6065_, lean_object* v_k_6066_, lean_object* v_v_6067_){
_start:
{
lean_object* v___x_6068_; 
v___x_6068_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7___redArg(v_n_6065_, v_k_6066_, v_v_6067_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_6069_, size_t v_depth_6070_, lean_object* v_keys_6071_, lean_object* v_vals_6072_, lean_object* v_heq_6073_, lean_object* v_i_6074_, lean_object* v_entries_6075_){
_start:
{
lean_object* v___x_6076_; 
v___x_6076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___redArg(v_depth_6070_, v_keys_6071_, v_vals_6072_, v_i_6074_, v_entries_6075_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_6077_, lean_object* v_depth_6078_, lean_object* v_keys_6079_, lean_object* v_vals_6080_, lean_object* v_heq_6081_, lean_object* v_i_6082_, lean_object* v_entries_6083_){
_start:
{
size_t v_depth_boxed_6084_; lean_object* v_res_6085_; 
v_depth_boxed_6084_ = lean_unbox_usize(v_depth_6078_);
lean_dec(v_depth_6078_);
v_res_6085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__8(v_00_u03b2_6077_, v_depth_boxed_6084_, v_keys_6079_, v_vals_6080_, v_heq_6081_, v_i_6082_, v_entries_6083_);
lean_dec_ref(v_vals_6080_);
lean_dec_ref(v_keys_6079_);
return v_res_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6086_, lean_object* v_x_6087_, lean_object* v_x_6088_, lean_object* v_x_6089_, lean_object* v_x_6090_){
_start:
{
lean_object* v___x_6091_; 
v___x_6091_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__5_spec__5_spec__6_spec__7_spec__8___redArg(v_x_6087_, v_x_6088_, v_x_6089_, v_x_6090_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_){
_start:
{
lean_object* v___x_6105_; 
v___x_6105_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6092_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_){
_start:
{
lean_object* v_res_6119_; 
v_res_6119_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_);
lean_dec(v___y_6117_);
lean_dec_ref(v___y_6116_);
lean_dec(v___y_6115_);
lean_dec_ref(v___y_6114_);
lean_dec(v___y_6113_);
lean_dec_ref(v___y_6112_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6107_);
return v_res_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_){
_start:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; 
v___x_6131_ = lean_st_mk_ref(v_goal_6120_);
v___x_6132_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6131_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
if (lean_obj_tag(v___x_6132_) == 0)
{
lean_object* v_a_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6142_; 
v_a_6133_ = lean_ctor_get(v___x_6132_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6132_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6135_ = v___x_6132_;
v_isShared_6136_ = v_isSharedCheck_6142_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_a_6133_);
lean_dec(v___x_6132_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6142_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6140_; 
v___x_6137_ = lean_st_ref_get(v___x_6131_);
lean_dec(v___x_6131_);
v___x_6138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6138_, 0, v_a_6133_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
if (v_isShared_6136_ == 0)
{
lean_ctor_set(v___x_6135_, 0, v___x_6138_);
v___x_6140_ = v___x_6135_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
else
{
lean_object* v_a_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
lean_dec(v___x_6131_);
v_a_6143_ = lean_ctor_get(v___x_6132_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6132_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6145_ = v___x_6132_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_a_6143_);
lean_dec(v___x_6132_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_){
_start:
{
lean_object* v_res_6162_; 
v_res_6162_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_);
lean_dec(v___y_6160_);
lean_dec_ref(v___y_6159_);
lean_dec(v___y_6158_);
lean_dec_ref(v___y_6157_);
lean_dec(v___y_6156_);
lean_dec_ref(v___y_6155_);
lean_dec(v___y_6154_);
lean_dec_ref(v___y_6153_);
lean_dec(v___y_6152_);
return v_res_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6163_, lean_object* v___f_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_){
_start:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6178_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6178_, 0, v___y_6163_);
v___x_6179_ = l_Lean_Meta_Grind_Action_andThen(v___x_6178_, v___f_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6180_, lean_object* v___f_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
lean_object* v_res_6195_; 
v_res_6195_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6180_, v___f_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6191_);
lean_dec_ref(v___y_6190_);
lean_dec(v___y_6189_);
lean_dec_ref(v___y_6188_);
lean_dec(v___y_6187_);
lean_dec_ref(v___y_6186_);
lean_dec(v___y_6185_);
return v_res_6195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6197_, uint8_t v_compress_6198_, lean_object* v_goal_6199_, lean_object* v_kna_6200_, lean_object* v_kp_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_){
_start:
{
lean_object* v_toGoalState_6212_; lean_object* v_split_6213_; lean_object* v_mvarId_6214_; lean_object* v_candidates_6215_; lean_object* v___f_6216_; lean_object* v___f_6217_; lean_object* v___x_6218_; 
v_toGoalState_6212_ = lean_ctor_get(v_goal_6199_, 0);
v_split_6213_ = lean_ctor_get(v_toGoalState_6212_, 15);
v_mvarId_6214_ = lean_ctor_get(v_goal_6199_, 1);
lean_inc(v_mvarId_6214_);
v_candidates_6215_ = lean_ctor_get(v_split_6213_, 1);
lean_inc(v_candidates_6215_);
v___f_6216_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6217_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6217_, 0, v_goal_6199_);
v___x_6218_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6214_, v___f_6217_, v_a_6202_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
if (lean_obj_tag(v___x_6218_) == 0)
{
lean_object* v_a_6219_; lean_object* v_fst_6220_; 
v_a_6219_ = lean_ctor_get(v___x_6218_, 0);
lean_inc(v_a_6219_);
lean_dec_ref_known(v___x_6218_, 1);
v_fst_6220_ = lean_ctor_get(v_a_6219_, 0);
if (lean_obj_tag(v_fst_6220_) == 1)
{
lean_object* v_snd_6221_; lean_object* v_c_6222_; lean_object* v_numCases_6223_; uint8_t v_isRec_6224_; lean_object* v___y_6226_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; uint8_t v___x_6239_; 
lean_inc_ref(v_fst_6220_);
v_snd_6221_ = lean_ctor_get(v_a_6219_, 1);
lean_inc(v_snd_6221_);
lean_dec(v_a_6219_);
v_c_6222_ = lean_ctor_get(v_fst_6220_, 0);
lean_inc_ref(v_c_6222_);
v_numCases_6223_ = lean_ctor_get(v_fst_6220_, 1);
lean_inc(v_numCases_6223_);
v_isRec_6224_ = lean_ctor_get_uint8(v_fst_6220_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6220_, 2);
v___x_6234_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6222_);
v___x_6235_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6221_, v___x_6234_);
lean_dec_ref(v___x_6234_);
v___x_6236_ = lean_unsigned_to_nat(1u);
v___x_6239_ = lean_nat_dec_lt(v___x_6236_, v_numCases_6223_);
if (v___x_6239_ == 0)
{
if (v_isRec_6224_ == 0)
{
v___y_6226_ = v___x_6235_;
goto v___jp_6225_;
}
else
{
goto v___jp_6237_;
}
}
else
{
goto v___jp_6237_;
}
v___jp_6225_:
{
lean_object* v___f_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; 
v___f_6227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6227_, 0, v___y_6226_);
lean_closure_set(v___f_6227_, 1, v___f_6216_);
v___x_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6228_, 0, v_candidates_6215_);
v___x_6229_ = lean_box(v_isRec_6224_);
v___x_6230_ = lean_box(v_stopAtFirstFailure_6197_);
v___x_6231_ = lean_box(v_compress_6198_);
v___x_6232_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6232_, 0, v_c_6222_);
lean_closure_set(v___x_6232_, 1, v_numCases_6223_);
lean_closure_set(v___x_6232_, 2, v___x_6229_);
lean_closure_set(v___x_6232_, 3, v___x_6230_);
lean_closure_set(v___x_6232_, 4, v___x_6231_);
lean_closure_set(v___x_6232_, 5, v___x_6228_);
v___x_6233_ = l_Lean_Meta_Grind_Action_andThen(v___x_6232_, v___f_6227_, v_snd_6221_, v_kna_6200_, v_kp_6201_, v_a_6202_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
return v___x_6233_;
}
v___jp_6237_:
{
lean_object* v___x_6238_; 
v___x_6238_ = lean_nat_add(v___x_6235_, v___x_6236_);
lean_dec(v___x_6235_);
v___y_6226_ = v___x_6238_;
goto v___jp_6225_;
}
}
else
{
lean_object* v_snd_6240_; lean_object* v___x_6241_; 
lean_dec(v_candidates_6215_);
lean_dec_ref(v_kp_6201_);
v_snd_6240_ = lean_ctor_get(v_a_6219_, 1);
lean_inc(v_snd_6240_);
lean_dec(v_a_6219_);
lean_inc(v_a_6210_);
lean_inc_ref(v_a_6209_);
lean_inc(v_a_6208_);
lean_inc_ref(v_a_6207_);
lean_inc(v_a_6206_);
lean_inc_ref(v_a_6205_);
lean_inc(v_a_6204_);
lean_inc_ref(v_a_6203_);
lean_inc(v_a_6202_);
v___x_6241_ = lean_apply_11(v_kna_6200_, v_snd_6240_, v_a_6202_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_, lean_box(0));
return v___x_6241_;
}
}
else
{
lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6249_; 
lean_dec(v_candidates_6215_);
lean_dec_ref(v_kp_6201_);
lean_dec_ref(v_kna_6200_);
v_a_6242_ = lean_ctor_get(v___x_6218_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6218_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6244_ = v___x_6218_;
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6218_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6245_ == 0)
{
v___x_6247_ = v___x_6244_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6242_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6250_, lean_object* v_compress_6251_, lean_object* v_goal_6252_, lean_object* v_kna_6253_, lean_object* v_kp_6254_, lean_object* v_a_6255_, lean_object* v_a_6256_, lean_object* v_a_6257_, lean_object* v_a_6258_, lean_object* v_a_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6265_; uint8_t v_compress_boxed_6266_; lean_object* v_res_6267_; 
v_stopAtFirstFailure_boxed_6265_ = lean_unbox(v_stopAtFirstFailure_6250_);
v_compress_boxed_6266_ = lean_unbox(v_compress_6251_);
v_res_6267_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6265_, v_compress_boxed_6266_, v_goal_6252_, v_kna_6253_, v_kp_6254_, v_a_6255_, v_a_6256_, v_a_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
lean_dec(v_a_6259_);
lean_dec_ref(v_a_6258_);
lean_dec(v_a_6257_);
lean_dec_ref(v_a_6256_);
lean_dec(v_a_6255_);
return v_res_6267_;
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
