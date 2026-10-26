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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getHoistedDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkHoistedDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_mkAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_Grind_SplitInfo_beq(lean_object*, lean_object*);
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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_withHoistedDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", generation: "};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v___x_1115_);
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
v___x_1124_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1115_, v_declHint_1106_);
lean_dec_ref(v___x_1115_);
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
lean_object* v_toCold_1273_; lean_object* v_currRecDepth_1274_; lean_object* v_ref_1275_; uint16_t v_optionFlags_1276_; uint8_t v_suppressElabErrors_1277_; uint8_t v_checkDeprecated_1278_; uint8_t v_isRecordingDeps_1279_; lean_object* v_ref_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_toCold_1273_ = lean_ctor_get(v___y_1270_, 0);
v_currRecDepth_1274_ = lean_ctor_get(v___y_1270_, 1);
v_ref_1275_ = lean_ctor_get(v___y_1270_, 2);
v_optionFlags_1276_ = lean_ctor_get_uint16(v___y_1270_, sizeof(void*)*3);
v_suppressElabErrors_1277_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 2);
v_checkDeprecated_1278_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1279_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 4);
v_ref_1280_ = l_Lean_replaceRef(v_ref_1260_, v_ref_1275_);
lean_inc(v_currRecDepth_1274_);
lean_inc_ref(v_toCold_1273_);
v___x_1281_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1281_, 0, v_toCold_1273_);
lean_ctor_set(v___x_1281_, 1, v_currRecDepth_1274_);
lean_ctor_set(v___x_1281_, 2, v_ref_1280_);
lean_ctor_set_uint16(v___x_1281_, sizeof(void*)*3, v_optionFlags_1276_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 2, v_suppressElabErrors_1277_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 3, v_checkDeprecated_1278_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*3 + 4, v_isRecordingDeps_1279_);
v___x_1282_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1261_, v___y_1268_, v___y_1269_, v___x_1281_, v___y_1271_);
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
lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___x_1794_; 
lean_inc_ref(v_e_1533_);
v___x_1794_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1533_, v_a_1541_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1823_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1823_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1823_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = l_Lean_Expr_cleanupAnnotations(v_a_1795_);
lean_dec(v_a_1795_);
v___x_1800_ = l_Lean_Expr_isApp(v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v___x_1799_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1799_);
v___x_1802_ = l_Lean_Expr_isApp(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1801_);
lean_dec_ref(v___x_1799_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v_arg_1803_; lean_object* v_arg_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_arg_1803_ = lean_ctor_get(v___x_1799_, 1);
lean_inc_ref(v_arg_1803_);
lean_dec_ref(v___x_1799_);
v_arg_1804_ = lean_ctor_get(v___x_1801_, 1);
lean_inc_ref(v_arg_1804_);
v___x_1805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_1807_ = l_Lean_Expr_isConstOf(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16));
v___x_1809_ = l_Lean_Expr_isConstOf(v___x_1805_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_Expr_isApp(v___x_1805_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1805_);
lean_dec_ref(v___x_1805_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_1813_ = l_Lean_Expr_isConstOf(v___x_1811_, v___x_1812_);
lean_dec_ref(v___x_1811_);
if (v___x_1813_ == 0)
{
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_del_object(v___x_1797_);
v___y_1674_ = v_a_1534_;
v___y_1675_ = v_a_1535_;
v___y_1676_ = v_a_1536_;
v___y_1677_ = v_a_1537_;
v___y_1678_ = v_a_1538_;
v___y_1679_ = v_a_1539_;
v___y_1680_ = v_a_1540_;
v___y_1681_ = v_a_1541_;
v___y_1682_ = v_a_1542_;
v___y_1683_ = v_a_1543_;
goto v___jp_1673_;
}
else
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_Meta_Grind_isMorallyIff(v_e_1533_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1803_);
lean_dec_ref(v_e_1533_);
v___x_1815_ = lean_unsigned_to_nat(2u);
v___x_1816_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*1, v___x_1814_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*1 + 1, v___x_1814_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1816_);
v___x_1818_ = v___x_1797_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v___x_1820_; 
lean_del_object(v___x_1797_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1820_;
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec_ref(v___x_1805_);
lean_del_object(v___x_1797_);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1821_;
}
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1805_);
lean_del_object(v___x_1797_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(v_e_1533_, v_arg_1804_, v_arg_1803_, v_a_1534_, v_a_1538_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
return v___x_1822_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v_e_1533_);
v_a_1824_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1794_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1794_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
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
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = l_Lean_Expr_getAppNumArgs(v_e_1533_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v___x_1561_);
lean_dec(v___x_1562_);
v___x_1564_ = lean_nat_sub(v___x_1563_, v___x_1561_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_Expr_getRevArg_x21(v_e_1533_, v___x_1564_);
lean_dec_ref(v_e_1533_);
v___x_1566_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(v___x_1565_, v___y_1557_, v___y_1558_, v___y_1555_, v___y_1560_, v___y_1556_, v___y_1559_);
return v___x_1566_;
}
v___jp_1567_:
{
uint8_t v___x_1579_; 
v___x_1579_ = l_Lean_Expr_isFVar(v_e_1533_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_e_1533_);
v___x_1580_ = lean_box(1);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; 
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc_ref(v_e_1533_);
v___x_1582_ = lean_infer_type(v_e_1533_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Meta_whnfD(v_a_1583_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_n(v_a_1585_, 2);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
v___x_1587_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_indentExpr(v_a_1585_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_Expr_getAppFn(v_a_1585_);
lean_dec(v_a_1585_);
if (lean_obj_tag(v___x_1593_) == 4)
{
lean_object* v_declName_1594_; lean_object* v___x_1595_; 
v_declName_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_declName_1594_);
lean_dec_ref_known(v___x_1593_, 2);
v___x_1595_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0(v_declName_1594_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1628_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1628_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1628_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
if (lean_obj_tag(v_a_1596_) == 5)
{
lean_object* v_val_1600_; lean_object* v_ctors_1601_; uint8_t v_isRec_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1592_, 2);
v_val_1600_ = lean_ctor_get(v_a_1596_, 0);
lean_inc_ref(v_val_1600_);
lean_dec_ref_known(v_a_1596_, 1);
v_ctors_1601_ = lean_ctor_get(v_val_1600_, 4);
lean_inc(v_ctors_1601_);
v_isRec_1602_ = lean_ctor_get_uint8(v_val_1600_, sizeof(void*)*6);
lean_dec_ref(v_val_1600_);
v___x_1603_ = l_List_lengthTR___redArg(v_ctors_1601_);
lean_dec(v_ctors_1601_);
v___x_1604_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1, v_isRec_1602_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*1 + 1, v___y_1568_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1604_);
v___x_1606_ = v___x_1598_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1598_);
lean_dec(v_a_1596_);
v___x_1608_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1573_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; uint8_t v_verbose_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_verbose_1610_ = lean_ctor_get_uint8(v_a_1609_, 0);
lean_dec(v_a_1609_);
if (v_verbose_1610_ == 0)
{
lean_dec_ref_known(v___x_1592_, 2);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Sym_reportIssue(v___x_1592_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec_ref_known(v___x_1611_, 1);
goto v___jp_1548_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
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
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1620_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1608_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1608_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1629_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1595_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1595_);
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
else
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1593_);
v___x_1637_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1573_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; uint8_t v_verbose_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v_verbose_1639_ = lean_ctor_get_uint8(v_a_1638_, 0);
lean_dec(v_a_1638_);
if (v_verbose_1639_ == 0)
{
lean_dec_ref_known(v___x_1592_, 2);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Sym_reportIssue(v___x_1592_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
goto v___jp_1551_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref_known(v___x_1592_, 2);
v_a_1649_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1637_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1637_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_e_1533_);
v_a_1657_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1584_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1584_);
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
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_e_1533_);
v_a_1665_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1582_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1582_);
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
v___jp_1673_:
{
uint8_t v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_isIte(v_e_1533_);
if (v___x_1684_ == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Lean_Meta_Grind_isDIte(v_e_1533_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(v_e_1533_, v___y_1674_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_inc_ref(v_e_1533_);
v___x_1689_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(v_e_1533_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1749_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1749_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_unbox(v_a_1690_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v_env_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_get(v___y_1683_);
v_env_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_ref(v_env_1696_);
lean_dec(v___x_1695_);
v___x_1697_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1696_, v_e_1533_);
if (lean_obj_tag(v___x_1697_) == 1)
{
lean_object* v_val_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1704_; 
lean_dec_ref(v_e_1533_);
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1698_);
lean_dec(v_val_1698_);
v___x_1700_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
v___x_1701_ = lean_unbox(v_a_1690_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*1, v___x_1701_);
v___x_1702_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*1 + 1, v___x_1702_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1700_);
v___x_1704_ = v___x_1692_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1700_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v___x_1706_; 
lean_dec(v___x_1697_);
lean_del_object(v___x_1692_);
v___x_1706_ = l_Lean_Expr_getAppFn(v_e_1533_);
if (lean_obj_tag(v___x_1706_) == 4)
{
lean_object* v_declName_1707_; lean_object* v___x_1708_; 
v_declName_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_declName_1707_);
lean_dec_ref_known(v___x_1706_, 2);
v___x_1708_ = l_Lean_Meta_isInductivePredicate_x3f(v_declName_1707_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
if (lean_obj_tag(v_a_1709_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1711_; 
v_val_1710_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_a_1709_, 1);
lean_inc_ref(v_e_1533_);
v___x_1711_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1533_, v___y_1674_, v___y_1678_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1726_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_unbox(v_a_1712_);
lean_dec(v_a_1712_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
lean_del_object(v___x_1714_);
lean_dec(v_val_1710_);
v___x_1717_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1717_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
else
{
lean_object* v_ctors_1718_; uint8_t v_isRec_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; lean_object* v___x_1724_; 
lean_dec_ref(v_e_1533_);
v_ctors_1718_ = lean_ctor_get(v_val_1710_, 4);
lean_inc(v_ctors_1718_);
v_isRec_1719_ = lean_ctor_get_uint8(v_val_1710_, sizeof(void*)*6);
lean_dec(v_val_1710_);
v___x_1720_ = l_List_lengthTR___redArg(v_ctors_1718_);
lean_dec(v_ctors_1718_);
v___x_1721_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1, v_isRec_1719_);
v___x_1722_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1 + 1, v___x_1722_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1721_);
v___x_1724_ = v___x_1714_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1721_);
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
lean_dec(v_val_1710_);
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v_a_1727_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1711_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1711_);
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
else
{
uint8_t v___x_1735_; 
lean_dec(v_a_1709_);
v___x_1735_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1735_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v_a_1736_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1708_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1708_);
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
uint8_t v___x_1744_; 
lean_dec_ref(v___x_1706_);
v___x_1744_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
v___y_1568_ = v___x_1744_;
v___y_1569_ = v___y_1674_;
v___y_1570_ = v___y_1675_;
v___y_1571_ = v___y_1676_;
v___y_1572_ = v___y_1677_;
v___y_1573_ = v___y_1678_;
v___y_1574_ = v___y_1679_;
v___y_1575_ = v___y_1680_;
v___y_1576_ = v___y_1681_;
v___y_1577_ = v___y_1682_;
v___y_1578_ = v___y_1683_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_a_1690_);
lean_dec_ref(v_e_1533_);
v___x_1745_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1745_);
v___x_1747_ = v___x_1692_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
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
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_e_1533_);
v_a_1750_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1689_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1689_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_toCold_1758_; lean_object* v_options_1759_; uint8_t v_hasTrace_1760_; 
v_toCold_1758_ = lean_ctor_get(v___y_1682_, 0);
v_options_1759_ = lean_ctor_get(v_toCold_1758_, 2);
v_hasTrace_1760_ = lean_ctor_get_uint8(v_options_1759_, sizeof(void*)*1);
if (v_hasTrace_1760_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v_inheritedTraceOptions_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_inheritedTraceOptions_1761_ = lean_ctor_get(v_toCold_1758_, 11);
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7));
v___x_1763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
v___x_1764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1761_, v_options_1759_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_e_1533_);
goto v___jp_1545_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_updateLastTag(v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec_ref_known(v___x_1765_, 1);
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
v___x_1767_ = l_Lean_MessageData_ofExpr(v_e_1533_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_1762_, v___x_1768_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref_known(v___x_1769_, 1);
goto v___jp_1545_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v_e_1533_);
v_a_1778_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1765_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1765_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_e_1533_);
v_a_1786_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1686_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1686_);
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
v___y_1555_ = v___y_1680_;
v___y_1556_ = v___y_1682_;
v___y_1557_ = v___y_1674_;
v___y_1558_ = v___y_1678_;
v___y_1559_ = v___y_1683_;
v___y_1560_ = v___y_1681_;
goto v___jp_1554_;
}
}
else
{
v___y_1555_ = v___y_1680_;
v___y_1556_ = v___y_1682_;
v___y_1557_ = v___y_1674_;
v___y_1558_ = v___y_1678_;
v___y_1559_ = v___y_1683_;
v___y_1560_ = v___y_1681_;
goto v___jp_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___boxed(lean_object* v_e_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec(v_a_1833_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(lean_object* v_cls_1845_, lean_object* v_msg_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v_cls_1845_, v_msg_1846_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___boxed(lean_object* v_cls_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1(v_cls_1859_, v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v___y_1861_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(lean_object* v_00_u03b1_1873_, lean_object* v_constName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___redArg(v_constName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_constName_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0(v_00_u03b1_1887_, v_constName_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1901_, lean_object* v_ref_1902_, lean_object* v_constName_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___redArg(v_ref_1902_, v_constName_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_ref_1917_, lean_object* v_constName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1(v_00_u03b1_1916_, v_ref_1917_, v_constName_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
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
lean_dec(v_ref_1917_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v_declHint_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1932_, v_msg_1933_, v_declHint_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_ref_1948_, lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1947_, v_ref_1948_, v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec(v_ref_1948_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1963_, lean_object* v_declHint_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1963_, v_declHint_1964_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1977_, lean_object* v_declHint_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1977_, v_declHint_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec(v___y_1979_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1991_, lean_object* v_ref_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1992_, v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_ref_2007_, lean_object* v_msg_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2006_, v_ref_2007_, v_msg_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v_ref_2007_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2021_, lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_2022_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2035_, lean_object* v_msg_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2035_, v_msg_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(lean_object* v_a_2049_, lean_object* v_x_2050_){
_start:
{
if (lean_obj_tag(v_x_2050_) == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
else
{
lean_object* v_key_2052_; lean_object* v_value_2053_; lean_object* v_tail_2054_; lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v_fst_2057_; lean_object* v_snd_2058_; uint8_t v___x_2059_; 
v_key_2052_ = lean_ctor_get(v_x_2050_, 0);
v_value_2053_ = lean_ctor_get(v_x_2050_, 1);
v_tail_2054_ = lean_ctor_get(v_x_2050_, 2);
v_fst_2055_ = lean_ctor_get(v_key_2052_, 0);
v_snd_2056_ = lean_ctor_get(v_key_2052_, 1);
v_fst_2057_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2058_ = lean_ctor_get(v_a_2049_, 1);
v___x_2059_ = lean_expr_eqv(v_fst_2055_, v_fst_2057_);
if (v___x_2059_ == 0)
{
v_x_2050_ = v_tail_2054_;
goto _start;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_expr_eqv(v_snd_2056_, v_snd_2058_);
if (v___x_2061_ == 0)
{
v_x_2050_ = v_tail_2054_;
goto _start;
}
else
{
lean_object* v___x_2063_; 
lean_inc(v_value_2053_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_value_2053_);
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg___boxed(lean_object* v_a_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2064_, v_x_2065_);
lean_dec(v_x_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_buckets_2069_; lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2072_; uint64_t v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; uint64_t v_fold_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_buckets_2069_ = lean_ctor_get(v_m_2067_, 1);
v_fst_2070_ = lean_ctor_get(v_a_2068_, 0);
v_snd_2071_ = lean_ctor_get(v_a_2068_, 1);
v___x_2072_ = lean_array_get_size(v_buckets_2069_);
v___x_2073_ = l_Lean_Expr_hash(v_fst_2070_);
v___x_2074_ = l_Lean_Expr_hash(v_snd_2071_);
v___x_2075_ = lean_uint64_mix_hash(v___x_2073_, v___x_2074_);
v___x_2076_ = 32ULL;
v___x_2077_ = lean_uint64_shift_right(v___x_2075_, v___x_2076_);
v_fold_2078_ = lean_uint64_xor(v___x_2075_, v___x_2077_);
v___x_2079_ = 16ULL;
v___x_2080_ = lean_uint64_shift_right(v_fold_2078_, v___x_2079_);
v___x_2081_ = lean_uint64_xor(v_fold_2078_, v___x_2080_);
v___x_2082_ = lean_uint64_to_usize(v___x_2081_);
v___x_2083_ = lean_usize_of_nat(v___x_2072_);
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_sub(v___x_2083_, v___x_2084_);
v___x_2086_ = lean_usize_land(v___x_2082_, v___x_2085_);
v___x_2087_ = lean_array_uget_borrowed(v_buckets_2069_, v___x_2086_);
v___x_2088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2068_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg___boxed(lean_object* v_m_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2089_, v_a_2090_);
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_m_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(uint8_t v_a_2092_, uint8_t v___x_2093_, lean_object* v_fst_2094_, lean_object* v_snd_2095_, lean_object* v___x_2096_, lean_object* v_____r_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_unsigned_to_nat(2u);
v___x_2110_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1, v_a_2092_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1 + 1, v___x_2093_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_fst_2094_);
lean_ctor_set(v___x_2112_, 1, v_snd_2095_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2096_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2117_ = _args[0];
lean_object* v___x_2118_ = _args[1];
lean_object* v_fst_2119_ = _args[2];
lean_object* v_snd_2120_ = _args[3];
lean_object* v___x_2121_ = _args[4];
lean_object* v_____r_2122_ = _args[5];
lean_object* v___y_2123_ = _args[6];
lean_object* v___y_2124_ = _args[7];
lean_object* v___y_2125_ = _args[8];
lean_object* v___y_2126_ = _args[9];
lean_object* v___y_2127_ = _args[10];
lean_object* v___y_2128_ = _args[11];
lean_object* v___y_2129_ = _args[12];
lean_object* v___y_2130_ = _args[13];
lean_object* v___y_2131_ = _args[14];
lean_object* v___y_2132_ = _args[15];
lean_object* v___y_2133_ = _args[16];
_start:
{
uint8_t v_a_34317__boxed_2134_; uint8_t v___x_34318__boxed_2135_; lean_object* v_res_2136_; 
v_a_34317__boxed_2134_ = lean_unbox(v_a_2117_);
v___x_34318__boxed_2135_ = lean_unbox(v___x_2118_);
v_res_2136_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v_a_34317__boxed_2134_, v___x_34318__boxed_2135_, v_fst_2119_, v_snd_2120_, v___x_2121_, v_____r_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(lean_object* v_fst_2137_, lean_object* v_snd_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v_____r_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2153_ = l_Lean_Expr_appFn_x21(v_fst_2137_);
v___x_2154_ = l_Lean_Expr_appFn_x21(v_snd_2138_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2139_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2140_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0___boxed(lean_object* v_fst_2160_, lean_object* v_snd_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_____r_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2160_, v_snd_2161_, v___x_2162_, v___x_2163_, v_____r_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v_snd_2161_);
lean_dec(v_fst_2160_);
return v_res_2176_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___f_2178_; 
v___x_2177_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2178_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2178_, 0, v___x_2177_);
return v___f_2178_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9));
v___x_2184_ = l_Lean_Name_append(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__3));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__5));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__7));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__9));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__11));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__13));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(uint8_t v_a_2203_, lean_object* v___y_2204_, lean_object* v_eq_2205_, lean_object* v_a_2206_, lean_object* v_b_2207_, lean_object* v_a_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___y_2221_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2363_; 
v_snd_2241_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_a_2208_, 0);
lean_dec(v_unused_2364_);
v___x_2243_ = v_a_2208_;
v_isShared_2244_ = v_isSharedCheck_2363_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_dec(v_a_2208_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2363_;
goto v_resetjp_2242_;
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2232_; 
v_a_2222_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2224_ = v___y_2221_;
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___y_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2232_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2222_, 1);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; 
lean_del_object(v___x_2224_);
v_a_2230_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2222_, 1);
v_a_2208_ = v_a_2230_;
goto _start;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2233_ = lean_ctor_get(v___y_2221_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___y_2221_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___y_2221_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___y_2221_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v_resetjp_2242_:
{
lean_object* v_snd_2245_; lean_object* v_fst_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2362_; 
v_snd_2245_ = lean_ctor_get(v_snd_2241_, 1);
v_fst_2246_ = lean_ctor_get(v_snd_2241_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_snd_2241_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2248_ = v_snd_2241_;
v_isShared_2249_ = v_isSharedCheck_2362_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_snd_2245_);
lean_inc(v_fst_2246_);
lean_dec(v_snd_2241_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2362_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2361_; 
v_fst_2250_ = lean_ctor_get(v_snd_2245_, 0);
v_snd_2251_ = lean_ctor_get(v_snd_2245_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_snd_2245_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2253_ = v_snd_2245_;
v_isShared_2254_ = v_isSharedCheck_2361_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2250_);
lean_dec(v_snd_2245_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2361_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint8_t v___y_2256_; uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Expr_isApp(v_fst_2250_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v___y_2256_ = v_a_2203_;
goto v___jp_2255_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Expr_isApp(v_snd_2251_);
if (v___x_2271_ == 0)
{
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v___y_2256_ = v___x_2271_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; uint8_t v___x_2276_; 
lean_del_object(v___x_2253_);
lean_del_object(v___x_2248_);
lean_del_object(v___x_2243_);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_nat_sub(v_fst_2246_, v___x_2273_);
lean_dec(v_fst_2246_);
v___f_2275_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__0);
lean_inc(v___y_2204_);
lean_inc(v___x_2274_);
v___x_2276_ = l_List_elem___redArg(v___f_2275_, v___x_2274_, v___y_2204_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = l_Lean_Expr_appArg_x21(v_fst_2250_);
v___x_2278_ = l_Lean_Expr_appArg_x21(v_snd_2251_);
v___x_2279_ = l_Lean_Meta_Grind_isEqv___redArg(v___x_2277_, v___x_2278_, v___y_2209_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unbox(v_a_2280_);
if (v___x_2281_ == 0)
{
lean_object* v_toCold_2282_; lean_object* v_options_2283_; lean_object* v_inheritedTraceOptions_2284_; uint8_t v_hasTrace_2285_; 
v_toCold_2282_ = lean_ctor_get(v___y_2217_, 0);
v_options_2283_ = lean_ctor_get(v_toCold_2282_, 2);
v_inheritedTraceOptions_2284_ = lean_ctor_get(v_toCold_2282_, 11);
v_hasTrace_2285_ = lean_ctor_get_uint8(v_options_2283_, sizeof(void*)*1);
if (v_hasTrace_2285_ == 0)
{
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
goto v___jp_2286_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_2291_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_2292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2284_, v_options_2283_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
goto v___jp_2286_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_Grind_updateLastTag(v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; 
lean_dec_ref_known(v___x_2293_, 1);
v___x_2294_ = l_Lean_Meta_Grind_getGeneration___redArg(v_eq_2205_, v___y_2209_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__4);
lean_inc_ref(v_a_2206_);
v___x_2297_ = l_Lean_MessageData_ofExpr(v_a_2206_);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__6);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
lean_inc_ref(v_b_2207_);
v___x_2301_ = l_Lean_MessageData_ofExpr(v_b_2207_);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__8);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_inc_ref(v_eq_2205_);
v___x_2305_ = l_Lean_MessageData_ofExpr(v_eq_2205_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__10);
v___x_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = l_Lean_MessageData_ofExpr(v___x_2277_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__12);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_MessageData_ofExpr(v___x_2278_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__14);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Nat_reprFast(v_a_2295_);
v___x_2318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
v___x_2319_ = l_Lean_MessageData_ofFormat(v___x_2318_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_2290_, v___x_2320_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___x_2324_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2323_, v___x_2271_, v_fst_2250_, v_snd_2251_, v___x_2274_, v_a_2322_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v___y_2221_ = v___x_2324_;
goto v___jp_2220_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2280_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2325_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2321_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2321_);
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
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2333_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2294_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2294_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2341_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2293_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2293_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_unbox(v_a_2280_);
lean_dec(v_a_2280_);
v___x_2289_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__1(v___x_2288_, v___x_2271_, v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2287_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
v___y_2221_ = v___x_2289_;
goto v___jp_2220_;
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_a_2280_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
v___x_2349_ = lean_box(0);
v___x_2350_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2272_, v___x_2349_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
v___y_2221_ = v___x_2350_;
goto v___jp_2220_;
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v___x_2277_);
lean_dec(v___x_2274_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
lean_dec_ref(v_b_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_eq_2205_);
lean_dec(v___y_2204_);
v_a_2351_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2279_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2279_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___lam__0(v_fst_2250_, v_snd_2251_, v___x_2274_, v___x_2272_, v___x_2359_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_snd_2251_);
lean_dec(v_fst_2250_);
v___y_2221_ = v___x_2360_;
goto v___jp_2220_;
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2257_ = lean_unsigned_to_nat(2u);
v___x_2258_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set_uint8(v___x_2258_, sizeof(void*)*1, v___y_2256_);
lean_ctor_set_uint8(v___x_2258_, sizeof(void*)*1 + 1, v___y_2256_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
if (v_isShared_2254_ == 0)
{
v___x_2261_ = v___x_2253_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_fst_2250_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_snd_2251_);
v___x_2261_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2261_);
v___x_2263_ = v___x_2248_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_fst_2246_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2263_);
lean_ctor_set(v___x_2243_, 0, v___x_2259_);
v___x_2265_ = v___x_2243_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
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
lean_object* v_a_2365_ = _args[0];
lean_object* v___y_2366_ = _args[1];
lean_object* v_eq_2367_ = _args[2];
lean_object* v_a_2368_ = _args[3];
lean_object* v_b_2369_ = _args[4];
lean_object* v_a_2370_ = _args[5];
lean_object* v___y_2371_ = _args[6];
lean_object* v___y_2372_ = _args[7];
lean_object* v___y_2373_ = _args[8];
lean_object* v___y_2374_ = _args[9];
lean_object* v___y_2375_ = _args[10];
lean_object* v___y_2376_ = _args[11];
lean_object* v___y_2377_ = _args[12];
lean_object* v___y_2378_ = _args[13];
lean_object* v___y_2379_ = _args[14];
lean_object* v___y_2380_ = _args[15];
lean_object* v___y_2381_ = _args[16];
_start:
{
uint8_t v_a_34491__boxed_2382_; lean_object* v_res_2383_; 
v_a_34491__boxed_2382_ = lean_unbox(v_a_2365_);
v_res_2383_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_34491__boxed_2382_, v___y_2366_, v_eq_2367_, v_a_2368_, v_b_2369_, v_a_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* v_a_2384_, lean_object* v_b_2385_, lean_object* v_eq_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2401_; 
lean_inc_ref(v_eq_2386_);
v___x_2401_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_eq_2386_, v_a_2387_, v_a_2391_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; uint8_t v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2403_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
lean_inc_ref(v_eq_2386_);
v___x_2404_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_eq_2386_, v_a_2387_, v_a_2391_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; uint8_t v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_unbox(v_a_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___y_2409_; lean_object* v_toGoalState_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2454_; 
v___x_2407_ = lean_st_ref_get(v_a_2387_);
v_toGoalState_2442_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v___x_2407_, 1);
lean_dec(v_unused_2455_);
v___x_2444_ = v___x_2407_;
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_toGoalState_2442_);
lean_dec(v___x_2407_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2454_;
goto v_resetjp_2443_;
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; 
v___x_2410_ = l_Lean_Expr_getAppNumArgs(v_a_2384_);
v___x_2411_ = lean_box(0);
lean_inc_ref(v_b_2385_);
lean_inc_ref(v_a_2384_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v_a_2384_);
lean_ctor_set(v___x_2412_, 1, v_b_2385_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2411_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_unbox(v_a_2405_);
v___x_2416_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v___x_2415_, v___y_2409_, v_eq_2386_, v_a_2384_, v_b_2385_, v___x_2414_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2433_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2433_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_fst_2421_; 
v_fst_2421_ = lean_ctor_get(v_a_2417_, 0);
lean_inc(v_fst_2421_);
lean_dec(v_a_2417_);
if (lean_obj_tag(v_fst_2421_) == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2427_; 
v___x_2422_ = lean_unsigned_to_nat(2u);
v___x_2423_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
v___x_2424_ = lean_unbox(v_a_2405_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___x_2424_);
v___x_2425_ = lean_unbox(v_a_2405_);
lean_dec(v_a_2405_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1 + 1, v___x_2425_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2423_);
v___x_2427_ = v___x_2419_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2423_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2431_; 
lean_dec(v_a_2405_);
v_val_2429_ = lean_ctor_get(v_fst_2421_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v_fst_2421_, 1);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_val_2429_);
v___x_2431_ = v___x_2419_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_val_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2405_);
v_a_2434_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2416_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2416_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
v_resetjp_2443_:
{
lean_object* v_split_2446_; lean_object* v_argPosMap_2447_; lean_object* v___x_2449_; 
v_split_2446_ = lean_ctor_get(v_toGoalState_2442_, 15);
lean_inc_ref(v_split_2446_);
lean_dec_ref(v_toGoalState_2442_);
v_argPosMap_2447_ = lean_ctor_get(v_split_2446_, 6);
lean_inc_ref(v_argPosMap_2447_);
lean_dec_ref(v_split_2446_);
lean_inc_ref(v_b_2385_);
lean_inc_ref(v_a_2384_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v_b_2385_);
lean_ctor_set(v___x_2444_, 0, v_a_2384_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2384_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_b_2385_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_argPosMap_2447_, v___x_2449_);
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_argPosMap_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_box(0);
v___y_2409_ = v___x_2451_;
goto v___jp_2408_;
}
else
{
lean_object* v_val_2452_; 
v_val_2452_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v___x_2450_, 1);
v___y_2409_ = v_val_2452_;
goto v___jp_2408_;
}
}
}
}
else
{
lean_dec(v_a_2405_);
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
goto v___jp_2398_;
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
v_a_2456_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2404_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2404_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
goto v___jp_2398_;
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_eq_2386_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_a_2384_);
v_a_2464_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2401_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2401_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
v___jp_2398_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* v_a_2472_, lean_object* v_b_2473_, lean_object* v_eq_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2472_, v_b_2473_, v_eq_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec(v_a_2475_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(uint8_t v_a_2487_, lean_object* v___y_2488_, lean_object* v_eq_2489_, lean_object* v_a_2490_, lean_object* v_b_2491_, lean_object* v_inst_2492_, lean_object* v_a_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(v_a_2487_, v___y_2488_, v_eq_2489_, v_a_2490_, v_b_2491_, v_a_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args){
lean_object* v_a_2506_ = _args[0];
lean_object* v___y_2507_ = _args[1];
lean_object* v_eq_2508_ = _args[2];
lean_object* v_a_2509_ = _args[3];
lean_object* v_b_2510_ = _args[4];
lean_object* v_inst_2511_ = _args[5];
lean_object* v_a_2512_ = _args[6];
lean_object* v___y_2513_ = _args[7];
lean_object* v___y_2514_ = _args[8];
lean_object* v___y_2515_ = _args[9];
lean_object* v___y_2516_ = _args[10];
lean_object* v___y_2517_ = _args[11];
lean_object* v___y_2518_ = _args[12];
lean_object* v___y_2519_ = _args[13];
lean_object* v___y_2520_ = _args[14];
lean_object* v___y_2521_ = _args[15];
lean_object* v___y_2522_ = _args[16];
lean_object* v___y_2523_ = _args[17];
_start:
{
uint8_t v_a_34972__boxed_2524_; lean_object* v_res_2525_; 
v_a_34972__boxed_2524_ = lean_unbox(v_a_2506_);
v_res_2525_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(v_a_34972__boxed_2524_, v___y_2507_, v_eq_2508_, v_a_2509_, v_b_2510_, v_inst_2511_, v_a_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(lean_object* v_00_u03b2_2526_, lean_object* v_m_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___redArg(v_m_2527_, v_a_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1___boxed(lean_object* v_00_u03b2_2530_, lean_object* v_m_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1(v_00_u03b2_2530_, v_m_2531_, v_a_2532_);
lean_dec_ref(v_a_2532_);
lean_dec_ref(v_m_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(lean_object* v_00_u03b2_2534_, lean_object* v_a_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___redArg(v_a_2535_, v_x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2538_, lean_object* v_a_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__1_spec__1(v_00_u03b2_2538_, v_a_2539_, v_x_2540_);
lean_dec(v_x_2540_);
lean_dec_ref(v_a_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* v_imp_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2556_; 
lean_inc_ref(v_imp_2542_);
v___x_2556_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_imp_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
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
v___x_2559_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_imp_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
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
lean_object* v_binderType_2582_; lean_object* v_body_2583_; lean_object* v___x_2584_; 
v_binderType_2582_ = lean_ctor_get(v_imp_2542_, 1);
lean_inc_ref_n(v_binderType_2582_, 2);
v_body_2583_ = lean_ctor_get(v_imp_2542_, 2);
lean_inc_ref(v_body_2583_);
lean_dec_ref(v_imp_2542_);
v___x_2584_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_2582_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = lean_unbox(v_a_2585_);
lean_dec(v_a_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_binderType_2582_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2624_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2624_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2624_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_unbox(v_a_2588_);
if (v___x_2600_ == 0)
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Expr_hasLooseBVars(v_body_2583_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_inc_ref(v_body_2583_);
v___x_2602_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_body_2583_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; uint8_t v___x_2604_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = lean_unbox(v_a_2603_);
lean_dec(v_a_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_2583_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; uint8_t v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2607_ == 0)
{
goto v___jp_2592_;
}
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
goto v___jp_2550_;
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
v_a_2608_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2605_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2605_);
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
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
goto v___jp_2550_;
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
v_a_2616_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2602_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2602_);
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
else
{
lean_dec_ref(v_body_2583_);
goto v___jp_2592_;
}
}
else
{
lean_del_object(v___x_2590_);
lean_dec(v_a_2588_);
lean_dec_ref(v_body_2583_);
goto v___jp_2553_;
}
v___jp_2592_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2598_; 
v___x_2593_ = lean_unsigned_to_nat(2u);
v___x_2594_ = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___x_2595_ = lean_unbox(v_a_2588_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2595_);
v___x_2596_ = lean_unbox(v_a_2588_);
lean_dec(v_a_2588_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1 + 1, v___x_2596_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2594_);
v___x_2598_ = v___x_2590_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2594_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_body_2583_);
v_a_2625_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2587_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2587_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_dec_ref(v_body_2583_);
lean_dec_ref(v_binderType_2582_);
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_body_2583_);
lean_dec_ref(v_binderType_2582_);
v_a_2633_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2584_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2584_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_imp_2542_);
v_a_2641_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2556_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2556_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
v___jp_2553_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* v_imp_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* v_imp_2658_, lean_object* v_h_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_imp_2658_, v_a_2660_, v_a_2664_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* v_imp_2672_, lean_object* v_h_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(v_imp_2672_, v_h_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec(v_a_2674_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* v_s_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
switch(lean_obj_tag(v_s_2686_))
{
case 0:
{
lean_object* v_e_2698_; lean_object* v___x_2699_; 
v_e_2698_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_e_2698_);
lean_dec_ref_known(v_s_2686_, 2);
v___x_2699_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(v_e_2698_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2699_;
}
case 1:
{
lean_object* v_e_2700_; lean_object* v___x_2701_; 
v_e_2700_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_e_2700_);
lean_dec_ref_known(v_s_2686_, 2);
v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(v_e_2700_, v_a_2687_, v_a_2691_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2701_;
}
default: 
{
lean_object* v_a_2702_; lean_object* v_b_2703_; lean_object* v_eq_2704_; lean_object* v___x_2705_; 
v_a_2702_ = lean_ctor_get(v_s_2686_, 0);
lean_inc_ref(v_a_2702_);
v_b_2703_ = lean_ctor_get(v_s_2686_, 1);
lean_inc_ref(v_b_2703_);
v_eq_2704_ = lean_ctor_get(v_s_2686_, 3);
lean_inc_ref(v_eq_2704_);
lean_dec_ref_known(v_s_2686_, 5);
v___x_2705_ = l_Lean_Meta_Grind_checkSplitInfoArgStatus(v_a_2702_, v_b_2703_, v_eq_2704_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus___boxed(lean_object* v_s_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Meta_Grind_checkSplitStatus(v_s_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec(v_a_2707_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_obj_tag_nat(v_x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl___boxed(lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorIdx___impl(v_x_2721_);
lean_dec(v_x_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(lean_object* v_t_2723_, lean_object* v_k_2724_){
_start:
{
if (lean_obj_tag(v_t_2723_) == 0)
{
return v_k_2724_;
}
else
{
lean_object* v_c_2725_; lean_object* v_numCases_2726_; uint8_t v_isRec_2727_; uint8_t v_tryPostpone_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_c_2725_ = lean_ctor_get(v_t_2723_, 0);
lean_inc_ref(v_c_2725_);
v_numCases_2726_ = lean_ctor_get(v_t_2723_, 1);
lean_inc(v_numCases_2726_);
v_isRec_2727_ = lean_ctor_get_uint8(v_t_2723_, sizeof(void*)*2);
v_tryPostpone_2728_ = lean_ctor_get_uint8(v_t_2723_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_t_2723_, 2);
v___x_2729_ = lean_box(v_isRec_2727_);
v___x_2730_ = lean_box(v_tryPostpone_2728_);
v___x_2731_ = lean_apply_4(v_k_2724_, v_c_2725_, v_numCases_2726_, v___x_2729_, v___x_2730_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(lean_object* v_motive_2732_, lean_object* v_ctorIdx_2733_, lean_object* v_t_2734_, lean_object* v_h_2735_, lean_object* v_k_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2734_, v_k_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___boxed(lean_object* v_motive_2738_, lean_object* v_ctorIdx_2739_, lean_object* v_t_2740_, lean_object* v_h_2741_, lean_object* v_k_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim(v_motive_2738_, v_ctorIdx_2739_, v_t_2740_, v_h_2741_, v_k_2742_);
lean_dec(v_ctorIdx_2739_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim___redArg(lean_object* v_t_2744_, lean_object* v_none_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2744_, v_none_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_none_elim(lean_object* v_motive_2747_, lean_object* v_t_2748_, lean_object* v_h_2749_, lean_object* v_none_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2748_, v_none_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim___redArg(lean_object* v_t_2752_, lean_object* v_some_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2752_, v_some_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_some_elim(lean_object* v_motive_2755_, lean_object* v_t_2756_, lean_object* v_h_2757_, lean_object* v_some_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_SplitCandidate_ctorElim___redArg(v_t_2756_, v_some_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(uint64_t v_a_2760_, lean_object* v_as_2761_, size_t v_i_2762_, size_t v_stop_2763_){
_start:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_eq(v_i_2762_, v_stop_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = lean_array_uget_borrowed(v_as_2761_, v_i_2762_);
v___x_2766_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_2765_, v_a_2760_);
if (v___x_2766_ == 0)
{
size_t v___x_2767_; size_t v___x_2768_; 
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2762_, v___x_2767_);
v_i_2762_ = v___x_2768_;
goto _start;
}
else
{
return v___x_2766_;
}
}
else
{
uint8_t v___x_2770_; 
v___x_2770_ = 0;
return v___x_2770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0___boxed(lean_object* v_a_2771_, lean_object* v_as_2772_, lean_object* v_i_2773_, lean_object* v_stop_2774_){
_start:
{
uint64_t v_a_2507__boxed_2775_; size_t v_i_boxed_2776_; size_t v_stop_boxed_2777_; uint8_t v_res_2778_; lean_object* v_r_2779_; 
v_a_2507__boxed_2775_ = lean_unbox_uint64(v_a_2771_);
lean_dec_ref(v_a_2771_);
v_i_boxed_2776_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_stop_boxed_2777_ = lean_unbox_usize(v_stop_2774_);
lean_dec(v_stop_2774_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v_a_2507__boxed_2775_, v_as_2772_, v_i_boxed_2776_, v_stop_boxed_2777_);
lean_dec_ref(v_as_2772_);
v_r_2779_ = lean_box(v_res_2778_);
return v_r_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(lean_object* v_c_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_2782_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2835_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2835_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2835_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
if (lean_obj_tag(v_a_2792_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2797_; 
lean_del_object(v___x_2794_);
v_val_2796_ = lean_ctor_get(v_a_2792_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v_a_2792_, 1);
v___x_2797_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2821_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2821_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2821_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = lean_array_get_size(v_val_2796_);
v___x_2804_ = lean_nat_dec_lt(v___x_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
lean_dec(v_a_2798_);
lean_dec(v_val_2796_);
v___x_2805_ = lean_box(v___x_2804_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2805_);
v___x_2807_ = v___x_2800_;
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
else
{
if (v___x_2804_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_dec(v_a_2798_);
lean_dec(v_val_2796_);
v___x_2809_ = lean_box(v___x_2804_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2809_);
v___x_2811_ = v___x_2800_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
size_t v___x_2813_; size_t v___x_2814_; uint64_t v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2813_ = ((size_t)0ULL);
v___x_2814_ = lean_usize_of_nat(v___x_2803_);
v___x_2815_ = lean_unbox_uint64(v_a_2798_);
lean_dec(v_a_2798_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs_spec__0(v___x_2815_, v_val_2796_, v___x_2813_, v___x_2814_);
lean_dec(v_val_2796_);
v___x_2817_ = lean_box(v___x_2816_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2817_);
v___x_2819_ = v___x_2800_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_val_2796_);
v_a_2822_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2797_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2797_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
lean_dec(v_a_2792_);
v___x_2830_ = 1;
v___x_2831_ = lean_box(v___x_2830_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2831_);
v___x_2833_ = v___x_2794_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_a_2836_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2791_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2791_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs___boxed(lean_object* v_c_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_c_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_c_2844_);
return v_res_2855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0));
v___x_2858_ = l_Lean_stringToMessageData(v___x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* v_cs_2859_, lean_object* v_c_x3f_2860_, lean_object* v_cs_x27_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
if (lean_obj_tag(v_cs_2859_) == 0)
{
lean_object* v___x_2873_; lean_object* v_toGoalState_2874_; lean_object* v_split_2875_; lean_object* v_mvarId_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2988_; 
v___x_2873_ = lean_st_ref_take(v_a_2862_);
v_toGoalState_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_toGoalState_2874_);
v_split_2875_ = lean_ctor_get(v_toGoalState_2874_, 15);
lean_inc_ref(v_split_2875_);
v_mvarId_2876_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2989_);
v___x_2878_ = v___x_2873_;
v_isShared_2879_ = v_isSharedCheck_2988_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_mvarId_2876_);
lean_dec(v___x_2873_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2988_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_nextDeclIdx_2880_; lean_object* v_enodeMap_2881_; lean_object* v_exprs_2882_; lean_object* v_parents_2883_; lean_object* v_congrTable_2884_; lean_object* v_appMap_2885_; lean_object* v_indicesFound_2886_; lean_object* v_toProcess_2887_; lean_object* v_internalizing_2888_; uint8_t v_inconsistent_2889_; lean_object* v_nextIdx_2890_; lean_object* v_newRawFacts_2891_; lean_object* v_facts_2892_; lean_object* v_extThms_2893_; lean_object* v_ematch_2894_; lean_object* v_inj_2895_; lean_object* v_clean_2896_; lean_object* v_sstates_2897_; lean_object* v_goalStack_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2986_; 
v_nextDeclIdx_2880_ = lean_ctor_get(v_toGoalState_2874_, 0);
v_enodeMap_2881_ = lean_ctor_get(v_toGoalState_2874_, 1);
v_exprs_2882_ = lean_ctor_get(v_toGoalState_2874_, 2);
v_parents_2883_ = lean_ctor_get(v_toGoalState_2874_, 3);
v_congrTable_2884_ = lean_ctor_get(v_toGoalState_2874_, 4);
v_appMap_2885_ = lean_ctor_get(v_toGoalState_2874_, 5);
v_indicesFound_2886_ = lean_ctor_get(v_toGoalState_2874_, 6);
v_toProcess_2887_ = lean_ctor_get(v_toGoalState_2874_, 7);
v_internalizing_2888_ = lean_ctor_get(v_toGoalState_2874_, 8);
v_inconsistent_2889_ = lean_ctor_get_uint8(v_toGoalState_2874_, sizeof(void*)*19);
v_nextIdx_2890_ = lean_ctor_get(v_toGoalState_2874_, 9);
v_newRawFacts_2891_ = lean_ctor_get(v_toGoalState_2874_, 10);
v_facts_2892_ = lean_ctor_get(v_toGoalState_2874_, 11);
v_extThms_2893_ = lean_ctor_get(v_toGoalState_2874_, 12);
v_ematch_2894_ = lean_ctor_get(v_toGoalState_2874_, 13);
v_inj_2895_ = lean_ctor_get(v_toGoalState_2874_, 14);
v_clean_2896_ = lean_ctor_get(v_toGoalState_2874_, 16);
v_sstates_2897_ = lean_ctor_get(v_toGoalState_2874_, 17);
v_goalStack_2898_ = lean_ctor_get(v_toGoalState_2874_, 18);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_toGoalState_2874_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_toGoalState_2874_, 15);
lean_dec(v_unused_2987_);
v___x_2900_ = v_toGoalState_2874_;
v_isShared_2901_ = v_isSharedCheck_2986_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_goalStack_2898_);
lean_inc(v_sstates_2897_);
lean_inc(v_clean_2896_);
lean_inc(v_inj_2895_);
lean_inc(v_ematch_2894_);
lean_inc(v_extThms_2893_);
lean_inc(v_facts_2892_);
lean_inc(v_newRawFacts_2891_);
lean_inc(v_nextIdx_2890_);
lean_inc(v_internalizing_2888_);
lean_inc(v_toProcess_2887_);
lean_inc(v_indicesFound_2886_);
lean_inc(v_appMap_2885_);
lean_inc(v_congrTable_2884_);
lean_inc(v_parents_2883_);
lean_inc(v_exprs_2882_);
lean_inc(v_enodeMap_2881_);
lean_inc(v_nextDeclIdx_2880_);
lean_dec(v_toGoalState_2874_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2986_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_num_2902_; lean_object* v_added_2903_; lean_object* v_resolved_2904_; lean_object* v_trace_2905_; lean_object* v_lookaheads_2906_; lean_object* v_argPosMap_2907_; lean_object* v_argsAt_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2984_; 
v_num_2902_ = lean_ctor_get(v_split_2875_, 0);
v_added_2903_ = lean_ctor_get(v_split_2875_, 2);
v_resolved_2904_ = lean_ctor_get(v_split_2875_, 3);
v_trace_2905_ = lean_ctor_get(v_split_2875_, 4);
v_lookaheads_2906_ = lean_ctor_get(v_split_2875_, 5);
v_argPosMap_2907_ = lean_ctor_get(v_split_2875_, 6);
v_argsAt_2908_ = lean_ctor_get(v_split_2875_, 7);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_split_2875_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_split_2875_, 1);
lean_dec(v_unused_2985_);
v___x_2910_ = v_split_2875_;
v_isShared_2911_ = v_isSharedCheck_2984_;
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
lean_dec(v_split_2875_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2984_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = l_List_reverse___redArg(v_cs_x27_2861_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_num_2902_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_added_2903_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_resolved_2904_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v_trace_2905_);
lean_ctor_set(v_reuseFailAlloc_2983_, 5, v_lookaheads_2906_);
lean_ctor_set(v_reuseFailAlloc_2983_, 6, v_argPosMap_2907_);
lean_ctor_set(v_reuseFailAlloc_2983_, 7, v_argsAt_2908_);
v___x_2914_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 15, v___x_2914_);
v___x_2916_ = v___x_2900_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_nextDeclIdx_2880_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_enodeMap_2881_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_exprs_2882_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_parents_2883_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_congrTable_2884_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_appMap_2885_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_indicesFound_2886_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_toProcess_2887_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_internalizing_2888_);
lean_ctor_set(v_reuseFailAlloc_2982_, 9, v_nextIdx_2890_);
lean_ctor_set(v_reuseFailAlloc_2982_, 10, v_newRawFacts_2891_);
lean_ctor_set(v_reuseFailAlloc_2982_, 11, v_facts_2892_);
lean_ctor_set(v_reuseFailAlloc_2982_, 12, v_extThms_2893_);
lean_ctor_set(v_reuseFailAlloc_2982_, 13, v_ematch_2894_);
lean_ctor_set(v_reuseFailAlloc_2982_, 14, v_inj_2895_);
lean_ctor_set(v_reuseFailAlloc_2982_, 15, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2982_, 16, v_clean_2896_);
lean_ctor_set(v_reuseFailAlloc_2982_, 17, v_sstates_2897_);
lean_ctor_set(v_reuseFailAlloc_2982_, 18, v_goalStack_2898_);
lean_ctor_set_uint8(v_reuseFailAlloc_2982_, sizeof(void*)*19, v_inconsistent_2889_);
v___x_2916_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2916_);
v___x_2918_ = v___x_2878_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_mvarId_2876_);
v___x_2918_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_st_ref_put(v_a_2862_, v___x_2918_);
if (lean_obj_tag(v_c_x3f_2860_) == 1)
{
lean_object* v___x_2920_; lean_object* v_toGoalState_2921_; lean_object* v_ematch_2922_; lean_object* v_mvarId_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2978_; 
v___x_2920_ = lean_st_ref_take(v_a_2862_);
v_toGoalState_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_toGoalState_2921_);
v_ematch_2922_ = lean_ctor_get(v_toGoalState_2921_, 13);
lean_inc_ref(v_ematch_2922_);
v_mvarId_2923_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2979_);
v___x_2925_ = v___x_2920_;
v_isShared_2926_ = v_isSharedCheck_2978_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_mvarId_2923_);
lean_dec(v___x_2920_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2978_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_nextDeclIdx_2927_; lean_object* v_enodeMap_2928_; lean_object* v_exprs_2929_; lean_object* v_parents_2930_; lean_object* v_congrTable_2931_; lean_object* v_appMap_2932_; lean_object* v_indicesFound_2933_; lean_object* v_toProcess_2934_; lean_object* v_internalizing_2935_; uint8_t v_inconsistent_2936_; lean_object* v_nextIdx_2937_; lean_object* v_newRawFacts_2938_; lean_object* v_facts_2939_; lean_object* v_extThms_2940_; lean_object* v_inj_2941_; lean_object* v_split_2942_; lean_object* v_clean_2943_; lean_object* v_sstates_2944_; lean_object* v_goalStack_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2976_; 
v_nextDeclIdx_2927_ = lean_ctor_get(v_toGoalState_2921_, 0);
v_enodeMap_2928_ = lean_ctor_get(v_toGoalState_2921_, 1);
v_exprs_2929_ = lean_ctor_get(v_toGoalState_2921_, 2);
v_parents_2930_ = lean_ctor_get(v_toGoalState_2921_, 3);
v_congrTable_2931_ = lean_ctor_get(v_toGoalState_2921_, 4);
v_appMap_2932_ = lean_ctor_get(v_toGoalState_2921_, 5);
v_indicesFound_2933_ = lean_ctor_get(v_toGoalState_2921_, 6);
v_toProcess_2934_ = lean_ctor_get(v_toGoalState_2921_, 7);
v_internalizing_2935_ = lean_ctor_get(v_toGoalState_2921_, 8);
v_inconsistent_2936_ = lean_ctor_get_uint8(v_toGoalState_2921_, sizeof(void*)*19);
v_nextIdx_2937_ = lean_ctor_get(v_toGoalState_2921_, 9);
v_newRawFacts_2938_ = lean_ctor_get(v_toGoalState_2921_, 10);
v_facts_2939_ = lean_ctor_get(v_toGoalState_2921_, 11);
v_extThms_2940_ = lean_ctor_get(v_toGoalState_2921_, 12);
v_inj_2941_ = lean_ctor_get(v_toGoalState_2921_, 14);
v_split_2942_ = lean_ctor_get(v_toGoalState_2921_, 15);
v_clean_2943_ = lean_ctor_get(v_toGoalState_2921_, 16);
v_sstates_2944_ = lean_ctor_get(v_toGoalState_2921_, 17);
v_goalStack_2945_ = lean_ctor_get(v_toGoalState_2921_, 18);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_toGoalState_2921_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_toGoalState_2921_, 13);
lean_dec(v_unused_2977_);
v___x_2947_ = v_toGoalState_2921_;
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_goalStack_2945_);
lean_inc(v_sstates_2944_);
lean_inc(v_clean_2943_);
lean_inc(v_split_2942_);
lean_inc(v_inj_2941_);
lean_inc(v_extThms_2940_);
lean_inc(v_facts_2939_);
lean_inc(v_newRawFacts_2938_);
lean_inc(v_nextIdx_2937_);
lean_inc(v_internalizing_2935_);
lean_inc(v_toProcess_2934_);
lean_inc(v_indicesFound_2933_);
lean_inc(v_appMap_2932_);
lean_inc(v_congrTable_2931_);
lean_inc(v_parents_2930_);
lean_inc(v_exprs_2929_);
lean_inc(v_enodeMap_2928_);
lean_inc(v_nextDeclIdx_2927_);
lean_dec(v_toGoalState_2921_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_thmMap_2949_; lean_object* v_gmt_2950_; lean_object* v_thms_2951_; lean_object* v_newThms_2952_; lean_object* v_numInstances_2953_; lean_object* v_numDelayedInstances_2954_; lean_object* v_preInstances_2955_; lean_object* v_nextThmIdx_2956_; lean_object* v_matchEqNames_2957_; lean_object* v_delayedThmInsts_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2974_; 
v_thmMap_2949_ = lean_ctor_get(v_ematch_2922_, 0);
v_gmt_2950_ = lean_ctor_get(v_ematch_2922_, 1);
v_thms_2951_ = lean_ctor_get(v_ematch_2922_, 2);
v_newThms_2952_ = lean_ctor_get(v_ematch_2922_, 3);
v_numInstances_2953_ = lean_ctor_get(v_ematch_2922_, 4);
v_numDelayedInstances_2954_ = lean_ctor_get(v_ematch_2922_, 5);
v_preInstances_2955_ = lean_ctor_get(v_ematch_2922_, 7);
v_nextThmIdx_2956_ = lean_ctor_get(v_ematch_2922_, 8);
v_matchEqNames_2957_ = lean_ctor_get(v_ematch_2922_, 9);
v_delayedThmInsts_2958_ = lean_ctor_get(v_ematch_2922_, 10);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_ematch_2922_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v_ematch_2922_, 6);
lean_dec(v_unused_2975_);
v___x_2960_ = v_ematch_2922_;
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
lean_dec(v_ematch_2922_);
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
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_nextDeclIdx_2927_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_enodeMap_2928_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_exprs_2929_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v_parents_2930_);
lean_ctor_set(v_reuseFailAlloc_2972_, 4, v_congrTable_2931_);
lean_ctor_set(v_reuseFailAlloc_2972_, 5, v_appMap_2932_);
lean_ctor_set(v_reuseFailAlloc_2972_, 6, v_indicesFound_2933_);
lean_ctor_set(v_reuseFailAlloc_2972_, 7, v_toProcess_2934_);
lean_ctor_set(v_reuseFailAlloc_2972_, 8, v_internalizing_2935_);
lean_ctor_set(v_reuseFailAlloc_2972_, 9, v_nextIdx_2937_);
lean_ctor_set(v_reuseFailAlloc_2972_, 10, v_newRawFacts_2938_);
lean_ctor_set(v_reuseFailAlloc_2972_, 11, v_facts_2939_);
lean_ctor_set(v_reuseFailAlloc_2972_, 12, v_extThms_2940_);
lean_ctor_set(v_reuseFailAlloc_2972_, 13, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2972_, 14, v_inj_2941_);
lean_ctor_set(v_reuseFailAlloc_2972_, 15, v_split_2942_);
lean_ctor_set(v_reuseFailAlloc_2972_, 16, v_clean_2943_);
lean_ctor_set(v_reuseFailAlloc_2972_, 17, v_sstates_2944_);
lean_ctor_set(v_reuseFailAlloc_2972_, 18, v_goalStack_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_2972_, sizeof(void*)*19, v_inconsistent_2936_);
v___x_2966_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2966_);
v___x_2968_ = v___x_2925_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_mvarId_2923_);
v___x_2968_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_st_ref_put(v_a_2862_, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_c_x3f_2860_);
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
lean_ctor_set(v___x_2980_, 0, v_c_x3f_2860_);
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
v_head_2990_ = lean_ctor_get(v_cs_2859_, 0);
v_tail_2991_ = lean_ctor_get(v_cs_2859_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_cs_2859_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_2993_ = v_cs_2859_;
v_isShared_2994_ = v_isSharedCheck_3211_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_tail_2991_);
lean_inc(v_head_2990_);
lean_dec(v_cs_2859_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3211_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; uint8_t v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; uint8_t v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; uint8_t v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___x_3103_; 
v___x_3103_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkAnchorRefs(v_head_2990_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
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
v_cs_2859_ = v_tail_2991_;
goto _start;
}
else
{
lean_object* v_toCold_3107_; lean_object* v_options_3108_; lean_object* v_inheritedTraceOptions_3109_; uint8_t v_hasTrace_3110_; uint8_t v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; uint8_t v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; uint8_t v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; 
v_toCold_3107_ = lean_ctor_get(v_a_2870_, 0);
v_options_3108_ = lean_ctor_get(v_toCold_3107_, 2);
v_inheritedTraceOptions_3109_ = lean_ctor_get(v_toCold_3107_, 11);
v_hasTrace_3110_ = lean_ctor_get_uint8(v_options_3108_, sizeof(void*)*1);
v___x_3111_ = 0;
if (v_hasTrace_3110_ == 0)
{
v___y_3137_ = v_a_2862_;
v___y_3138_ = v_a_2863_;
v___y_3139_ = v_a_2864_;
v___y_3140_ = v_a_2865_;
v___y_3141_ = v_a_2866_;
v___y_3142_ = v_a_2867_;
v___y_3143_ = v_a_2868_;
v___y_3144_ = v_a_2869_;
v___y_3145_ = v_a_2870_;
v___y_3146_ = v_a_2871_;
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
v___y_3137_ = v_a_2862_;
v___y_3138_ = v_a_2863_;
v___y_3139_ = v_a_2864_;
v___y_3140_ = v_a_2865_;
v___y_3141_ = v_a_2866_;
v___y_3142_ = v_a_2867_;
v___y_3143_ = v_a_2868_;
v___y_3144_ = v_a_2869_;
v___y_3145_ = v_a_2870_;
v___y_3146_ = v_a_2871_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Meta_Grind_updateLastTag(v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
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
v___x_3186_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_3178_, v___x_3185_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
v___y_3137_ = v_a_2862_;
v___y_3138_ = v_a_2863_;
v___y_3139_ = v_a_2864_;
v___y_3140_ = v_a_2865_;
v___y_3141_ = v_a_2866_;
v___y_3142_ = v_a_2867_;
v___y_3143_ = v_a_2868_;
v___y_3144_ = v_a_2869_;
v___y_3145_ = v_a_2870_;
v___y_3146_ = v_a_2871_;
goto v___jp_3136_;
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
if (lean_obj_tag(v_c_x3f_2860_) == 0)
{
lean_object* v___x_3127_; 
lean_del_object(v___x_2993_);
v___x_3127_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3127_, 0, v_head_2990_);
lean_ctor_set(v___x_3127_, 1, v___y_3113_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*2, v___y_3117_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*2 + 1, v___y_3121_);
v_cs_2859_ = v_tail_2991_;
v_c_x3f_2860_ = v___x_3127_;
v_a_2862_ = v___y_3114_;
v_a_2863_ = v___y_3122_;
v_a_2864_ = v___y_3120_;
v_a_2865_ = v___y_3116_;
v_a_2866_ = v___y_3118_;
v_a_2867_ = v___y_3115_;
v_a_2868_ = v___y_3123_;
v_a_2869_ = v___y_3119_;
v_a_2870_ = v___y_3124_;
v_a_2871_ = v___y_3125_;
goto _start;
}
else
{
uint8_t v_tryPostpone_3129_; 
v_tryPostpone_3129_ = lean_ctor_get_uint8(v_c_x3f_2860_, sizeof(void*)*2 + 1);
if (v_tryPostpone_3129_ == 0)
{
if (v___y_3121_ == 0)
{
lean_object* v_c_3130_; lean_object* v_numCases_3131_; 
v_c_3130_ = lean_ctor_get(v_c_x3f_2860_, 0);
v_numCases_3131_ = lean_ctor_get(v_c_x3f_2860_, 1);
lean_inc(v_numCases_3131_);
lean_inc_ref(v_c_3130_);
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v_c_3130_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3118_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v_numCases_3131_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___x_3111_;
goto v___jp_3084_;
}
else
{
lean_dec(v___y_3113_);
v___y_2996_ = v___y_3114_;
v___y_2997_ = v___y_3115_;
v___y_2998_ = v___y_3116_;
v___y_2999_ = v___y_3122_;
v___y_3000_ = v___y_3119_;
v___y_3001_ = v___y_3123_;
v___y_3002_ = v___y_3118_;
v___y_3003_ = v___y_3125_;
v___y_3004_ = v___y_3124_;
v___y_3005_ = v___y_3120_;
goto v___jp_2995_;
}
}
else
{
if (v___y_3121_ == 0)
{
lean_object* v_c_3132_; 
lean_del_object(v___x_2993_);
v_c_3132_ = lean_ctor_get(v_c_x3f_2860_, 0);
lean_inc_ref(v_c_3132_);
lean_dec_ref_known(v_c_x3f_2860_, 2);
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v_c_3132_;
v___y_3014_ = v___y_3115_;
v___y_3015_ = v___y_3116_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3124_;
goto v___jp_3010_;
}
else
{
if (v___y_3126_ == 0)
{
lean_object* v_c_3133_; lean_object* v_numCases_3134_; 
v_c_3133_ = lean_ctor_get(v_c_x3f_2860_, 0);
v_numCases_3134_ = lean_ctor_get(v_c_x3f_2860_, 1);
lean_inc(v_numCases_3134_);
lean_inc_ref(v_c_3133_);
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3114_;
v___y_3087_ = v_c_3133_;
v___y_3088_ = v___y_3115_;
v___y_3089_ = v___y_3116_;
v___y_3090_ = v___y_3117_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3118_;
v___y_3093_ = v___y_3120_;
v___y_3094_ = v_numCases_3134_;
v___y_3095_ = v___y_3121_;
v___y_3096_ = v___y_3122_;
v___y_3097_ = v___y_3123_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3126_;
goto v___jp_3084_;
}
else
{
lean_object* v_c_3135_; 
lean_del_object(v___x_2993_);
v_c_3135_ = lean_ctor_get(v_c_x3f_2860_, 0);
lean_inc_ref(v_c_3135_);
lean_dec_ref_known(v_c_x3f_2860_, 2);
v___y_3011_ = v___y_3113_;
v___y_3012_ = v___y_3114_;
v___y_3013_ = v_c_3135_;
v___y_3014_ = v___y_3115_;
v___y_3015_ = v___y_3116_;
v___y_3016_ = v___y_3117_;
v___y_3017_ = v___y_3118_;
v___y_3018_ = v___y_3119_;
v___y_3019_ = v___y_3120_;
v___y_3020_ = v___y_3121_;
v___y_3021_ = v___y_3122_;
v___y_3022_ = v___y_3123_;
v___y_3023_ = v___y_3125_;
v___y_3024_ = v___y_3124_;
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
v_cs_2859_ = v_tail_2991_;
v_a_2862_ = v___y_3137_;
v_a_2863_ = v___y_3138_;
v_a_2864_ = v___y_3139_;
v_a_2865_ = v___y_3140_;
v_a_2866_ = v___y_3141_;
v_a_2867_ = v___y_3142_;
v_a_2868_ = v___y_3143_;
v_a_2869_ = v___y_3144_;
v_a_2870_ = v___y_3145_;
v_a_2871_ = v___y_3146_;
goto _start;
}
case 1:
{
lean_object* v___x_3150_; 
lean_del_object(v___x_2993_);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_head_2990_);
lean_ctor_set(v___x_3150_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2991_;
v_cs_x27_2861_ = v___x_3150_;
v_a_2862_ = v___y_3137_;
v_a_2863_ = v___y_3138_;
v_a_2864_ = v___y_3139_;
v_a_2865_ = v___y_3140_;
v_a_2866_ = v___y_3141_;
v_a_2867_ = v___y_3142_;
v_a_2868_ = v___y_3143_;
v_a_2869_ = v___y_3144_;
v_a_2870_ = v___y_3145_;
v_a_2871_ = v___y_3146_;
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
v___y_3113_ = v_numCases_3152_;
v___y_3114_ = v___y_3137_;
v___y_3115_ = v___y_3142_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v_isRec_3153_;
v___y_3118_ = v___y_3141_;
v___y_3119_ = v___y_3144_;
v___y_3120_ = v___y_3139_;
v___y_3121_ = v_tryPostpone_3154_;
v___y_3122_ = v___y_3138_;
v___y_3123_ = v___y_3143_;
v___y_3124_ = v___y_3145_;
v___y_3125_ = v___y_3146_;
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
v___y_3113_ = v_numCases_3152_;
v___y_3114_ = v___y_3137_;
v___y_3115_ = v___y_3142_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v_isRec_3153_;
v___y_3118_ = v___y_3141_;
v___y_3119_ = v___y_3144_;
v___y_3120_ = v___y_3139_;
v___y_3121_ = v_tryPostpone_3154_;
v___y_3122_ = v___y_3138_;
v___y_3123_ = v___y_3143_;
v___y_3124_ = v___y_3145_;
v___y_3125_ = v___y_3146_;
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
lean_ctor_set(v___x_3160_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2991_;
v_cs_x27_2861_ = v___x_3160_;
v_a_2862_ = v___y_3137_;
v_a_2863_ = v___y_3138_;
v_a_2864_ = v___y_3139_;
v_a_2865_ = v___y_3140_;
v_a_2866_ = v___y_3141_;
v_a_2867_ = v___y_3142_;
v_a_2868_ = v___y_3143_;
v_a_2869_ = v___y_3144_;
v_a_2870_ = v___y_3145_;
v_a_2871_ = v___y_3146_;
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
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
lean_ctor_set(v___x_2993_, 1, v_cs_x27_2861_);
v___x_3007_ = v___x_2993_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_head_2990_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_cs_x27_2861_);
v___x_3007_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
v_cs_2859_ = v_tail_2991_;
v_cs_x27_2861_ = v___x_3007_;
v_a_2862_ = v___y_2996_;
v_a_2863_ = v___y_2999_;
v_a_2864_ = v___y_3005_;
v_a_2865_ = v___y_2998_;
v_a_2866_ = v___y_3002_;
v_a_2867_ = v___y_2997_;
v_a_2868_ = v___y_3001_;
v_a_2869_ = v___y_3000_;
v_a_2870_ = v___y_3004_;
v_a_2871_ = v___y_3003_;
goto _start;
}
}
v___jp_3010_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3025_, 0, v_head_2990_);
lean_ctor_set(v___x_3025_, 1, v___y_3011_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*2, v___y_3016_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*2 + 1, v___y_3020_);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___y_3013_);
lean_ctor_set(v___x_3026_, 1, v_cs_x27_2861_);
v_cs_2859_ = v_tail_2991_;
v_c_x3f_2860_ = v___x_3025_;
v_cs_x27_2861_ = v___x_3026_;
v_a_2862_ = v___y_3012_;
v_a_2863_ = v___y_3021_;
v_a_2864_ = v___y_3019_;
v_a_2865_ = v___y_3015_;
v_a_2866_ = v___y_3017_;
v_a_2867_ = v___y_3014_;
v_a_2868_ = v___y_3022_;
v_a_2869_ = v___y_3018_;
v_a_2870_ = v___y_3024_;
v_a_2871_ = v___y_3023_;
goto _start;
}
v___jp_3028_:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v_head_2990_, v___y_3029_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = l_Lean_Meta_Grind_SplitInfo_getGeneration___redArg(v___y_3031_, v___y_3029_);
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
v___x_3049_ = lean_nat_dec_lt(v___y_3030_, v___y_3038_);
lean_dec(v___y_3038_);
if (v___x_3049_ == 0)
{
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
v___y_2996_ = v___y_3029_;
v___y_2997_ = v___y_3032_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3040_;
v___y_3000_ = v___y_3035_;
v___y_3001_ = v___y_3041_;
v___y_3002_ = v___y_3036_;
v___y_3003_ = v___y_3042_;
v___y_3004_ = v___y_3043_;
v___y_3005_ = v___y_3037_;
goto v___jp_2995_;
}
else
{
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2860_);
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3029_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3035_;
v___y_3019_ = v___y_3037_;
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
lean_dec(v___y_3038_);
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2860_);
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3029_;
v___y_3013_ = v___y_3031_;
v___y_3014_ = v___y_3032_;
v___y_3015_ = v___y_3033_;
v___y_3016_ = v___y_3034_;
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3035_;
v___y_3019_ = v___y_3037_;
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
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_del_object(v___x_2993_);
lean_dec(v_tail_2991_);
lean_dec(v_head_2990_);
lean_dec(v_cs_x27_2861_);
lean_dec(v_c_x3f_2860_);
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
v___x_3083_ = lean_nat_dec_lt(v___x_3082_, v___y_3076_);
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
v___y_3041_ = v___y_3079_;
v___y_3042_ = v___y_3081_;
v___y_3043_ = v___y_3080_;
goto v___jp_3028_;
}
else
{
lean_dec(v___y_3076_);
lean_del_object(v___x_2993_);
lean_dec(v_c_x3f_2860_);
v___y_3011_ = v___y_3068_;
v___y_3012_ = v___y_3067_;
v___y_3013_ = v___y_3069_;
v___y_3014_ = v___y_3070_;
v___y_3015_ = v___y_3071_;
v___y_3016_ = v___y_3072_;
v___y_3017_ = v___y_3074_;
v___y_3018_ = v___y_3073_;
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3078_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3081_;
v___y_3024_ = v___y_3080_;
goto v___jp_3010_;
}
}
v___jp_3084_:
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_dec_eq(v___y_3085_, v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3029_ = v___y_3086_;
v___y_3030_ = v___y_3085_;
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
v___y_3042_ = v___y_3099_;
v___y_3043_ = v___y_3098_;
goto v___jp_3028_;
}
else
{
if (v___y_3090_ == 0)
{
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3085_;
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
v___y_3029_ = v___y_3086_;
v___y_3030_ = v___y_3085_;
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
v___y_3042_ = v___y_3099_;
v___y_3043_ = v___y_3098_;
goto v___jp_3028_;
}
else
{
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3085_;
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
lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___x_3396_; 
lean_inc_ref(v_c_3335_);
v___x_3396_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_c_3335_, v_a_3343_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3469_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3469_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3469_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = l_Lean_Expr_cleanupAnnotations(v_a_3397_);
lean_dec(v_a_3397_);
v___x_3402_ = l_Lean_Expr_isApp(v___x_3401_);
if (v___x_3402_ == 0)
{
lean_dec_ref(v___x_3401_);
lean_del_object(v___x_3399_);
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
goto v___jp_3355_;
}
else
{
lean_object* v_arg_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v_arg_3403_ = lean_ctor_get(v___x_3401_, 1);
lean_inc_ref(v_arg_3403_);
v___x_3404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1));
v___x_3406_ = l_Lean_Expr_isConstOf(v___x_3404_, v___x_3405_);
if (v___x_3406_ == 0)
{
uint8_t v___x_3407_; 
v___x_3407_ = l_Lean_Expr_isApp(v___x_3404_);
if (v___x_3407_ == 0)
{
lean_dec_ref(v___x_3404_);
lean_dec_ref(v_arg_3403_);
lean_del_object(v___x_3399_);
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
goto v___jp_3355_;
}
else
{
lean_object* v_arg_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_arg_3408_ = lean_ctor_get(v___x_3404_, 1);
lean_inc_ref(v_arg_3408_);
v___x_3409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3404_);
lean_dec_ref(v___x_3404_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14));
v___x_3411_ = l_Lean_Expr_isConstOf(v___x_3409_, v___x_3410_);
if (v___x_3411_ == 0)
{
uint8_t v___x_3412_; 
v___x_3412_ = l_Lean_Expr_isApp(v___x_3409_);
if (v___x_3412_ == 0)
{
lean_dec_ref(v___x_3409_);
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
lean_del_object(v___x_3399_);
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3409_);
lean_dec_ref(v___x_3409_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__18));
v___x_3415_ = l_Lean_Expr_isConstOf(v___x_3413_, v___x_3414_);
lean_dec_ref(v___x_3413_);
if (v___x_3415_ == 0)
{
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
lean_del_object(v___x_3399_);
v___y_3356_ = v_a_3336_;
v___y_3357_ = v_a_3337_;
v___y_3358_ = v_a_3338_;
v___y_3359_ = v_a_3339_;
v___y_3360_ = v_a_3340_;
v___y_3361_ = v_a_3341_;
v___y_3362_ = v_a_3342_;
v___y_3363_ = v_a_3343_;
v___y_3364_ = v_a_3344_;
v___y_3365_ = v_a_3345_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3416_; 
v___x_3416_ = l_Lean_Meta_Grind_isMorallyIff(v_c_3335_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
v___x_3417_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_c_3335_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3417_);
v___x_3419_ = v___x_3399_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
else
{
lean_object* v___x_3421_; 
lean_del_object(v___x_3399_);
lean_inc_ref(v_c_3335_);
v___x_3421_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3335_, v_a_3336_, v_a_3340_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; uint8_t v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = lean_unbox(v_a_3422_);
lean_dec(v_a_3422_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3434_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3434_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3434_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3432_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
v___x_3430_ = l_Lean_mkApp3(v___x_3429_, v_arg_3408_, v_arg_3403_, v_a_3425_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3430_);
v___x_3432_ = v___x_3427_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
else
{
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
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
v___x_3440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
v___x_3441_ = l_Lean_mkApp3(v___x_3440_, v_arg_3408_, v_arg_3403_, v_a_3436_);
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
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
return v___x_3435_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
lean_dec_ref(v_c_3335_);
v_a_3446_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3421_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3421_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3454_; 
lean_dec_ref(v___x_3409_);
lean_del_object(v___x_3399_);
v___x_3454_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3464_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3464_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3464_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10, &l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
v___x_3460_ = l_Lean_mkApp3(v___x_3459_, v_arg_3408_, v_arg_3403_, v_a_3455_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3460_);
v___x_3462_ = v___x_3457_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3403_);
return v___x_3454_;
}
}
}
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
lean_dec_ref(v___x_3404_);
lean_dec_ref(v_c_3335_);
v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_arg_3403_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3465_);
v___x_3467_ = v___x_3399_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_3335_);
return v___x_3396_;
}
v___jp_3347_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = l_Lean_Expr_getAppNumArgs(v_c_3335_);
v___x_3350_ = lean_nat_sub(v___x_3349_, v___x_3348_);
lean_dec(v___x_3349_);
v___x_3351_ = lean_nat_sub(v___x_3350_, v___x_3348_);
lean_dec(v___x_3350_);
v___x_3352_ = l_Lean_Expr_getRevArg_x21(v_c_3335_, v___x_3351_);
lean_dec_ref(v_c_3335_);
v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
v___jp_3355_:
{
uint8_t v___x_3366_; 
v___x_3366_ = l_Lean_Meta_Grind_isIte(v_c_3335_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Lean_Meta_Grind_isDIte(v_c_3335_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_inc_ref(v_c_3335_);
v___x_3368_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3335_, v___y_3356_, v___y_3360_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3387_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3387_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3387_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_unbox(v_a_3369_);
lean_dec(v_a_3369_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3375_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_c_3335_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_c_3335_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
else
{
lean_object* v___x_3377_; 
lean_del_object(v___x_3371_);
lean_inc_ref(v_c_3335_);
v___x_3377_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3335_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3386_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3335_, v_a_3378_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3382_);
v___x_3384_ = v___x_3380_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
else
{
lean_dec_ref(v_c_3335_);
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_c_3335_);
v_a_3388_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3368_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3368_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
goto v___jp_3347_;
}
}
else
{
goto v___jp_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___boxed(lean_object* v_c_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v_c_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec(v_a_3471_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* v_mvarId_3483_, lean_object* v_major_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3485_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; uint8_t v_trace_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_trace_3494_ = lean_ctor_get_uint8(v_a_3493_, sizeof(void*)*17);
lean_dec(v_a_3493_);
if (v_trace_3494_ == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_Grind_cases(v_mvarId_3483_, v_major_3484_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3495_;
}
else
{
lean_object* v___x_3496_; 
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
lean_inc(v_a_3488_);
lean_inc_ref(v_a_3487_);
lean_inc_ref(v_major_3484_);
v___x_3496_ = lean_infer_type(v_major_3484_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = l_Lean_Meta_whnfD(v_a_3497_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = l_Lean_Expr_getAppFn(v_a_3499_);
lean_dec(v_a_3499_);
if (lean_obj_tag(v___x_3500_) == 4)
{
lean_object* v_declName_3501_; lean_object* v___x_3502_; 
v_declName_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_declName_3501_);
lean_dec_ref_known(v___x_3500_, 2);
v___x_3502_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3501_, v_a_3486_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v___x_3503_; 
lean_dec_ref_known(v___x_3502_, 1);
v___x_3503_ = l_Lean_Meta_Grind_cases(v_mvarId_3483_, v_major_3484_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3503_;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_major_3484_);
lean_dec(v_mvarId_3483_);
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3502_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3502_);
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
else
{
lean_object* v___x_3512_; 
lean_dec_ref(v___x_3500_);
v___x_3512_ = l_Lean_Meta_Grind_cases(v_mvarId_3483_, v_major_3484_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3512_;
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_major_3484_);
lean_dec(v_mvarId_3483_);
v_a_3513_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3498_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3498_);
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
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v_major_3484_);
lean_dec(v_mvarId_3483_);
v_a_3521_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3496_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3496_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v_major_3484_);
lean_dec(v_mvarId_3483_);
v_a_3529_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3492_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3492_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* v_mvarId_3537_, lean_object* v_major_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3537_, v_major_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* v_mvarId_3547_, lean_object* v_major_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_mvarId_3547_, v_major_3548_, v_a_3551_, v_a_3552_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* v_mvarId_3561_, lean_object* v_major_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(v_mvarId_3561_, v_major_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec(v_a_3563_);
return v_res_3574_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(lean_object* v_e_3575_){
_start:
{
uint64_t v_anchor_3576_; 
v_anchor_3576_ = lean_ctor_get_uint64(v_e_3575_, sizeof(void*)*3);
return v_anchor_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0___boxed(lean_object* v_e_3577_){
_start:
{
uint64_t v_res_3578_; lean_object* v_r_3579_; 
v_res_3578_ = l_Lean_Meta_Grind_instHasAnchorSplitCandidateWithAnchor___lam__0(v_e_3577_);
lean_dec_ref(v_e_3577_);
v_r_3579_ = lean_box_uint64(v_res_3578_);
return v_r_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(uint64_t v_a_3582_, lean_object* v_x_3583_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_box(0);
return v___x_3584_;
}
else
{
lean_object* v_key_3585_; lean_object* v_value_3586_; lean_object* v_tail_3587_; uint64_t v___x_3588_; uint8_t v___x_3589_; 
v_key_3585_ = lean_ctor_get(v_x_3583_, 0);
v_value_3586_ = lean_ctor_get(v_x_3583_, 1);
v_tail_3587_ = lean_ctor_get(v_x_3583_, 2);
v___x_3588_ = lean_unbox_uint64(v_key_3585_);
v___x_3589_ = lean_uint64_dec_eq(v___x_3588_, v_a_3582_);
if (v___x_3589_ == 0)
{
v_x_3583_ = v_tail_3587_;
goto _start;
}
else
{
lean_object* v___x_3591_; 
lean_inc(v_value_3586_);
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_value_3586_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_a_3592_, lean_object* v_x_3593_){
_start:
{
uint64_t v_a_boxed_3594_; lean_object* v_res_3595_; 
v_a_boxed_3594_ = lean_unbox_uint64(v_a_3592_);
lean_dec_ref(v_a_3592_);
v_res_3595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_boxed_3594_, v_x_3593_);
lean_dec(v_x_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(lean_object* v_m_3596_, uint64_t v_a_3597_){
_start:
{
lean_object* v_buckets_3598_; lean_object* v___x_3599_; uint64_t v___x_3600_; uint64_t v___x_3601_; uint64_t v_fold_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; uint64_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_buckets_3598_ = lean_ctor_get(v_m_3596_, 1);
v___x_3599_ = lean_array_get_size(v_buckets_3598_);
v___x_3600_ = 32ULL;
v___x_3601_ = lean_uint64_shift_right(v_a_3597_, v___x_3600_);
v_fold_3602_ = lean_uint64_xor(v_a_3597_, v___x_3601_);
v___x_3603_ = 16ULL;
v___x_3604_ = lean_uint64_shift_right(v_fold_3602_, v___x_3603_);
v___x_3605_ = lean_uint64_xor(v_fold_3602_, v___x_3604_);
v___x_3606_ = lean_uint64_to_usize(v___x_3605_);
v___x_3607_ = lean_usize_of_nat(v___x_3599_);
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_sub(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_usize_land(v___x_3606_, v___x_3609_);
v___x_3611_ = lean_array_uget_borrowed(v_buckets_3598_, v___x_3610_);
v___x_3612_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_3597_, v___x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_m_3613_, lean_object* v_a_3614_){
_start:
{
uint64_t v_a_boxed_3615_; lean_object* v_res_3616_; 
v_a_boxed_3615_ = lean_unbox_uint64(v_a_3614_);
lean_dec_ref(v_a_3614_);
v_res_3616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_3613_, v_a_boxed_3615_);
lean_dec_ref(v_m_3613_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
if (lean_obj_tag(v_x_3618_) == 0)
{
return v_x_3617_;
}
else
{
lean_object* v_key_3619_; lean_object* v_value_3620_; lean_object* v_tail_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3645_; 
v_key_3619_ = lean_ctor_get(v_x_3618_, 0);
v_value_3620_ = lean_ctor_get(v_x_3618_, 1);
v_tail_3621_ = lean_ctor_get(v_x_3618_, 2);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_x_3618_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3623_ = v_x_3618_;
v_isShared_3624_ = v_isSharedCheck_3645_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_tail_3621_);
lean_inc(v_value_3620_);
lean_inc(v_key_3619_);
lean_dec(v_x_3618_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3645_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; uint64_t v___x_3626_; uint64_t v___x_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v_fold_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3625_ = lean_array_get_size(v_x_3617_);
v___x_3626_ = 32ULL;
v___x_3627_ = lean_unbox_uint64(v_key_3619_);
v___x_3628_ = lean_uint64_shift_right(v___x_3627_, v___x_3626_);
v___x_3629_ = lean_unbox_uint64(v_key_3619_);
v_fold_3630_ = lean_uint64_xor(v___x_3629_, v___x_3628_);
v___x_3631_ = 16ULL;
v___x_3632_ = lean_uint64_shift_right(v_fold_3630_, v___x_3631_);
v___x_3633_ = lean_uint64_xor(v_fold_3630_, v___x_3632_);
v___x_3634_ = lean_uint64_to_usize(v___x_3633_);
v___x_3635_ = lean_usize_of_nat(v___x_3625_);
v___x_3636_ = ((size_t)1ULL);
v___x_3637_ = lean_usize_sub(v___x_3635_, v___x_3636_);
v___x_3638_ = lean_usize_land(v___x_3634_, v___x_3637_);
v___x_3639_ = lean_array_uget_borrowed(v_x_3617_, v___x_3638_);
lean_inc(v___x_3639_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 2, v___x_3639_);
v___x_3641_ = v___x_3623_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_key_3619_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_value_3620_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_array_uset(v_x_3617_, v___x_3638_, v___x_3641_);
v_x_3617_ = v___x_3642_;
v_x_3618_ = v_tail_3621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(lean_object* v_i_3646_, lean_object* v_source_3647_, lean_object* v_target_3648_){
_start:
{
lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = lean_array_get_size(v_source_3647_);
v___x_3650_ = lean_nat_dec_lt(v_i_3646_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_dec_ref(v_source_3647_);
lean_dec(v_i_3646_);
return v_target_3648_;
}
else
{
lean_object* v_es_3651_; lean_object* v___x_3652_; lean_object* v_source_3653_; lean_object* v_target_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_es_3651_ = lean_array_fget(v_source_3647_, v_i_3646_);
v___x_3652_ = lean_box(0);
v_source_3653_ = lean_array_fset(v_source_3647_, v_i_3646_, v___x_3652_);
v_target_3654_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_target_3648_, v_es_3651_);
v___x_3655_ = lean_unsigned_to_nat(1u);
v___x_3656_ = lean_nat_add(v_i_3646_, v___x_3655_);
lean_dec(v_i_3646_);
v_i_3646_ = v___x_3656_;
v_source_3647_ = v_source_3653_;
v_target_3648_ = v_target_3654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_data_3658_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_nbuckets_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3659_ = lean_array_get_size(v_data_3658_);
v___x_3660_ = lean_unsigned_to_nat(2u);
v_nbuckets_3661_ = lean_nat_mul(v___x_3659_, v___x_3660_);
v___x_3662_ = lean_unsigned_to_nat(0u);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_mk_array(v_nbuckets_3661_, v___x_3663_);
v___x_3665_ = lean_array_propagate_mark(v_data_3658_, v___x_3664_);
v___x_3666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v___x_3662_, v_data_3658_, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(uint64_t v_a_3667_, lean_object* v_b_3668_, lean_object* v_x_3669_){
_start:
{
if (lean_obj_tag(v_x_3669_) == 0)
{
lean_dec(v_b_3668_);
return v_x_3669_;
}
else
{
lean_object* v_key_3670_; lean_object* v_value_3671_; lean_object* v_tail_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3686_; 
v_key_3670_ = lean_ctor_get(v_x_3669_, 0);
v_value_3671_ = lean_ctor_get(v_x_3669_, 1);
v_tail_3672_ = lean_ctor_get(v_x_3669_, 2);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_x_3669_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3674_ = v_x_3669_;
v_isShared_3675_ = v_isSharedCheck_3686_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_tail_3672_);
lean_inc(v_value_3671_);
lean_inc(v_key_3670_);
lean_dec(v_x_3669_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3686_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
uint64_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = lean_unbox_uint64(v_key_3670_);
v___x_3677_ = lean_uint64_dec_eq(v___x_3676_, v_a_3667_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3667_, v_b_3668_, v_tail_3672_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 2, v___x_3678_);
v___x_3680_ = v___x_3674_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_key_3670_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_value_3671_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
lean_dec(v_value_3671_);
lean_dec(v_key_3670_);
v___x_3682_ = lean_box_uint64(v_a_3667_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 1, v_b_3668_);
lean_ctor_set(v___x_3674_, 0, v___x_3682_);
v___x_3684_ = v___x_3674_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_b_3668_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_tail_3672_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_a_3687_, lean_object* v_b_3688_, lean_object* v_x_3689_){
_start:
{
uint64_t v_a_boxed_3690_; lean_object* v_res_3691_; 
v_a_boxed_3690_ = lean_unbox_uint64(v_a_3687_);
lean_dec_ref(v_a_3687_);
v_res_3691_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_boxed_3690_, v_b_3688_, v_x_3689_);
return v_res_3691_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(uint64_t v_a_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3693_) == 0)
{
uint8_t v___x_3694_; 
v___x_3694_ = 0;
return v___x_3694_;
}
else
{
lean_object* v_key_3695_; lean_object* v_tail_3696_; uint64_t v___x_3697_; uint8_t v___x_3698_; 
v_key_3695_ = lean_ctor_get(v_x_3693_, 0);
v_tail_3696_ = lean_ctor_get(v_x_3693_, 2);
v___x_3697_ = lean_unbox_uint64(v_key_3695_);
v___x_3698_ = lean_uint64_dec_eq(v___x_3697_, v_a_3692_);
if (v___x_3698_ == 0)
{
v_x_3693_ = v_tail_3696_;
goto _start;
}
else
{
return v___x_3698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_3700_, lean_object* v_x_3701_){
_start:
{
uint64_t v_a_boxed_3702_; uint8_t v_res_3703_; lean_object* v_r_3704_; 
v_a_boxed_3702_ = lean_unbox_uint64(v_a_3700_);
lean_dec_ref(v_a_3700_);
v_res_3703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_boxed_3702_, v_x_3701_);
lean_dec(v_x_3701_);
v_r_3704_ = lean_box(v_res_3703_);
return v_r_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(lean_object* v_m_3705_, uint64_t v_a_3706_, lean_object* v_b_3707_){
_start:
{
lean_object* v_size_3708_; lean_object* v_buckets_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3752_; 
v_size_3708_ = lean_ctor_get(v_m_3705_, 0);
v_buckets_3709_ = lean_ctor_get(v_m_3705_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_m_3705_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3711_ = v_m_3705_;
v_isShared_3712_ = v_isSharedCheck_3752_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_buckets_3709_);
lean_inc(v_size_3708_);
lean_dec(v_m_3705_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3752_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; uint64_t v___x_3714_; uint64_t v___x_3715_; uint64_t v_fold_3716_; uint64_t v___x_3717_; uint64_t v___x_3718_; uint64_t v___x_3719_; size_t v___x_3720_; size_t v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; lean_object* v_bkt_3725_; uint8_t v___x_3726_; 
v___x_3713_ = lean_array_get_size(v_buckets_3709_);
v___x_3714_ = 32ULL;
v___x_3715_ = lean_uint64_shift_right(v_a_3706_, v___x_3714_);
v_fold_3716_ = lean_uint64_xor(v_a_3706_, v___x_3715_);
v___x_3717_ = 16ULL;
v___x_3718_ = lean_uint64_shift_right(v_fold_3716_, v___x_3717_);
v___x_3719_ = lean_uint64_xor(v_fold_3716_, v___x_3718_);
v___x_3720_ = lean_uint64_to_usize(v___x_3719_);
v___x_3721_ = lean_usize_of_nat(v___x_3713_);
v___x_3722_ = ((size_t)1ULL);
v___x_3723_ = lean_usize_sub(v___x_3721_, v___x_3722_);
v___x_3724_ = lean_usize_land(v___x_3720_, v___x_3723_);
v_bkt_3725_ = lean_array_uget_borrowed(v_buckets_3709_, v___x_3724_);
v___x_3726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_3706_, v_bkt_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v_size_x27_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v_buckets_x27_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3727_ = lean_unsigned_to_nat(1u);
v_size_x27_3728_ = lean_nat_add(v_size_3708_, v___x_3727_);
lean_dec(v_size_3708_);
v___x_3729_ = lean_box_uint64(v_a_3706_);
lean_inc(v_bkt_3725_);
v___x_3730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v_b_3707_);
lean_ctor_set(v___x_3730_, 2, v_bkt_3725_);
v_buckets_x27_3731_ = lean_array_uset(v_buckets_3709_, v___x_3724_, v___x_3730_);
v___x_3732_ = lean_unsigned_to_nat(4u);
v___x_3733_ = lean_nat_mul(v_size_x27_3728_, v___x_3732_);
v___x_3734_ = lean_unsigned_to_nat(3u);
v___x_3735_ = lean_nat_div(v___x_3733_, v___x_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_array_get_size(v_buckets_x27_3731_);
v___x_3737_ = lean_nat_dec_le(v___x_3735_, v___x_3736_);
lean_dec(v___x_3735_);
if (v___x_3737_ == 0)
{
lean_object* v_val_3738_; lean_object* v___x_3740_; 
v_val_3738_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_buckets_x27_3731_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 1, v_val_3738_);
lean_ctor_set(v___x_3711_, 0, v_size_x27_3728_);
v___x_3740_ = v___x_3711_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_size_x27_3728_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_val_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
else
{
lean_object* v___x_3743_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 1, v_buckets_x27_3731_);
lean_ctor_set(v___x_3711_, 0, v_size_x27_3728_);
v___x_3743_ = v___x_3711_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_size_x27_3728_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_buckets_x27_3731_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v_buckets_x27_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
lean_inc(v_bkt_3725_);
v___x_3745_ = lean_box(0);
v_buckets_x27_3746_ = lean_array_uset(v_buckets_3709_, v___x_3724_, v___x_3745_);
v___x_3747_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_3706_, v_b_3707_, v_bkt_3725_);
v___x_3748_ = lean_array_uset(v_buckets_x27_3746_, v___x_3724_, v___x_3747_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 1, v___x_3748_);
v___x_3750_ = v___x_3711_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_size_3708_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_m_3753_, lean_object* v_a_3754_, lean_object* v_b_3755_){
_start:
{
uint64_t v_a_boxed_3756_; lean_object* v_res_3757_; 
v_a_boxed_3756_ = lean_unbox_uint64(v_a_3754_);
lean_dec_ref(v_a_3754_);
v_res_3757_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_3753_, v_a_boxed_3756_, v_b_3755_);
return v_res_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_box(0);
v___x_3759_ = lean_unsigned_to_nat(16u);
v___x_3760_ = lean_mk_array(v___x_3759_, v___x_3758_);
return v___x_3760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_found_3763_; 
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__0);
v___x_3762_ = lean_unsigned_to_nat(0u);
v_found_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_3763_, 0, v___x_3762_);
lean_ctor_set(v_found_3763_, 1, v___x_3761_);
return v_found_3763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v_found_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_found_3764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__1);
v___x_3765_ = lean_box(0);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_found_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(lean_object* v_shift_3767_, lean_object* v_numDigits_3768_, lean_object* v_es_3769_, lean_object* v_as_3770_, size_t v_sz_3771_, size_t v_i_3772_, lean_object* v_b_3773_){
_start:
{
lean_object* v_a_3775_; uint8_t v___x_3779_; 
v___x_3779_ = lean_usize_dec_lt(v_i_3772_, v_sz_3771_);
if (v___x_3779_ == 0)
{
return v_b_3773_;
}
else
{
lean_object* v_snd_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3814_; 
v_snd_3780_ = lean_ctor_get(v_b_3773_, 1);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_b_3773_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v_b_3773_, 0);
lean_dec(v_unused_3815_);
v___x_3782_ = v_b_3773_;
v_isShared_3783_ = v_isSharedCheck_3814_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_snd_3780_);
lean_dec(v_b_3773_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3814_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v_a_3784_; uint64_t v_anchor_3785_; lean_object* v___x_3786_; uint64_t v___x_3787_; uint64_t v___x_3788_; lean_object* v___x_3789_; 
v_a_3784_ = lean_array_uget_borrowed(v_as_3770_, v_i_3772_);
v_anchor_3785_ = lean_ctor_get_uint64(v_a_3784_, sizeof(void*)*3);
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_uint64_of_nat(v_shift_3767_);
v___x_3788_ = lean_uint64_shift_right(v_anchor_3785_, v___x_3787_);
v___x_3789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_snd_3780_, v___x_3788_);
if (lean_obj_tag(v___x_3789_) == 1)
{
lean_object* v_val_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3808_; 
v_val_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3808_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_val_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3808_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
uint64_t v___x_3794_; uint8_t v___x_3795_; 
v___x_3794_ = lean_unbox_uint64(v_val_3790_);
lean_dec(v_val_3790_);
v___x_3795_ = lean_uint64_dec_eq(v___x_3794_, v_anchor_3785_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_add(v_numDigits_3768_, v___x_3796_);
v___x_3798_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3769_, v___x_3797_);
lean_dec(v___x_3797_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3798_);
v___x_3800_ = v___x_3792_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3800_);
v___x_3802_ = v___x_3782_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_snd_3780_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v___x_3806_; 
lean_del_object(v___x_3792_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3786_);
v___x_3806_ = v___x_3782_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_snd_3780_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v_a_3775_ = v___x_3806_;
goto v___jp_3774_;
}
}
}
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
lean_dec(v___x_3789_);
v___x_3809_ = lean_box_uint64(v_anchor_3785_);
v___x_3810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_snd_3780_, v___x_3788_, v___x_3809_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3810_);
lean_ctor_set(v___x_3782_, 0, v___x_3786_);
v___x_3812_ = v___x_3782_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
v_a_3775_ = v___x_3812_;
goto v___jp_3774_;
}
}
}
}
v___jp_3774_:
{
size_t v___x_3776_; size_t v___x_3777_; 
v___x_3776_ = ((size_t)1ULL);
v___x_3777_ = lean_usize_add(v_i_3772_, v___x_3776_);
v_i_3772_ = v___x_3777_;
v_b_3773_ = v_a_3775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(lean_object* v_es_3816_, lean_object* v_numDigits_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3818_ = lean_unsigned_to_nat(4u);
v___x_3819_ = lean_nat_mul(v___x_3818_, v_numDigits_3817_);
v___x_3820_ = lean_unsigned_to_nat(64u);
v___x_3821_ = lean_nat_dec_lt(v___x_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_dec(v___x_3819_);
lean_inc(v_numDigits_3817_);
return v_numDigits_3817_;
}
else
{
lean_object* v_shift_3822_; lean_object* v___x_3823_; size_t v_sz_3824_; size_t v___x_3825_; lean_object* v___x_3826_; lean_object* v_fst_3827_; 
v_shift_3822_ = lean_nat_sub(v___x_3820_, v___x_3819_);
lean_dec(v___x_3819_);
v___x_3823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___closed__2);
v_sz_3824_ = lean_array_size(v_es_3816_);
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3822_, v_numDigits_3817_, v_es_3816_, v_es_3816_, v_sz_3824_, v___x_3825_, v___x_3823_);
lean_dec(v_shift_3822_);
v_fst_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_fst_3827_);
lean_dec_ref(v___x_3826_);
if (lean_obj_tag(v_fst_3827_) == 0)
{
lean_inc(v_numDigits_3817_);
return v_numDigits_3817_;
}
else
{
lean_object* v_val_3828_; 
v_val_3828_ = lean_ctor_get(v_fst_3827_, 0);
lean_inc(v_val_3828_);
lean_dec_ref_known(v_fst_3827_, 1);
return v_val_3828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2___boxed(lean_object* v_es_3829_, lean_object* v_numDigits_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3829_, v_numDigits_3830_);
lean_dec(v_numDigits_3830_);
lean_dec_ref(v_es_3829_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5___boxed(lean_object* v_shift_3832_, lean_object* v_numDigits_3833_, lean_object* v_es_3834_, lean_object* v_as_3835_, lean_object* v_sz_3836_, lean_object* v_i_3837_, lean_object* v_b_3838_){
_start:
{
size_t v_sz_boxed_3839_; size_t v_i_boxed_3840_; lean_object* v_res_3841_; 
v_sz_boxed_3839_ = lean_unbox_usize(v_sz_3836_);
lean_dec(v_sz_3836_);
v_i_boxed_3840_ = lean_unbox_usize(v_i_3837_);
lean_dec(v_i_3837_);
v_res_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__5(v_shift_3832_, v_numDigits_3833_, v_es_3834_, v_as_3835_, v_sz_boxed_3839_, v_i_boxed_3840_, v_b_3838_);
lean_dec_ref(v_as_3835_);
lean_dec_ref(v_es_3834_);
lean_dec(v_numDigits_3833_);
lean_dec(v_shift_3832_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(lean_object* v_es_3842_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_unsigned_to_nat(4u);
v___x_3844_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2(v_es_3842_, v___x_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1___boxed(lean_object* v_es_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_es_3845_);
lean_dec_ref(v_es_3845_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(lean_object* v_filter_3847_, lean_object* v_as_3848_, size_t v_i_3849_, size_t v_stop_3850_, lean_object* v_b_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_a_3864_; uint8_t v___x_3868_; 
v___x_3868_ = lean_usize_dec_eq(v_i_3849_, v_stop_3850_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; lean_object* v_e_3870_; lean_object* v___x_3871_; 
v___x_3869_ = lean_array_uget_borrowed(v_as_3848_, v_i_3849_);
v_e_3870_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v___x_3869_);
v___x_3871_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v___x_3869_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
lean_inc(v___x_3869_);
v___x_3873_ = l_Lean_Meta_Grind_checkSplitStatus(v___x_3869_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
if (lean_obj_tag(v_a_3874_) == 2)
{
lean_object* v_numCases_3875_; uint8_t v_isRec_3876_; lean_object* v___x_3877_; 
v_numCases_3875_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_numCases_3875_);
v_isRec_3876_ = lean_ctor_get_uint8(v_a_3874_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3874_, 1);
lean_inc_ref(v_filter_3847_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3854_);
lean_inc(v___y_3853_);
lean_inc(v___y_3852_);
lean_inc_ref(v_e_3870_);
v___x_3877_ = lean_apply_12(v_filter_3847_, v_e_3870_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, lean_box(0));
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; uint8_t v___x_3879_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = lean_unbox(v_a_3878_);
lean_dec(v_a_3878_);
if (v___x_3879_ == 0)
{
lean_dec(v_numCases_3875_);
lean_dec(v_a_3872_);
lean_dec_ref(v_e_3870_);
v_a_3864_ = v_b_3851_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3880_; uint64_t v___x_3881_; lean_object* v___x_3882_; 
lean_inc(v___x_3869_);
v___x_3880_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_3880_, 0, v___x_3869_);
lean_ctor_set(v___x_3880_, 1, v_numCases_3875_);
lean_ctor_set(v___x_3880_, 2, v_e_3870_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*3 + 8, v_isRec_3876_);
v___x_3881_ = lean_unbox_uint64(v_a_3872_);
lean_dec(v_a_3872_);
lean_ctor_set_uint64(v___x_3880_, sizeof(void*)*3, v___x_3881_);
v___x_3882_ = lean_array_push(v_b_3851_, v___x_3880_);
v_a_3864_ = v___x_3882_;
goto v___jp_3863_;
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v_numCases_3875_);
lean_dec(v_a_3872_);
lean_dec_ref(v_e_3870_);
lean_dec_ref(v_b_3851_);
lean_dec_ref(v_filter_3847_);
v_a_3883_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3877_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3877_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_dec(v_a_3874_);
lean_dec(v_a_3872_);
lean_dec_ref(v_e_3870_);
v_a_3864_ = v_b_3851_;
goto v___jp_3863_;
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_e_3870_);
lean_dec_ref(v_b_3851_);
lean_dec_ref(v_filter_3847_);
v_a_3891_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3873_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3873_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec_ref(v_e_3870_);
lean_dec_ref(v_b_3851_);
lean_dec_ref(v_filter_3847_);
v_a_3899_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3871_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3871_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v___x_3907_; 
lean_dec_ref(v_filter_3847_);
v___x_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3907_, 0, v_b_3851_);
return v___x_3907_;
}
v___jp_3863_:
{
size_t v___x_3865_; size_t v___x_3866_; 
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_add(v_i_3849_, v___x_3865_);
v_i_3849_ = v___x_3866_;
v_b_3851_ = v_a_3864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0___boxed(lean_object* v_filter_3908_, lean_object* v_as_3909_, lean_object* v_i_3910_, lean_object* v_stop_3911_, lean_object* v_b_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
size_t v_i_boxed_3924_; size_t v_stop_boxed_3925_; lean_object* v_res_3926_; 
v_i_boxed_3924_ = lean_unbox_usize(v_i_3910_);
lean_dec(v_i_3910_);
v_stop_boxed_3925_ = lean_unbox_usize(v_stop_3911_);
lean_dec(v_stop_3911_);
v_res_3926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3908_, v_as_3909_, v_i_boxed_3924_, v_stop_boxed_3925_, v_b_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v_as_3909_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(lean_object* v_filter_3929_, lean_object* v_as_3930_, lean_object* v_start_3931_, lean_object* v_stop_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___closed__0));
v___x_3945_ = lean_nat_dec_lt(v_start_3931_, v_stop_3932_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref(v_filter_3929_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
return v___x_3946_;
}
else
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = lean_array_get_size(v_as_3930_);
v___x_3948_ = lean_nat_dec_le(v_stop_3932_, v___x_3947_);
if (v___x_3948_ == 0)
{
uint8_t v___x_3949_; 
v___x_3949_ = lean_nat_dec_lt(v_start_3931_, v___x_3947_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
lean_dec_ref(v_filter_3929_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3944_);
return v___x_3950_;
}
else
{
size_t v___x_3951_; size_t v___x_3952_; lean_object* v___x_3953_; 
v___x_3951_ = lean_usize_of_nat(v_start_3931_);
v___x_3952_ = lean_usize_of_nat(v___x_3947_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3929_, v_as_3930_, v___x_3951_, v___x_3952_, v___x_3944_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3953_;
}
}
else
{
size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = lean_usize_of_nat(v_start_3931_);
v___x_3955_ = lean_usize_of_nat(v_stop_3932_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0_spec__0(v_filter_3929_, v_as_3930_, v___x_3954_, v___x_3955_, v___x_3944_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0___boxed(lean_object* v_filter_3957_, lean_object* v_as_3958_, lean_object* v_start_3959_, lean_object* v_stop_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3957_, v_as_3958_, v_start_3959_, v_stop_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec(v_stop_3960_);
lean_dec(v_start_3959_);
lean_dec_ref(v_as_3958_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors(lean_object* v_filter_3973_, lean_object* v_candidates_x3f_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_candidates_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; 
if (lean_obj_tag(v_candidates_x3f_3974_) == 0)
{
lean_object* v___x_4020_; lean_object* v_toGoalState_4021_; lean_object* v_split_4022_; lean_object* v_candidates_4023_; 
v___x_4020_ = lean_st_ref_get(v_a_3975_);
v_toGoalState_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc_ref(v_toGoalState_4021_);
lean_dec(v___x_4020_);
v_split_4022_ = lean_ctor_get(v_toGoalState_4021_, 15);
lean_inc_ref(v_split_4022_);
lean_dec_ref(v_toGoalState_4021_);
v_candidates_4023_ = lean_ctor_get(v_split_4022_, 1);
lean_inc(v_candidates_4023_);
lean_dec_ref(v_split_4022_);
v_candidates_3987_ = v_candidates_4023_;
v___y_3988_ = v_a_3975_;
v___y_3989_ = v_a_3976_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
goto v___jp_3986_;
}
else
{
lean_object* v_val_4024_; 
v_val_4024_ = lean_ctor_get(v_candidates_x3f_3974_, 0);
lean_inc(v_val_4024_);
lean_dec_ref_known(v_candidates_x3f_3974_, 1);
v_candidates_3987_ = v_val_4024_;
v___y_3988_ = v_a_3975_;
v___y_3989_ = v_a_3976_;
v___y_3990_ = v_a_3977_;
v___y_3991_ = v_a_3978_;
v___y_3992_ = v_a_3979_;
v___y_3993_ = v_a_3980_;
v___y_3994_ = v_a_3981_;
v___y_3995_ = v_a_3982_;
v___y_3996_ = v_a_3983_;
v___y_3997_ = v_a_3984_;
goto v___jp_3986_;
}
v___jp_3986_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3998_ = lean_array_mk(v_candidates_3987_);
v___x_3999_ = lean_unsigned_to_nat(0u);
v___x_4000_ = lean_array_get_size(v___x_3998_);
v___x_4001_ = l_Array_filterMapM___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__0(v_filter_3973_, v___x_3998_, v___x_3999_, v___x_4000_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec_ref(v___x_3998_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4011_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4011_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4011_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4006_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1(v_a_4002_);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v_a_4002_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4007_);
v___x_4009_ = v___x_4004_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4001_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4001_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed(lean_object* v_filter_4025_, lean_object* v_candidates_x3f_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v_filter_4025_, v_candidates_x3f_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec(v_a_4027_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4039_, lean_object* v_m_4040_, uint64_t v_a_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___redArg(v_m_4040_, v_a_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4043_, lean_object* v_m_4044_, lean_object* v_a_4045_){
_start:
{
uint64_t v_a_boxed_4046_; lean_object* v_res_4047_; 
v_a_boxed_4046_ = lean_unbox_uint64(v_a_4045_);
lean_dec_ref(v_a_4045_);
v_res_4047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3(v_00_u03b2_4043_, v_m_4044_, v_a_boxed_4046_);
lean_dec_ref(v_m_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4048_, lean_object* v_m_4049_, uint64_t v_a_4050_, lean_object* v_b_4051_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___redArg(v_m_4049_, v_a_4050_, v_b_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4053_, lean_object* v_m_4054_, lean_object* v_a_4055_, lean_object* v_b_4056_){
_start:
{
uint64_t v_a_boxed_4057_; lean_object* v_res_4058_; 
v_a_boxed_4057_ = lean_unbox_uint64(v_a_4055_);
lean_dec_ref(v_a_4055_);
v_res_4058_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4(v_00_u03b2_4053_, v_m_4054_, v_a_boxed_4057_, v_b_4056_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_4059_, uint64_t v_a_4060_, lean_object* v_x_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___redArg(v_a_4060_, v_x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4063_, lean_object* v_a_4064_, lean_object* v_x_4065_){
_start:
{
uint64_t v_a_boxed_4066_; lean_object* v_res_4067_; 
v_a_boxed_4066_ = lean_unbox_uint64(v_a_4064_);
lean_dec_ref(v_a_4064_);
v_res_4067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__3_spec__4(v_00_u03b2_4063_, v_a_boxed_4066_, v_x_4065_);
lean_dec(v_x_4065_);
return v_res_4067_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4068_, uint64_t v_a_4069_, lean_object* v_x_4070_){
_start:
{
uint8_t v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___redArg(v_a_4069_, v_x_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4072_, lean_object* v_a_4073_, lean_object* v_x_4074_){
_start:
{
uint64_t v_a_boxed_4075_; uint8_t v_res_4076_; lean_object* v_r_4077_; 
v_a_boxed_4075_ = lean_unbox_uint64(v_a_4073_);
lean_dec_ref(v_a_4073_);
v_res_4076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_4072_, v_a_boxed_4075_, v_x_4074_);
lean_dec(v_x_4074_);
v_r_4077_ = lean_box(v_res_4076_);
return v_r_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_4078_, lean_object* v_data_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7___redArg(v_data_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4081_, uint64_t v_a_4082_, lean_object* v_b_4083_, lean_object* v_x_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___redArg(v_a_4082_, v_b_4083_, v_x_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_, lean_object* v_x_4089_){
_start:
{
uint64_t v_a_boxed_4090_; lean_object* v_res_4091_; 
v_a_boxed_4090_ = lean_unbox_uint64(v_a_4087_);
lean_dec_ref(v_a_4087_);
v_res_4091_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4086_, v_a_boxed_4090_, v_b_4088_, v_x_4089_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_4092_, lean_object* v_i_4093_, lean_object* v_source_4094_, lean_object* v_target_4095_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8___redArg(v_i_4093_, v_source_4094_, v_target_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_4097_, lean_object* v_x_4098_, lean_object* v_x_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00Lean_Meta_Grind_getSplitCandidateAnchors_spec__1_spec__2_spec__4_spec__7_spec__8_spec__10___redArg(v_x_4098_, v_x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(lean_object* v_x_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = 1;
v___x_4114_ = lean_box(v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0___boxed(lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo___lam__0(v_x_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v_x_4116_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(uint64_t v___x_4129_, uint64_t v_a_4130_, lean_object* v_c_4131_, lean_object* v_numDigits_4132_, lean_object* v_as_4133_, size_t v_sz_4134_, size_t v_i_4135_, lean_object* v_b_4136_){
_start:
{
lean_object* v_a_4139_; uint8_t v___x_4143_; 
v___x_4143_ = lean_usize_dec_lt(v_i_4135_, v_sz_4134_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; 
lean_dec(v_numDigits_4132_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v_b_4136_);
return v___x_4144_;
}
else
{
lean_object* v_snd_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4171_; 
v_snd_4145_ = lean_ctor_get(v_b_4136_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_b_4136_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v_b_4136_, 0);
lean_dec(v_unused_4172_);
v___x_4147_ = v_b_4136_;
v_isShared_4148_ = v_isSharedCheck_4171_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_snd_4145_);
lean_dec(v_b_4136_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4171_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v_a_4149_; lean_object* v_c_4150_; uint64_t v_anchor_4151_; lean_object* v___x_4152_; uint64_t v___x_4153_; uint64_t v___x_4154_; uint8_t v___x_4155_; 
v_a_4149_ = lean_array_uget_borrowed(v_as_4133_, v_i_4135_);
v_c_4150_ = lean_ctor_get(v_a_4149_, 0);
v_anchor_4151_ = lean_ctor_get_uint64(v_a_4149_, sizeof(void*)*3);
v___x_4152_ = lean_box(0);
v___x_4153_ = lean_uint64_shift_right(v_anchor_4151_, v___x_4129_);
v___x_4154_ = lean_uint64_shift_right(v_a_4130_, v___x_4129_);
v___x_4155_ = lean_uint64_dec_eq(v___x_4153_, v___x_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4157_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4152_);
v___x_4157_ = v___x_4147_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_snd_4145_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
v_a_4139_ = v___x_4157_;
goto v___jp_4138_;
}
}
else
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Lean_Meta_Grind_SplitInfo_beq(v_c_4150_, v_c_4131_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_nat_add(v_snd_4145_, v___x_4160_);
lean_dec(v_snd_4145_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 1, v___x_4161_);
lean_ctor_set(v___x_4147_, 0, v___x_4152_);
v___x_4163_ = v___x_4147_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
v_a_4139_ = v___x_4163_;
goto v___jp_4138_;
}
}
else
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; 
lean_inc(v_snd_4145_);
v___x_4165_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4165_, 0, v_numDigits_4132_);
lean_ctor_set(v___x_4165_, 1, v_snd_4145_);
lean_ctor_set_uint64(v___x_4165_, sizeof(void*)*2, v_a_4130_);
v___x_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4166_);
v___x_4168_ = v___x_4147_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_snd_4145_);
v___x_4168_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
}
}
}
v___jp_4138_:
{
size_t v___x_4140_; size_t v___x_4141_; 
v___x_4140_ = ((size_t)1ULL);
v___x_4141_ = lean_usize_add(v_i_4135_, v___x_4140_);
v_i_4135_ = v___x_4141_;
v_b_4136_ = v_a_4139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg___boxed(lean_object* v___x_4173_, lean_object* v_a_4174_, lean_object* v_c_4175_, lean_object* v_numDigits_4176_, lean_object* v_as_4177_, lean_object* v_sz_4178_, lean_object* v_i_4179_, lean_object* v_b_4180_, lean_object* v___y_4181_){
_start:
{
uint64_t v___x_7695__boxed_4182_; uint64_t v_a_7696__boxed_4183_; size_t v_sz_boxed_4184_; size_t v_i_boxed_4185_; lean_object* v_res_4186_; 
v___x_7695__boxed_4182_ = lean_unbox_uint64(v___x_4173_);
lean_dec_ref(v___x_4173_);
v_a_7696__boxed_4183_ = lean_unbox_uint64(v_a_4174_);
lean_dec_ref(v_a_4174_);
v_sz_boxed_4184_ = lean_unbox_usize(v_sz_4178_);
lean_dec(v_sz_4178_);
v_i_boxed_4185_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_7695__boxed_4182_, v_a_7696__boxed_4183_, v_c_4175_, v_numDigits_4176_, v_as_4177_, v_sz_boxed_4184_, v_i_boxed_4185_, v_b_4180_);
lean_dec_ref(v_as_4177_);
lean_dec_ref(v_c_4175_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo(lean_object* v_c_4191_, lean_object* v_candidates_x3f_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___f_4204_; lean_object* v___x_4205_; 
v___f_4204_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__0));
v___x_4205_ = l_Lean_Meta_Grind_getSplitCandidateAnchors(v___f_4204_, v_candidates_x3f_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v_candidates_4207_; lean_object* v_numDigits_4208_; lean_object* v___x_4209_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v_candidates_4207_ = lean_ctor_get(v_a_4206_, 0);
lean_inc_ref(v_candidates_4207_);
v_numDigits_4208_ = lean_ctor_get(v_a_4206_, 1);
lean_inc(v_numDigits_4208_);
lean_dec(v_a_4206_);
v___x_4209_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_c_4191_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; uint64_t v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; size_t v_sz_4218_; size_t v___x_4219_; uint64_t v___x_4220_; lean_object* v___x_4221_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v___x_4211_ = lean_unsigned_to_nat(64u);
v___x_4212_ = lean_unsigned_to_nat(4u);
v___x_4213_ = lean_nat_mul(v___x_4212_, v_numDigits_4208_);
v___x_4214_ = lean_nat_sub(v___x_4211_, v___x_4213_);
lean_dec(v___x_4213_);
v___x_4215_ = lean_uint64_of_nat(v___x_4214_);
lean_dec(v___x_4214_);
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = ((lean_object*)(l_Lean_Meta_Grind_mkSplitAnchorRefInfo___closed__1));
v_sz_4218_ = lean_array_size(v_candidates_4207_);
v___x_4219_ = ((size_t)0ULL);
v___x_4220_ = lean_unbox_uint64(v_a_4210_);
lean_inc(v_numDigits_4208_);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4215_, v___x_4220_, v_c_4191_, v_numDigits_4208_, v_candidates_4207_, v_sz_4218_, v___x_4219_, v___x_4217_);
lean_dec_ref(v_candidates_4207_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4236_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4236_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4236_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_fst_4226_; 
v_fst_4226_ = lean_ctor_get(v_a_4222_, 0);
lean_inc(v_fst_4226_);
lean_dec(v_a_4222_);
if (lean_obj_tag(v_fst_4226_) == 0)
{
lean_object* v___x_4227_; uint64_t v___x_4228_; lean_object* v___x_4230_; 
v___x_4227_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_4227_, 0, v_numDigits_4208_);
lean_ctor_set(v___x_4227_, 1, v___x_4216_);
v___x_4228_ = lean_unbox_uint64(v_a_4210_);
lean_dec(v_a_4210_);
lean_ctor_set_uint64(v___x_4227_, sizeof(void*)*2, v___x_4228_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4227_);
v___x_4230_ = v___x_4224_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4227_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
else
{
lean_object* v_val_4232_; lean_object* v___x_4234_; 
lean_dec(v_a_4210_);
lean_dec(v_numDigits_4208_);
v_val_4232_ = lean_ctor_get(v_fst_4226_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v_fst_4226_, 1);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v_val_4232_);
v___x_4234_ = v___x_4224_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_val_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec(v_a_4210_);
lean_dec(v_numDigits_4208_);
v_a_4237_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4221_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4221_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec(v_numDigits_4208_);
lean_dec_ref(v_candidates_4207_);
v_a_4245_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4209_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4209_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
v_a_4253_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4205_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4205_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkSplitAnchorRefInfo___boxed(lean_object* v_c_4261_, lean_object* v_candidates_x3f_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_4261_, v_candidates_x3f_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_c_4261_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(uint64_t v___x_4275_, uint64_t v_a_4276_, lean_object* v_c_4277_, lean_object* v_numDigits_4278_, lean_object* v_as_4279_, size_t v_sz_4280_, size_t v_i_4281_, lean_object* v_b_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___redArg(v___x_4275_, v_a_4276_, v_c_4277_, v_numDigits_4278_, v_as_4279_, v_sz_4280_, v_i_4281_, v_b_4282_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0___boxed(lean_object** _args){
lean_object* v___x_4295_ = _args[0];
lean_object* v_a_4296_ = _args[1];
lean_object* v_c_4297_ = _args[2];
lean_object* v_numDigits_4298_ = _args[3];
lean_object* v_as_4299_ = _args[4];
lean_object* v_sz_4300_ = _args[5];
lean_object* v_i_4301_ = _args[6];
lean_object* v_b_4302_ = _args[7];
lean_object* v___y_4303_ = _args[8];
lean_object* v___y_4304_ = _args[9];
lean_object* v___y_4305_ = _args[10];
lean_object* v___y_4306_ = _args[11];
lean_object* v___y_4307_ = _args[12];
lean_object* v___y_4308_ = _args[13];
lean_object* v___y_4309_ = _args[14];
lean_object* v___y_4310_ = _args[15];
lean_object* v___y_4311_ = _args[16];
lean_object* v___y_4312_ = _args[17];
lean_object* v___y_4313_ = _args[18];
_start:
{
uint64_t v___x_7894__boxed_4314_; uint64_t v_a_7895__boxed_4315_; size_t v_sz_boxed_4316_; size_t v_i_boxed_4317_; lean_object* v_res_4318_; 
v___x_7894__boxed_4314_ = lean_unbox_uint64(v___x_4295_);
lean_dec_ref(v___x_4295_);
v_a_7895__boxed_4315_ = lean_unbox_uint64(v_a_4296_);
lean_dec_ref(v_a_4296_);
v_sz_boxed_4316_ = lean_unbox_usize(v_sz_4300_);
lean_dec(v_sz_4300_);
v_i_boxed_4317_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_res_4318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkSplitAnchorRefInfo_spec__0(v___x_7894__boxed_4314_, v_a_7895__boxed_4315_, v_c_4297_, v_numDigits_4298_, v_as_4299_, v_sz_boxed_4316_, v_i_boxed_4317_, v_b_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v_as_4299_);
lean_dec_ref(v_c_4297_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(lean_object* v_info_4343_, lean_object* v_a_4344_){
_start:
{
lean_object* v_numDigits_4346_; uint64_t v_anchor_4347_; lean_object* v_ordinal_4348_; lean_object* v___x_4349_; 
v_numDigits_4346_ = lean_ctor_get(v_info_4343_, 0);
v_anchor_4347_ = lean_ctor_get_uint64(v_info_4343_, sizeof(void*)*2);
v_ordinal_4348_ = lean_ctor_get(v_info_4343_, 1);
v___x_4349_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_4346_, v_anchor_4347_, v_a_4344_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4386_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4352_ = v___x_4349_;
v_isShared_4353_ = v_isSharedCheck_4386_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4386_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4354_ = lean_unsigned_to_nat(0u);
v___x_4355_ = lean_nat_dec_eq(v_ordinal_4348_, v___x_4354_);
if (v___x_4355_ == 0)
{
lean_object* v_ref_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
v_ref_4356_ = lean_ctor_get(v_a_4344_, 2);
v___x_4357_ = l_Lean_SourceInfo_fromRef(v_ref_4356_, v___x_4355_);
v___x_4358_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4359_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4357_, 3);
v___x_4360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4357_);
lean_ctor_set(v___x_4360_, 1, v___x_4358_);
v___x_4361_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__5));
v___x_4362_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__6));
v___x_4363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4357_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
v___x_4364_ = lean_unsigned_to_nat(1u);
v___x_4365_ = lean_nat_add(v_ordinal_4348_, v___x_4364_);
v___x_4366_ = l_Nat_reprFast(v___x_4365_);
v___x_4367_ = lean_box(2);
v___x_4368_ = l_Lean_Syntax_mkNumLit(v___x_4366_, v___x_4367_);
v___x_4369_ = l_Lean_Syntax_node3(v___x_4357_, v___x_4361_, v_a_4350_, v___x_4363_, v___x_4368_);
v___x_4370_ = l_Lean_Syntax_node2(v___x_4357_, v___x_4359_, v___x_4360_, v___x_4369_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4370_);
v___x_4372_ = v___x_4352_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
else
{
lean_object* v_ref_4374_; uint8_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4384_; 
v_ref_4374_ = lean_ctor_get(v_a_4344_, 2);
v___x_4375_ = 0;
v___x_4376_ = l_Lean_SourceInfo_fromRef(v_ref_4374_, v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__2));
v___x_4378_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__3));
lean_inc_n(v___x_4376_, 2);
v___x_4379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4376_);
lean_ctor_set(v___x_4379_, 1, v___x_4377_);
v___x_4380_ = ((lean_object*)(l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___closed__8));
v___x_4381_ = l_Lean_Syntax_node1(v___x_4376_, v___x_4380_, v_a_4350_);
v___x_4382_ = l_Lean_Syntax_node2(v___x_4376_, v___x_4378_, v___x_4379_, v___x_4381_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4382_);
v___x_4384_ = v___x_4352_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg___boxed(lean_object* v_info_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4387_, v_a_4388_);
lean_dec_ref(v_a_4388_);
lean_dec_ref(v_info_4387_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(lean_object* v_info_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_info_4391_, v_a_4392_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___boxed(lean_object* v_info_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax(v_info_4396_, v_a_4397_, v_a_4398_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec_ref(v_info_4396_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(lean_object* v_proof_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v_p_4432_; lean_object* v___x_4435_; 
lean_inc_ref(v_proof_4413_);
v___x_4435_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_4413_, v_a_4415_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4462_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4462_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4462_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = l_Lean_Expr_cleanupAnnotations(v_a_4436_);
lean_dec(v_a_4436_);
v___x_4441_ = l_Lean_Expr_isApp(v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec_ref(v___x_4440_);
lean_del_object(v___x_4438_);
v___y_4420_ = v_a_4414_;
v___y_4421_ = v_a_4415_;
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
goto v___jp_4419_;
}
else
{
lean_object* v___x_4442_; uint8_t v___x_4443_; 
v___x_4442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4440_);
v___x_4443_ = l_Lean_Expr_isApp(v___x_4442_);
if (v___x_4443_ == 0)
{
lean_dec_ref(v___x_4442_);
lean_dec_ref(v___x_4440_);
lean_del_object(v___x_4438_);
v___y_4420_ = v_a_4414_;
v___y_4421_ = v_a_4415_;
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
goto v___jp_4419_;
}
else
{
lean_object* v_arg_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v_arg_4444_ = lean_ctor_get(v___x_4440_, 1);
lean_inc_ref(v_arg_4444_);
lean_dec_ref(v___x_4440_);
v___x_4445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4442_);
v___x_4446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__1));
v___x_4447_ = l_Lean_Expr_isConstOf(v___x_4445_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; uint8_t v___x_4449_; 
lean_dec_ref(v___x_4442_);
lean_del_object(v___x_4438_);
v___x_4448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__4));
v___x_4449_ = l_Lean_Expr_isConstOf(v___x_4445_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; uint8_t v___x_4451_; 
v___x_4450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___closed__6));
v___x_4451_ = l_Lean_Expr_isConstOf(v___x_4445_, v___x_4450_);
lean_dec_ref(v___x_4445_);
if (v___x_4451_ == 0)
{
lean_dec_ref(v_arg_4444_);
v___y_4420_ = v_a_4414_;
v___y_4421_ = v_a_4415_;
v___y_4422_ = v_a_4416_;
v___y_4423_ = v_a_4417_;
goto v___jp_4419_;
}
else
{
lean_dec_ref(v_proof_4413_);
v_p_4432_ = v_arg_4444_;
goto v___jp_4431_;
}
}
else
{
lean_dec_ref(v___x_4445_);
lean_dec_ref(v_proof_4413_);
v_p_4432_ = v_arg_4444_;
goto v___jp_4431_;
}
}
else
{
lean_object* v_arg_4452_; uint8_t v___x_4453_; 
lean_dec_ref(v___x_4445_);
lean_dec_ref(v_proof_4413_);
v_arg_4452_ = lean_ctor_get(v___x_4442_, 1);
lean_inc_ref(v_arg_4452_);
lean_dec_ref(v___x_4442_);
v___x_4453_ = l_Lean_Expr_isFalse(v_arg_4452_);
lean_dec_ref(v_arg_4452_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_dec_ref(v_arg_4444_);
v___x_4454_ = lean_box(0);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4454_);
v___x_4456_ = v___x_4438_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4460_; 
v___x_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4458_, 0, v_arg_4444_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4458_);
v___x_4460_ = v___x_4438_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v_proof_4413_);
v_a_4463_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4435_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4435_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
v___jp_4419_:
{
if (lean_obj_tag(v_proof_4413_) == 6)
{
lean_object* v_body_4424_; uint8_t v___x_4425_; 
v_body_4424_ = lean_ctor_get(v_proof_4413_, 2);
lean_inc_ref(v_body_4424_);
lean_dec_ref_known(v_proof_4413_, 3);
v___x_4425_ = l_Lean_Expr_hasLooseBVars(v_body_4424_);
if (v___x_4425_ == 0)
{
v_proof_4413_ = v_body_4424_;
v_a_4414_ = v___y_4420_;
v_a_4415_ = v___y_4421_;
v_a_4416_ = v___y_4422_;
v_a_4417_ = v___y_4423_;
goto _start;
}
else
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_dec_ref(v_body_4424_);
v___x_4427_ = lean_box(0);
v___x_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
return v___x_4428_;
}
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref(v_proof_4413_);
v___x_4429_ = lean_box(0);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
}
v___jp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v_p_4432_);
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go___boxed(lean_object* v_proof_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_proof_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec(v_a_4473_);
lean_dec_ref(v_a_4472_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(lean_object* v_e_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v___x_4481_; 
v___x_4481_ = l_Lean_Expr_hasMVar(v_e_4478_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v_e_4478_);
return v___x_4482_;
}
else
{
lean_object* v___x_4483_; lean_object* v_mctx_4484_; lean_object* v___x_4485_; lean_object* v_fst_4486_; lean_object* v_snd_4487_; lean_object* v___x_4488_; lean_object* v_cache_4489_; lean_object* v_zetaDeltaFVarIds_4490_; lean_object* v_postponed_4491_; lean_object* v_diag_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4501_; 
v___x_4483_ = lean_st_ref_get(v___y_4479_);
v_mctx_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc_ref(v_mctx_4484_);
lean_dec(v___x_4483_);
v___x_4485_ = l_Lean_instantiateMVarsCore(v_mctx_4484_, v_e_4478_);
v_fst_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_fst_4486_);
v_snd_4487_ = lean_ctor_get(v___x_4485_, 1);
lean_inc(v_snd_4487_);
lean_dec_ref(v___x_4485_);
v___x_4488_ = lean_st_ref_take(v___y_4479_);
v_cache_4489_ = lean_ctor_get(v___x_4488_, 1);
v_zetaDeltaFVarIds_4490_ = lean_ctor_get(v___x_4488_, 2);
v_postponed_4491_ = lean_ctor_get(v___x_4488_, 3);
v_diag_4492_ = lean_ctor_get(v___x_4488_, 4);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4488_, 0);
lean_dec(v_unused_4502_);
v___x_4494_ = v___x_4488_;
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_diag_4492_);
lean_inc(v_postponed_4491_);
lean_inc(v_zetaDeltaFVarIds_4490_);
lean_inc(v_cache_4489_);
lean_dec(v___x_4488_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4501_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v_snd_4487_);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_snd_4487_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_cache_4489_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_zetaDeltaFVarIds_4490_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_postponed_4491_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_diag_4492_);
v___x_4497_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = lean_st_ref_put(v___y_4479_, v___x_4497_);
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v_fst_4486_);
return v___x_4499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* v_e_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4503_, v___y_4504_);
lean_dec(v___y_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(lean_object* v_e_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v_e_4507_, v___y_4509_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___boxed(lean_object* v_e_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0(v_e_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(lean_object* v_mvarId_4521_, lean_object* v_x_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4521_, v_x_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_a_4537_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4528_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4528_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_4545_, lean_object* v_x_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4545_, v_x_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(lean_object* v_00_u03b1_4553_, lean_object* v_mvarId_4554_, lean_object* v_x_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4554_, v_x_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___boxed(lean_object* v_00_u03b1_4562_, lean_object* v_mvarId_4563_, lean_object* v_x_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1(v_00_u03b1_4562_, v_mvarId_4563_, v_x_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(lean_object* v___x_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4588_; 
v___x_4577_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__0___redArg(v___x_4571_, v___y_4573_);
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4588_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4588_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
uint8_t v___x_4582_; 
v___x_4582_ = l_Lean_Expr_hasSyntheticSorry(v_a_4578_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; 
lean_del_object(v___x_4580_);
v___x_4583_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_go(v_a_4578_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
return v___x_4583_;
}
else
{
lean_object* v___x_4584_; lean_object* v___x_4586_; 
lean_dec(v_a_4578_);
v___x_4584_ = lean_box(0);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4584_);
v___x_4586_ = v___x_4580_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4584_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed(lean_object* v___x_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0(v___x_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(lean_object* v_mvarId_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v___x_4602_; lean_object* v___f_4603_; lean_object* v___x_4604_; 
lean_inc(v_mvarId_4596_);
v___x_4602_ = l_Lean_mkMVar(v_mvarId_4596_);
v___f_4603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4603_, 0, v___x_4602_);
v___x_4604_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f_spec__1___redArg(v_mvarId_4596_, v___f_4603_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f___boxed(lean_object* v_mvarId_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4611_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(lean_object* v_x_4633_){
_start:
{
if (lean_obj_tag(v_x_4633_) == 0)
{
uint8_t v___x_4634_; 
v___x_4634_ = 1;
return v___x_4634_;
}
else
{
lean_object* v_head_4635_; lean_object* v_tail_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
v_head_4635_ = lean_ctor_get(v_x_4633_, 0);
lean_inc_n(v_head_4635_, 2);
v_tail_4636_ = lean_ctor_get(v_x_4633_, 1);
lean_inc(v_tail_4636_);
lean_dec_ref_known(v_x_4633_, 2);
v___x_4637_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__1));
v___x_4638_ = l_Lean_Syntax_isOfKind(v_head_4635_, v___x_4637_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; uint8_t v___x_4640_; 
v___x_4639_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__3));
lean_inc(v_head_4635_);
v___x_4640_ = l_Lean_Syntax_isOfKind(v_head_4635_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_dec(v_head_4635_);
v_x_4633_ = v_tail_4636_;
goto _start;
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4642_ = lean_unsigned_to_nat(1u);
v___x_4643_ = l_Lean_Syntax_getArg(v_head_4635_, v___x_4642_);
lean_dec(v_head_4635_);
v___x_4644_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4645_ = l_Lean_Syntax_isOfKind(v___x_4643_, v___x_4644_);
if (v___x_4645_ == 0)
{
v_x_4633_ = v_tail_4636_;
goto _start;
}
else
{
lean_dec(v_tail_4636_);
return v___x_4638_;
}
}
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4647_ = lean_unsigned_to_nat(3u);
v___x_4648_ = l_Lean_Syntax_getArg(v_head_4635_, v___x_4647_);
lean_dec(v_head_4635_);
v___x_4649_ = ((lean_object*)(l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___closed__5));
v___x_4650_ = l_Lean_Syntax_isOfKind(v___x_4648_, v___x_4649_);
if (v___x_4650_ == 0)
{
v_x_4633_ = v_tail_4636_;
goto _start;
}
else
{
uint8_t v___x_4652_; 
lean_dec(v_tail_4636_);
v___x_4652_ = 0;
return v___x_4652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0___boxed(lean_object* v_x_4653_){
_start:
{
uint8_t v_res_4654_; lean_object* v_r_4655_; 
v_res_4654_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_x_4653_);
v_r_4655_ = lean_box(v_res_4654_);
return v_r_4655_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(lean_object* v_seq_4656_){
_start:
{
uint8_t v___x_4657_; 
v___x_4657_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_seq_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq___boxed(lean_object* v_seq_4658_){
_start:
{
uint8_t v_res_4659_; lean_object* v_r_4660_; 
v_res_4659_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq(v_seq_4658_);
v_r_4660_ = lean_box(v_res_4659_);
return v_r_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(lean_object* v_seq_4676_, lean_object* v_a_4677_){
_start:
{
if (lean_obj_tag(v_seq_4676_) == 0)
{
lean_object* v_ref_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v_ref_4679_ = lean_ctor_get(v_a_4677_, 2);
v___x_4680_ = 0;
v___x_4681_ = l_Lean_SourceInfo_fromRef(v_ref_4679_, v___x_4680_);
v___x_4682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__0));
v___x_4683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__1));
lean_inc(v___x_4681_);
v___x_4684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4681_);
lean_ctor_set(v___x_4684_, 1, v___x_4682_);
v___x_4685_ = l_Lean_Syntax_node1(v___x_4681_, v___x_4683_, v___x_4684_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
else
{
lean_object* v_tail_4687_; 
v_tail_4687_ = lean_ctor_get(v_seq_4676_, 1);
if (lean_obj_tag(v_tail_4687_) == 0)
{
lean_object* v_head_4688_; lean_object* v___x_4689_; 
v_head_4688_ = lean_ctor_get(v_seq_4676_, 0);
lean_inc(v_head_4688_);
lean_dec_ref_known(v_seq_4676_, 2);
v___x_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4689_, 0, v_head_4688_);
return v___x_4689_;
}
else
{
lean_object* v_head_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4712_; 
lean_inc(v_tail_4687_);
v_head_4690_ = lean_ctor_get(v_seq_4676_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v_seq_4676_);
if (v_isSharedCheck_4712_ == 0)
{
lean_object* v_unused_4713_; 
v_unused_4713_ = lean_ctor_get(v_seq_4676_, 1);
lean_dec(v_unused_4713_);
v___x_4692_ = v_seq_4676_;
v_isShared_4693_ = v_isSharedCheck_4712_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_head_4690_);
lean_dec(v_seq_4676_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4712_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4711_; 
v___x_4694_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_tail_4687_, v_a_4677_);
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4694_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4697_ = v___x_4694_;
v_isShared_4698_ = v_isSharedCheck_4711_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4694_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4711_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v_ref_4699_; uint8_t v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; 
v_ref_4699_ = lean_ctor_get(v_a_4677_, 2);
v___x_4700_ = 0;
v___x_4701_ = l_Lean_SourceInfo_fromRef(v_ref_4699_, v___x_4700_);
v___x_4702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4701_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set_tag(v___x_4692_, 2);
lean_ctor_set(v___x_4692_, 1, v___x_4703_);
lean_ctor_set(v___x_4692_, 0, v___x_4701_);
v___x_4705_ = v___x_4692_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4710_, 1, v___x_4703_);
v___x_4705_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4706_; lean_object* v___x_4708_; 
v___x_4706_ = l_Lean_Syntax_node3(v___x_4701_, v___x_4702_, v_head_4690_, v___x_4705_, v_a_4695_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 0, v___x_4706_);
v___x_4708_ = v___x_4697_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v___x_4706_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___boxed(lean_object* v_seq_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4714_, v_a_4715_);
lean_dec_ref(v_a_4715_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(lean_object* v_seq_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4718_, v_a_4719_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___boxed(lean_object* v_seq_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq(v_seq_4723_, v_a_4724_, v_a_4725_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(lean_object* v_cases_4728_, lean_object* v_seq_4729_, lean_object* v_a_4730_){
_start:
{
if (lean_obj_tag(v_seq_4729_) == 0)
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v_cases_4728_);
return v___x_4732_;
}
else
{
lean_object* v___x_4733_; lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4748_; 
v___x_4733_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg(v_seq_4729_, v_a_4730_);
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4736_ = v___x_4733_;
v_isShared_4737_ = v_isSharedCheck_4748_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4733_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4748_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v_ref_4738_; uint8_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
v_ref_4738_ = lean_ctor_get(v_a_4730_, 2);
v___x_4739_ = 0;
v___x_4740_ = l_Lean_SourceInfo_fromRef(v_ref_4738_, v___x_4739_);
v___x_4741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__3));
v___x_4742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkAndThenSeq___redArg___closed__4));
lean_inc(v___x_4740_);
v___x_4743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4740_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = l_Lean_Syntax_node3(v___x_4740_, v___x_4741_, v_cases_4728_, v___x_4743_, v_a_4734_);
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 0, v___x_4744_);
v___x_4746_ = v___x_4736_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4744_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg___boxed(lean_object* v_cases_4749_, lean_object* v_seq_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4749_, v_seq_4750_, v_a_4751_);
lean_dec_ref(v_a_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(lean_object* v_cases_4754_, lean_object* v_seq_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4754_, v_seq_4755_, v_a_4756_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___boxed(lean_object* v_cases_4760_, lean_object* v_seq_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen(v_cases_4760_, v_seq_4761_, v_a_4762_, v_a_4763_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
return v_res_4765_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(lean_object* v_x_4766_, lean_object* v_x_4767_){
_start:
{
if (lean_obj_tag(v_x_4766_) == 0)
{
if (lean_obj_tag(v_x_4767_) == 0)
{
uint8_t v___x_4768_; 
v___x_4768_ = 1;
return v___x_4768_;
}
else
{
uint8_t v___x_4769_; 
v___x_4769_ = 0;
return v___x_4769_;
}
}
else
{
if (lean_obj_tag(v_x_4767_) == 0)
{
uint8_t v___x_4770_; 
v___x_4770_ = 0;
return v___x_4770_;
}
else
{
lean_object* v_head_4771_; lean_object* v_tail_4772_; lean_object* v_head_4773_; lean_object* v_tail_4774_; uint8_t v___x_4775_; 
v_head_4771_ = lean_ctor_get(v_x_4766_, 0);
v_tail_4772_ = lean_ctor_get(v_x_4766_, 1);
v_head_4773_ = lean_ctor_get(v_x_4767_, 0);
v_tail_4774_ = lean_ctor_get(v_x_4767_, 1);
v___x_4775_ = l_Lean_Syntax_structEq(v_head_4771_, v_head_4773_);
if (v___x_4775_ == 0)
{
return v___x_4775_;
}
else
{
v_x_4766_ = v_tail_4772_;
v_x_4767_ = v_tail_4774_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0___boxed(lean_object* v_x_4777_, lean_object* v_x_4778_){
_start:
{
uint8_t v_res_4779_; lean_object* v_r_4780_; 
v_res_4779_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v_x_4777_, v_x_4778_);
lean_dec(v_x_4778_);
lean_dec(v_x_4777_);
v_r_4780_ = lean_box(v_res_4779_);
return v_r_4780_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(lean_object* v_alt_4781_, lean_object* v___x_4782_, lean_object* v_as_4783_, size_t v_i_4784_, size_t v_stop_4785_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_eq(v_i_4784_, v_stop_4785_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4791_ = lean_array_uget_borrowed(v_as_4783_, v_i_4784_);
v___x_4792_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__0(v___x_4791_, v_alt_4781_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4793_ = lean_unsigned_to_nat(0u);
v___x_4794_ = lean_nat_dec_lt(v___x_4793_, v___x_4782_);
if (v___x_4794_ == 0)
{
goto v___jp_4786_;
}
else
{
return v___x_4794_;
}
}
else
{
goto v___jp_4786_;
}
}
else
{
uint8_t v___x_4795_; 
v___x_4795_ = 0;
return v___x_4795_;
}
v___jp_4786_:
{
size_t v___x_4787_; size_t v___x_4788_; 
v___x_4787_ = ((size_t)1ULL);
v___x_4788_ = lean_usize_add(v_i_4784_, v___x_4787_);
v_i_4784_ = v___x_4788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1___boxed(lean_object* v_alt_4796_, lean_object* v___x_4797_, lean_object* v_as_4798_, lean_object* v_i_4799_, lean_object* v_stop_4800_){
_start:
{
size_t v_i_boxed_4801_; size_t v_stop_boxed_4802_; uint8_t v_res_4803_; lean_object* v_r_4804_; 
v_i_boxed_4801_ = lean_unbox_usize(v_i_4799_);
lean_dec(v_i_4799_);
v_stop_boxed_4802_ = lean_unbox_usize(v_stop_4800_);
lean_dec(v_stop_4800_);
v_res_4803_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4796_, v___x_4797_, v_as_4798_, v_i_boxed_4801_, v_stop_boxed_4802_);
lean_dec_ref(v_as_4798_);
lean_dec(v___x_4797_);
lean_dec(v_alt_4796_);
v_r_4804_ = lean_box(v_res_4803_);
return v_r_4804_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(lean_object* v_alts_4805_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4806_ = lean_unsigned_to_nat(0u);
v___x_4807_ = lean_array_get_size(v_alts_4805_);
v___x_4808_ = lean_nat_dec_lt(v___x_4806_, v___x_4807_);
if (v___x_4808_ == 0)
{
uint8_t v___x_4809_; 
v___x_4809_ = 1;
return v___x_4809_;
}
else
{
lean_object* v_alt_4810_; uint8_t v___x_4811_; 
v_alt_4810_ = lean_array_fget_borrowed(v_alts_4805_, v___x_4806_);
lean_inc(v_alt_4810_);
v___x_4811_ = l_List_all___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleSeq_spec__0(v_alt_4810_);
if (v___x_4811_ == 0)
{
return v___x_4811_;
}
else
{
if (v___x_4808_ == 0)
{
return v___x_4808_;
}
else
{
size_t v___x_4812_; size_t v___x_4813_; uint8_t v___x_4814_; 
v___x_4812_ = ((size_t)0ULL);
v___x_4813_ = lean_usize_of_nat(v___x_4807_);
v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts_spec__1(v_alt_4810_, v___x_4807_, v_alts_4805_, v___x_4812_, v___x_4813_);
if (v___x_4814_ == 0)
{
return v___x_4808_;
}
else
{
uint8_t v___x_4815_; 
v___x_4815_ = 0;
return v___x_4815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts___boxed(lean_object* v_alts_4816_){
_start:
{
uint8_t v_res_4817_; lean_object* v_r_4818_; 
v_res_4817_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4816_);
lean_dec_ref(v_alts_4816_);
v_r_4818_ = lean_box(v_res_4817_);
return v_r_4818_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Action_isSorryAlt(lean_object* v_alt_4826_){
_start:
{
if (lean_obj_tag(v_alt_4826_) == 1)
{
lean_object* v_tail_4827_; 
v_tail_4827_ = lean_ctor_get(v_alt_4826_, 1);
if (lean_obj_tag(v_tail_4827_) == 0)
{
lean_object* v_head_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_head_4828_ = lean_ctor_get(v_alt_4826_, 0);
lean_inc(v_head_4828_);
lean_dec_ref_known(v_alt_4826_, 2);
v___x_4829_ = ((lean_object*)(l_Lean_Meta_Grind_Action_isSorryAlt___closed__1));
v___x_4830_ = l_Lean_Syntax_isOfKind(v_head_4828_, v___x_4829_);
return v___x_4830_;
}
else
{
uint8_t v___x_4831_; 
lean_dec_ref_known(v_alt_4826_, 2);
v___x_4831_ = 0;
return v___x_4831_;
}
}
else
{
uint8_t v___x_4832_; 
lean_dec(v_alt_4826_);
v___x_4832_ = 0;
return v___x_4832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_isSorryAlt___boxed(lean_object* v_alt_4833_){
_start:
{
uint8_t v_res_4834_; lean_object* v_r_4835_; 
v_res_4834_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_alt_4833_);
v_r_4835_ = lean_box(v_res_4834_);
return v_r_4835_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(lean_object* v_x_4836_, lean_object* v_x_4837_, lean_object* v___y_4838_){
_start:
{
if (lean_obj_tag(v_x_4836_) == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = l_List_reverse___redArg(v_x_4837_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
else
{
lean_object* v_head_4842_; lean_object* v_tail_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4861_; 
v_head_4842_ = lean_ctor_get(v_x_4836_, 0);
v_tail_4843_ = lean_ctor_get(v_x_4836_, 1);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_x_4836_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4845_ = v_x_4836_;
v_isShared_4846_ = v_isSharedCheck_4861_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_tail_4843_);
lean_inc(v_head_4842_);
lean_dec(v_x_4836_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4861_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_head_4842_, v___y_4838_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4850_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc(v_a_4848_);
lean_dec_ref_known(v___x_4847_, 1);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 1, v_x_4837_);
lean_ctor_set(v___x_4845_, 0, v_a_4848_);
v___x_4850_ = v___x_4845_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4848_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v_x_4837_);
v___x_4850_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
v_x_4836_ = v_tail_4843_;
v_x_4837_ = v___x_4850_;
goto _start;
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_del_object(v___x_4845_);
lean_dec(v_tail_4843_);
lean_dec(v_x_4837_);
v_a_4853_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4847_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4847_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg___boxed(lean_object* v_x_4862_, lean_object* v_x_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4862_, v_x_4863_, v___y_4864_);
lean_dec_ref(v___y_4864_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(lean_object* v_cases_4867_, lean_object* v_alts_4868_, uint8_t v_compress_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v_seq_4874_; 
if (v_compress_4869_ == 0)
{
goto v___jp_4877_;
}
else
{
uint8_t v___x_4887_; 
v___x_4887_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_isCompressibleAlts(v_alts_4868_);
if (v___x_4887_ == 0)
{
goto v___jp_4877_;
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; uint8_t v___x_4890_; 
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = lean_array_get_size(v_alts_4868_);
v___x_4890_ = lean_nat_dec_lt(v___x_4888_, v___x_4889_);
if (v___x_4890_ == 0)
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref(v_alts_4868_);
v___x_4891_ = lean_box(0);
v___x_4892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4892_, 0, v_cases_4867_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
return v___x_4893_;
}
else
{
lean_object* v___x_4894_; lean_object* v_firstAlt_4895_; uint8_t v___x_4896_; 
v___x_4894_ = lean_box(0);
v_firstAlt_4895_ = lean_array_get(v___x_4894_, v_alts_4868_, v___x_4888_);
lean_dec_ref(v_alts_4868_);
lean_inc(v_firstAlt_4895_);
v___x_4896_ = l_Lean_Meta_Grind_Action_isSorryAlt(v_firstAlt_4895_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4906_; 
v___x_4897_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesAndThen___redArg(v_cases_4867_, v_firstAlt_4895_, v_a_4870_);
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4902_, 0, v_a_4898_);
lean_ctor_set(v___x_4902_, 1, v___x_4894_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_4902_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
else
{
lean_object* v___x_4907_; 
lean_dec(v_cases_4867_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v_firstAlt_4895_);
return v___x_4907_;
}
}
}
}
v___jp_4873_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4875_, 0, v_cases_4867_);
lean_ctor_set(v___x_4875_, 1, v_seq_4874_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
return v___x_4876_;
}
v___jp_4877_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; uint8_t v___x_4880_; 
v___x_4878_ = lean_array_get_size(v_alts_4868_);
v___x_4879_ = lean_unsigned_to_nat(1u);
v___x_4880_ = lean_nat_dec_eq(v___x_4878_, v___x_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = lean_array_to_list(v_alts_4868_);
v___x_4882_ = lean_box(0);
v___x_4883_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v___x_4881_, v___x_4882_, v_a_4870_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4883_, 1);
v_seq_4874_ = v_a_4884_;
goto v___jp_4873_;
}
else
{
lean_dec(v_cases_4867_);
return v___x_4883_;
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = lean_array_fget(v_alts_4868_, v___x_4885_);
lean_dec_ref(v_alts_4868_);
v_seq_4874_ = v___x_4886_;
goto v___jp_4873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq___boxed(lean_object* v_cases_4908_, lean_object* v_alts_4909_, lean_object* v_compress_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
uint8_t v_compress_boxed_4914_; lean_object* v_res_4915_; 
v_compress_boxed_4914_ = lean_unbox(v_compress_4910_);
v_res_4915_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_cases_4908_, v_alts_4909_, v_compress_boxed_4914_, v_a_4911_, v_a_4912_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(lean_object* v_x_4916_, lean_object* v_x_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___redArg(v_x_4916_, v_x_4917_, v___y_4918_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0___boxed(lean_object* v_x_4922_, lean_object* v_x_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq_spec__0(v_x_4922_, v_x_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(lean_object* v_e_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v___x_4931_; lean_object* v_env_4932_; uint8_t v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4931_ = lean_st_ref_get(v___y_4929_);
v_env_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc_ref(v_env_4932_);
lean_dec(v___x_4931_);
v___x_4933_ = l_Lean_Meta_isMatcherAppCore(v_env_4932_, v_e_4928_);
v___x_4934_ = lean_box(v___x_4933_);
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg___boxed(lean_object* v_e_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v_e_4936_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(lean_object* v_e_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v_e_4940_, v___y_4950_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___boxed(lean_object* v_e_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0(v_e_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v_e_4953_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(lean_object* v_x_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4977_; 
lean_inc(v___y_4971_);
lean_inc_ref(v___y_4970_);
lean_inc(v___y_4969_);
lean_inc_ref(v___y_4968_);
lean_inc(v___y_4967_);
v___x_4977_ = lean_apply_10(v_x_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, lean_box(0));
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed(lean_object* v_x_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0(v_x_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(lean_object* v_mvarId_4990_, lean_object* v_x_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v___f_5002_; lean_object* v___x_5003_; 
lean_inc(v___y_4996_);
lean_inc_ref(v___y_4995_);
lean_inc(v___y_4994_);
lean_inc_ref(v___y_4993_);
lean_inc(v___y_4992_);
v___f_5002_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_5002_, 0, v_x_4991_);
lean_closure_set(v___f_5002_, 1, v___y_4992_);
lean_closure_set(v___f_5002_, 2, v___y_4993_);
lean_closure_set(v___f_5002_, 3, v___y_4994_);
lean_closure_set(v___f_5002_, 4, v___y_4995_);
lean_closure_set(v___f_5002_, 5, v___y_4996_);
v___x_5003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4990_, v___f_5002_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
if (lean_obj_tag(v___x_5003_) == 0)
{
return v___x_5003_;
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg___boxed(lean_object* v_mvarId_5012_, lean_object* v_x_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5012_, v_x_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(lean_object* v_00_u03b1_5025_, lean_object* v_mvarId_5026_, lean_object* v_x_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5026_, v_x_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___boxed(lean_object* v_00_u03b1_5039_, lean_object* v_mvarId_5040_, lean_object* v_x_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1(v_00_u03b1_5039_, v_mvarId_5040_, v_x_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(lean_object* v_e_5053_, lean_object* v___y_5054_){
_start:
{
uint8_t v___x_5056_; 
v___x_5056_ = l_Lean_Expr_hasMVar(v_e_5053_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; 
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v_e_5053_);
return v___x_5057_;
}
else
{
lean_object* v___x_5058_; lean_object* v_mctx_5059_; lean_object* v___x_5060_; lean_object* v_fst_5061_; lean_object* v_snd_5062_; lean_object* v___x_5063_; lean_object* v_cache_5064_; lean_object* v_zetaDeltaFVarIds_5065_; lean_object* v_postponed_5066_; lean_object* v_diag_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5076_; 
v___x_5058_ = lean_st_ref_get(v___y_5054_);
v_mctx_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc_ref(v_mctx_5059_);
lean_dec(v___x_5058_);
v___x_5060_ = l_Lean_instantiateMVarsCore(v_mctx_5059_, v_e_5053_);
v_fst_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_fst_5061_);
v_snd_5062_ = lean_ctor_get(v___x_5060_, 1);
lean_inc(v_snd_5062_);
lean_dec_ref(v___x_5060_);
v___x_5063_ = lean_st_ref_take(v___y_5054_);
v_cache_5064_ = lean_ctor_get(v___x_5063_, 1);
v_zetaDeltaFVarIds_5065_ = lean_ctor_get(v___x_5063_, 2);
v_postponed_5066_ = lean_ctor_get(v___x_5063_, 3);
v_diag_5067_ = lean_ctor_get(v___x_5063_, 4);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5076_ == 0)
{
lean_object* v_unused_5077_; 
v_unused_5077_ = lean_ctor_get(v___x_5063_, 0);
lean_dec(v_unused_5077_);
v___x_5069_ = v___x_5063_;
v_isShared_5070_ = v_isSharedCheck_5076_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_diag_5067_);
lean_inc(v_postponed_5066_);
lean_inc(v_zetaDeltaFVarIds_5065_);
lean_inc(v_cache_5064_);
lean_dec(v___x_5063_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5076_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v_snd_5062_);
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_snd_5062_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_cache_5064_);
lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_zetaDeltaFVarIds_5065_);
lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_postponed_5066_);
lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_diag_5067_);
v___x_5072_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = lean_st_ref_put(v___y_5054_, v___x_5072_);
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v_fst_5061_);
return v___x_5074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg___boxed(lean_object* v_e_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_e_5078_, v___y_5079_);
lean_dec(v___y_5079_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(lean_object* v_e_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v_e_5082_, v___y_5089_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___boxed(lean_object* v_e_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5(v_e_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
return v_res_5105_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5107_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__0));
v___x_5108_ = l_Lean_stringToMessageData(v___x_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(lean_object* v___x_5109_, lean_object* v_c_5110_, lean_object* v_a_5111_, lean_object* v_numCases_5112_, uint8_t v_isRec_5113_, lean_object* v_anchorInfo_x3f_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v_mvarIds_5127_; lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_5109_, v___y_5115_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___y_5180_; lean_object* v___x_5232_; uint8_t v___x_5235_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5178_);
lean_dec_ref_known(v___x_5177_, 1);
v___x_5232_ = lean_unsigned_to_nat(1u);
v___x_5235_ = lean_nat_dec_lt(v___x_5232_, v_numCases_5112_);
if (v___x_5235_ == 0)
{
if (v_isRec_5113_ == 0)
{
lean_inc(v_a_5178_);
v___y_5180_ = v_a_5178_;
goto v___jp_5179_;
}
else
{
goto v___jp_5233_;
}
}
else
{
goto v___jp_5233_;
}
v___jp_5179_:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; 
v___x_5181_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5110_);
lean_inc_ref(v___x_5109_);
v___x_5182_ = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(v___x_5109_, v___y_5180_, v_numCases_5112_, v___x_5181_, v___y_5118_, v___y_5121_, v___y_5123_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v___x_5183_; 
lean_dec_ref_known(v___x_5182_, 1);
lean_inc_ref(v___x_5109_);
v___x_5183_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v___x_5109_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_toCold_5184_; lean_object* v_options_5185_; uint8_t v_hasTrace_5186_; 
lean_dec_ref_known(v___x_5183_, 1);
v_toCold_5184_ = lean_ctor_get(v___y_5123_, 0);
v_options_5185_ = lean_ctor_get(v_toCold_5184_, 2);
v_hasTrace_5186_ = lean_ctor_get_uint8(v_options_5185_, sizeof(void*)*1);
if (v_hasTrace_5186_ == 0)
{
lean_dec(v_a_5178_);
goto v___jp_5130_;
}
else
{
lean_object* v_inheritedTraceOptions_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; 
v_inheritedTraceOptions_5187_ = lean_ctor_get(v_toCold_5184_, 11);
v___x_5188_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__1));
v___x_5189_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___closed__2);
v___x_5190_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5187_, v_options_5185_, v___x_5189_);
if (v___x_5190_ == 0)
{
lean_dec(v_a_5178_);
goto v___jp_5130_;
}
else
{
lean_object* v___x_5191_; 
v___x_5191_ = l_Lean_Meta_Grind_updateLastTag(v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
lean_dec_ref_known(v___x_5191_, 1);
lean_inc_ref(v___x_5109_);
v___x_5192_ = l_Lean_MessageData_ofExpr(v___x_5109_);
v___x_5193_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___closed__1);
v___x_5194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5192_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
v___x_5195_ = l_Nat_reprFast(v_a_5178_);
v___x_5196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5195_);
v___x_5197_ = l_Lean_MessageData_ofFormat(v___x_5196_);
v___x_5198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5194_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus_spec__1___redArg(v___x_5188_, v___x_5198_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_dec_ref_known(v___x_5199_, 1);
goto v___jp_5130_;
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_a_5111_);
lean_dec_ref(v_c_5110_);
lean_dec_ref(v___x_5109_);
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
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
lean_dec(v_a_5178_);
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_a_5111_);
lean_dec_ref(v_c_5110_);
lean_dec_ref(v___x_5109_);
v_a_5208_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5191_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5191_);
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
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_dec(v_a_5178_);
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_a_5111_);
lean_dec_ref(v_c_5110_);
lean_dec_ref(v___x_5109_);
v_a_5216_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5183_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5183_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
lean_dec(v_a_5178_);
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_a_5111_);
lean_dec_ref(v_c_5110_);
lean_dec_ref(v___x_5109_);
v_a_5224_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_5182_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5182_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
v___jp_5233_:
{
lean_object* v___x_5234_; 
v___x_5234_ = lean_nat_add(v_a_5178_, v___x_5232_);
v___y_5180_ = v___x_5234_;
goto v___jp_5179_;
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_numCases_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_c_5110_);
lean_dec_ref(v___x_5109_);
v_a_5236_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5177_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5177_);
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
v___jp_5126_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5128_, 0, v_mvarIds_5127_);
lean_ctor_set(v___x_5128_, 1, v_anchorInfo_x3f_5114_);
v___x_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
return v___x_5129_;
}
v___jp_5130_:
{
lean_object* v___x_5131_; 
v___x_5131_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_Grind_Action_splitCore_spec__0___redArg(v___x_5109_, v___y_5124_);
if (lean_obj_tag(v_c_5110_) == 1)
{
lean_object* v_e_5132_; lean_object* v_binderType_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
lean_dec_ref(v___x_5131_);
lean_dec_ref(v___x_5109_);
v_e_5132_ = lean_ctor_get(v_c_5110_, 0);
lean_inc_ref(v_e_5132_);
lean_dec_ref_known(v_c_5110_, 2);
v_binderType_5133_ = lean_ctor_get(v_e_5132_, 1);
lean_inc_ref(v_binderType_5133_);
lean_dec_ref(v_e_5132_);
v___x_5134_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(v_binderType_5133_);
v___x_5135_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5111_, v___x_5134_, v___y_5117_, v___y_5118_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_a_5136_; 
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5135_, 1);
v_mvarIds_5127_ = v_a_5136_;
goto v___jp_5126_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
lean_dec(v_anchorInfo_x3f_5114_);
v_a_5137_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5135_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5135_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
else
{
lean_object* v_a_5145_; uint8_t v___x_5146_; 
lean_dec_ref(v_c_5110_);
v_a_5145_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5145_);
lean_dec_ref(v___x_5131_);
v___x_5146_ = lean_unbox(v_a_5145_);
lean_dec(v_a_5145_);
if (v___x_5146_ == 0)
{
lean_object* v___x_5147_; 
v___x_5147_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(v___x_5109_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5149_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v___x_5149_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(v_a_5111_, v_a_5148_, v___y_5117_, v___y_5118_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v_mvarIds_5127_ = v_a_5150_;
goto v___jp_5126_;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_anchorInfo_x3f_5114_);
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
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec(v_anchorInfo_x3f_5114_);
lean_dec(v_a_5111_);
v_a_5159_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5147_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5147_);
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
else
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Meta_Grind_casesMatch(v_a_5111_, v___x_5109_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
v_mvarIds_5127_ = v_a_5168_;
goto v___jp_5126_;
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec(v_anchorInfo_x3f_5114_);
v_a_5169_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5167_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5167_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5244_ = _args[0];
lean_object* v_c_5245_ = _args[1];
lean_object* v_a_5246_ = _args[2];
lean_object* v_numCases_5247_ = _args[3];
lean_object* v_isRec_5248_ = _args[4];
lean_object* v_anchorInfo_x3f_5249_ = _args[5];
lean_object* v___y_5250_ = _args[6];
lean_object* v___y_5251_ = _args[7];
lean_object* v___y_5252_ = _args[8];
lean_object* v___y_5253_ = _args[9];
lean_object* v___y_5254_ = _args[10];
lean_object* v___y_5255_ = _args[11];
lean_object* v___y_5256_ = _args[12];
lean_object* v___y_5257_ = _args[13];
lean_object* v___y_5258_ = _args[14];
lean_object* v___y_5259_ = _args[15];
lean_object* v___y_5260_ = _args[16];
_start:
{
uint8_t v_isRec_boxed_5261_; lean_object* v_res_5262_; 
v_isRec_boxed_5261_ = lean_unbox(v_isRec_5248_);
v_res_5262_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0(v___x_5244_, v_c_5245_, v_a_5246_, v_numCases_5247_, v_isRec_boxed_5261_, v_anchorInfo_x3f_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec(v___y_5250_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(lean_object* v_goal_5263_, uint8_t v_trace_5264_, lean_object* v___f_5265_, lean_object* v_c_5266_, lean_object* v_candidates_x3f_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v___x_5278_; lean_object* v___y_5280_; 
v___x_5278_ = lean_st_mk_ref(v_goal_5263_);
if (v_trace_5264_ == 0)
{
lean_object* v___x_5299_; lean_object* v___x_5300_; 
lean_dec(v_candidates_x3f_5267_);
v___x_5299_ = lean_box(0);
lean_inc(v___x_5278_);
v___x_5300_ = lean_apply_12(v___f_5265_, v___x_5299_, v___x_5278_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, lean_box(0));
v___y_5280_ = v___x_5300_;
goto v___jp_5279_;
}
else
{
lean_object* v___x_5301_; 
v___x_5301_ = l_Lean_Meta_Grind_mkSplitAnchorRefInfo(v_c_5266_, v_candidates_x3f_5267_, v___x_5278_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc(v_a_5302_);
lean_dec_ref_known(v___x_5301_, 1);
v___x_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5303_, 0, v_a_5302_);
lean_inc(v___x_5278_);
v___x_5304_ = lean_apply_12(v___f_5265_, v___x_5303_, v___x_5278_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, lean_box(0));
v___y_5280_ = v___x_5304_;
goto v___jp_5279_;
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec(v___x_5278_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___f_5265_);
v_a_5305_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5301_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5301_);
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
v___jp_5279_:
{
if (lean_obj_tag(v___y_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5290_; 
v_a_5281_ = lean_ctor_get(v___y_5280_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___y_5280_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5283_ = v___y_5280_;
v_isShared_5284_ = v_isSharedCheck_5290_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___y_5280_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5290_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5288_; 
v___x_5285_ = lean_st_ref_get(v___x_5278_);
lean_dec(v___x_5278_);
v___x_5286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5286_, 0, v_a_5281_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 0, v___x_5286_);
v___x_5288_ = v___x_5283_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5286_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
else
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
lean_dec(v___x_5278_);
v_a_5291_ = lean_ctor_get(v___y_5280_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___y_5280_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___y_5280_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___y_5280_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed(lean_object* v_goal_5313_, lean_object* v_trace_5314_, lean_object* v___f_5315_, lean_object* v_c_5316_, lean_object* v_candidates_x3f_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
uint8_t v_trace_boxed_5328_; lean_object* v_res_5329_; 
v_trace_boxed_5328_ = lean_unbox(v_trace_5314_);
v_res_5329_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1(v_goal_5313_, v_trace_boxed_5328_, v___f_5315_, v_c_5316_, v_candidates_x3f_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
lean_dec_ref(v_c_5316_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(lean_object* v_x_5330_, lean_object* v_x_5331_, lean_object* v_x_5332_, lean_object* v_x_5333_){
_start:
{
lean_object* v_ks_5334_; lean_object* v_vs_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5359_; 
v_ks_5334_ = lean_ctor_get(v_x_5330_, 0);
v_vs_5335_ = lean_ctor_get(v_x_5330_, 1);
v_isSharedCheck_5359_ = !lean_is_exclusive(v_x_5330_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5337_ = v_x_5330_;
v_isShared_5338_ = v_isSharedCheck_5359_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_vs_5335_);
lean_inc(v_ks_5334_);
lean_dec(v_x_5330_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5359_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5339_ = lean_array_get_size(v_ks_5334_);
v___x_5340_ = lean_nat_dec_lt(v_x_5331_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
lean_dec(v_x_5331_);
v___x_5341_ = lean_array_push(v_ks_5334_, v_x_5332_);
v___x_5342_ = lean_array_push(v_vs_5335_, v_x_5333_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 1, v___x_5342_);
lean_ctor_set(v___x_5337_, 0, v___x_5341_);
v___x_5344_ = v___x_5337_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v___x_5342_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
else
{
lean_object* v_k_x27_5346_; uint8_t v___x_5347_; 
v_k_x27_5346_ = lean_array_fget_borrowed(v_ks_5334_, v_x_5331_);
v___x_5347_ = l_Lean_instBEqMVarId_beq(v_x_5332_, v_k_x27_5346_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5349_; 
if (v_isShared_5338_ == 0)
{
v___x_5349_ = v___x_5337_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_ks_5334_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_vs_5335_);
v___x_5349_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5350_; lean_object* v___x_5351_; 
v___x_5350_ = lean_unsigned_to_nat(1u);
v___x_5351_ = lean_nat_add(v_x_5331_, v___x_5350_);
lean_dec(v_x_5331_);
v_x_5330_ = v___x_5349_;
v_x_5331_ = v___x_5351_;
goto _start;
}
}
else
{
lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5354_ = lean_array_fset(v_ks_5334_, v_x_5331_, v_x_5332_);
v___x_5355_ = lean_array_fset(v_vs_5335_, v_x_5331_, v_x_5333_);
lean_dec(v_x_5331_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 1, v___x_5355_);
lean_ctor_set(v___x_5337_, 0, v___x_5354_);
v___x_5357_ = v___x_5337_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5358_, 1, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(lean_object* v_n_5360_, lean_object* v_k_5361_, lean_object* v_v_5362_){
_start:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5363_ = lean_unsigned_to_nat(0u);
v___x_5364_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(v_n_5360_, v___x_5363_, v_k_5361_, v_v_5362_);
return v___x_5364_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(lean_object* v_x_5366_, size_t v_x_5367_, size_t v_x_5368_, lean_object* v_x_5369_, lean_object* v_x_5370_){
_start:
{
if (lean_obj_tag(v_x_5366_) == 0)
{
lean_object* v_es_5371_; size_t v___x_5372_; size_t v___x_5373_; lean_object* v_j_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_es_5371_ = lean_ctor_get(v_x_5366_, 0);
v___x_5372_ = ((size_t)31ULL);
v___x_5373_ = lean_usize_land(v_x_5367_, v___x_5372_);
v_j_5374_ = lean_usize_to_nat(v___x_5373_);
v___x_5375_ = lean_array_get_size(v_es_5371_);
v___x_5376_ = lean_nat_dec_lt(v_j_5374_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_dec(v_j_5374_);
lean_dec(v_x_5370_);
lean_dec(v_x_5369_);
return v_x_5366_;
}
else
{
lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5415_; 
lean_inc_ref(v_es_5371_);
v_isSharedCheck_5415_ = !lean_is_exclusive(v_x_5366_);
if (v_isSharedCheck_5415_ == 0)
{
lean_object* v_unused_5416_; 
v_unused_5416_ = lean_ctor_get(v_x_5366_, 0);
lean_dec(v_unused_5416_);
v___x_5378_ = v_x_5366_;
v_isShared_5379_ = v_isSharedCheck_5415_;
goto v_resetjp_5377_;
}
else
{
lean_dec(v_x_5366_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5415_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v_v_5380_; lean_object* v___x_5381_; lean_object* v_xs_x27_5382_; lean_object* v___y_5384_; 
v_v_5380_ = lean_array_fget(v_es_5371_, v_j_5374_);
v___x_5381_ = lean_box(0);
v_xs_x27_5382_ = lean_array_fset(v_es_5371_, v_j_5374_, v___x_5381_);
switch(lean_obj_tag(v_v_5380_))
{
case 0:
{
lean_object* v_key_5389_; lean_object* v_val_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5400_; 
v_key_5389_ = lean_ctor_get(v_v_5380_, 0);
v_val_5390_ = lean_ctor_get(v_v_5380_, 1);
v_isSharedCheck_5400_ = !lean_is_exclusive(v_v_5380_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5392_ = v_v_5380_;
v_isShared_5393_ = v_isSharedCheck_5400_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_val_5390_);
lean_inc(v_key_5389_);
lean_dec(v_v_5380_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5400_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
uint8_t v___x_5394_; 
v___x_5394_ = l_Lean_instBEqMVarId_beq(v_x_5369_, v_key_5389_);
if (v___x_5394_ == 0)
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
lean_del_object(v___x_5392_);
v___x_5395_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_5389_, v_val_5390_, v_x_5369_, v_x_5370_);
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5395_);
v___y_5384_ = v___x_5396_;
goto v___jp_5383_;
}
else
{
lean_object* v___x_5398_; 
lean_dec(v_val_5390_);
lean_dec(v_key_5389_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 1, v_x_5370_);
lean_ctor_set(v___x_5392_, 0, v_x_5369_);
v___x_5398_ = v___x_5392_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_x_5369_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_x_5370_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
v___y_5384_ = v___x_5398_;
goto v___jp_5383_;
}
}
}
}
case 1:
{
lean_object* v_node_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5413_; 
v_node_5401_ = lean_ctor_get(v_v_5380_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v_v_5380_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5403_ = v_v_5380_;
v_isShared_5404_ = v_isSharedCheck_5413_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_node_5401_);
lean_dec(v_v_5380_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5413_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
size_t v___x_5405_; size_t v___x_5406_; size_t v___x_5407_; size_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5411_; 
v___x_5405_ = ((size_t)5ULL);
v___x_5406_ = lean_usize_shift_right(v_x_5367_, v___x_5405_);
v___x_5407_ = ((size_t)1ULL);
v___x_5408_ = lean_usize_add(v_x_5368_, v___x_5407_);
v___x_5409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_node_5401_, v___x_5406_, v___x_5408_, v_x_5369_, v_x_5370_);
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 0, v___x_5409_);
v___x_5411_ = v___x_5403_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
v___y_5384_ = v___x_5411_;
goto v___jp_5383_;
}
}
}
default: 
{
lean_object* v___x_5414_; 
v___x_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5414_, 0, v_x_5369_);
lean_ctor_set(v___x_5414_, 1, v_x_5370_);
v___y_5384_ = v___x_5414_;
goto v___jp_5383_;
}
}
v___jp_5383_:
{
lean_object* v___x_5385_; lean_object* v___x_5387_; 
v___x_5385_ = lean_array_fset(v_xs_x27_5382_, v_j_5374_, v___y_5384_);
lean_dec(v_j_5374_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 0, v___x_5385_);
v___x_5387_ = v___x_5378_;
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
}
}
}
else
{
lean_object* v_ks_5417_; lean_object* v_vs_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5436_; 
v_ks_5417_ = lean_ctor_get(v_x_5366_, 0);
v_vs_5418_ = lean_ctor_get(v_x_5366_, 1);
v_isSharedCheck_5436_ = !lean_is_exclusive(v_x_5366_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5420_ = v_x_5366_;
v_isShared_5421_ = v_isSharedCheck_5436_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_vs_5418_);
lean_inc(v_ks_5417_);
lean_dec(v_x_5366_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5436_;
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
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_ks_5417_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_vs_5418_);
v___x_5423_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v_newNode_5424_; size_t v___x_5425_; uint8_t v___x_5426_; 
v_newNode_5424_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(v___x_5423_, v_x_5369_, v_x_5370_);
v___x_5425_ = ((size_t)7ULL);
v___x_5426_ = lean_usize_dec_le(v___x_5425_, v_x_5368_);
if (v___x_5426_ == 0)
{
lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; 
v___x_5427_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5424_);
v___x_5428_ = lean_unsigned_to_nat(4u);
v___x_5429_ = lean_nat_dec_lt(v___x_5427_, v___x_5428_);
lean_dec(v___x_5427_);
if (v___x_5429_ == 0)
{
lean_object* v_ks_5430_; lean_object* v_vs_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v_ks_5430_ = lean_ctor_get(v_newNode_5424_, 0);
lean_inc_ref(v_ks_5430_);
v_vs_5431_ = lean_ctor_get(v_newNode_5424_, 1);
lean_inc_ref(v_vs_5431_);
lean_dec_ref(v_newNode_5424_);
v___x_5432_ = lean_unsigned_to_nat(0u);
v___x_5433_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___closed__0);
v___x_5434_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_x_5368_, v_ks_5430_, v_vs_5431_, v___x_5432_, v___x_5433_);
lean_dec_ref(v_vs_5431_);
lean_dec_ref(v_ks_5430_);
return v___x_5434_;
}
else
{
return v_newNode_5424_;
}
}
else
{
return v_newNode_5424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(size_t v_depth_5437_, lean_object* v_keys_5438_, lean_object* v_vals_5439_, lean_object* v_i_5440_, lean_object* v_entries_5441_){
_start:
{
lean_object* v___x_5442_; uint8_t v___x_5443_; 
v___x_5442_ = lean_array_get_size(v_keys_5438_);
v___x_5443_ = lean_nat_dec_lt(v_i_5440_, v___x_5442_);
if (v___x_5443_ == 0)
{
lean_dec(v_i_5440_);
return v_entries_5441_;
}
else
{
lean_object* v_k_5444_; lean_object* v_v_5445_; uint64_t v___x_5446_; size_t v_h_5447_; size_t v___x_5448_; lean_object* v___x_5449_; size_t v___x_5450_; size_t v___x_5451_; size_t v___x_5452_; size_t v_h_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v_k_5444_ = lean_array_fget_borrowed(v_keys_5438_, v_i_5440_);
v_v_5445_ = lean_array_fget_borrowed(v_vals_5439_, v_i_5440_);
v___x_5446_ = l_Lean_instHashableMVarId_hash(v_k_5444_);
v_h_5447_ = lean_uint64_to_usize(v___x_5446_);
v___x_5448_ = ((size_t)5ULL);
v___x_5449_ = lean_unsigned_to_nat(1u);
v___x_5450_ = ((size_t)1ULL);
v___x_5451_ = lean_usize_sub(v_depth_5437_, v___x_5450_);
v___x_5452_ = lean_usize_mul(v___x_5448_, v___x_5451_);
v_h_5453_ = lean_usize_shift_right(v_h_5447_, v___x_5452_);
v___x_5454_ = lean_nat_add(v_i_5440_, v___x_5449_);
lean_dec(v_i_5440_);
lean_inc(v_v_5445_);
lean_inc(v_k_5444_);
v___x_5455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_entries_5441_, v_h_5453_, v_depth_5437_, v_k_5444_, v_v_5445_);
v_i_5440_ = v___x_5454_;
v_entries_5441_ = v___x_5455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_depth_5457_, lean_object* v_keys_5458_, lean_object* v_vals_5459_, lean_object* v_i_5460_, lean_object* v_entries_5461_){
_start:
{
size_t v_depth_boxed_5462_; lean_object* v_res_5463_; 
v_depth_boxed_5462_ = lean_unbox_usize(v_depth_5457_);
lean_dec(v_depth_5457_);
v_res_5463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_depth_boxed_5462_, v_keys_5458_, v_vals_5459_, v_i_5460_, v_entries_5461_);
lean_dec_ref(v_vals_5459_);
lean_dec_ref(v_keys_5458_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg___boxed(lean_object* v_x_5464_, lean_object* v_x_5465_, lean_object* v_x_5466_, lean_object* v_x_5467_, lean_object* v_x_5468_){
_start:
{
size_t v_x_67443__boxed_5469_; size_t v_x_67444__boxed_5470_; lean_object* v_res_5471_; 
v_x_67443__boxed_5469_ = lean_unbox_usize(v_x_5465_);
lean_dec(v_x_5465_);
v_x_67444__boxed_5470_ = lean_unbox_usize(v_x_5466_);
lean_dec(v_x_5466_);
v_res_5471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_5464_, v_x_67443__boxed_5469_, v_x_67444__boxed_5470_, v_x_5467_, v_x_5468_);
return v_res_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(lean_object* v_x_5472_, lean_object* v_x_5473_, lean_object* v_x_5474_){
_start:
{
uint64_t v___x_5475_; size_t v___x_5476_; size_t v___x_5477_; lean_object* v___x_5478_; 
v___x_5475_ = l_Lean_instHashableMVarId_hash(v_x_5473_);
v___x_5476_ = lean_uint64_to_usize(v___x_5475_);
v___x_5477_ = ((size_t)1ULL);
v___x_5478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_5472_, v___x_5476_, v___x_5477_, v_x_5473_, v_x_5474_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(lean_object* v_mvarId_5479_, lean_object* v_val_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v___x_5483_; lean_object* v_mctx_5484_; lean_object* v_cache_5485_; lean_object* v_zetaDeltaFVarIds_5486_; lean_object* v_postponed_5487_; lean_object* v_diag_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5518_; 
v___x_5483_ = lean_st_ref_take(v___y_5481_);
v_mctx_5484_ = lean_ctor_get(v___x_5483_, 0);
v_cache_5485_ = lean_ctor_get(v___x_5483_, 1);
v_zetaDeltaFVarIds_5486_ = lean_ctor_get(v___x_5483_, 2);
v_postponed_5487_ = lean_ctor_get(v___x_5483_, 3);
v_diag_5488_ = lean_ctor_get(v___x_5483_, 4);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5490_ = v___x_5483_;
v_isShared_5491_ = v_isSharedCheck_5518_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_diag_5488_);
lean_inc(v_postponed_5487_);
lean_inc(v_zetaDeltaFVarIds_5486_);
lean_inc(v_cache_5485_);
lean_inc(v_mctx_5484_);
lean_dec(v___x_5483_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5518_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v_depth_5492_; lean_object* v_levelAssignDepth_5493_; lean_object* v_lmvarCounter_5494_; lean_object* v_mvarCounter_5495_; lean_object* v_lDecls_5496_; lean_object* v_decls_5497_; lean_object* v_userNames_5498_; lean_object* v_lAssignment_5499_; lean_object* v_eAssignment_5500_; lean_object* v_dAssignment_5501_; lean_object* v_instanceTypedMVars_5502_; lean_object* v_synthNormMemo_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5517_; 
v_depth_5492_ = lean_ctor_get(v_mctx_5484_, 0);
v_levelAssignDepth_5493_ = lean_ctor_get(v_mctx_5484_, 1);
v_lmvarCounter_5494_ = lean_ctor_get(v_mctx_5484_, 2);
v_mvarCounter_5495_ = lean_ctor_get(v_mctx_5484_, 3);
v_lDecls_5496_ = lean_ctor_get(v_mctx_5484_, 4);
v_decls_5497_ = lean_ctor_get(v_mctx_5484_, 5);
v_userNames_5498_ = lean_ctor_get(v_mctx_5484_, 6);
v_lAssignment_5499_ = lean_ctor_get(v_mctx_5484_, 7);
v_eAssignment_5500_ = lean_ctor_get(v_mctx_5484_, 8);
v_dAssignment_5501_ = lean_ctor_get(v_mctx_5484_, 9);
v_instanceTypedMVars_5502_ = lean_ctor_get(v_mctx_5484_, 10);
v_synthNormMemo_5503_ = lean_ctor_get(v_mctx_5484_, 11);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_mctx_5484_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5505_ = v_mctx_5484_;
v_isShared_5506_ = v_isSharedCheck_5517_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_synthNormMemo_5503_);
lean_inc(v_instanceTypedMVars_5502_);
lean_inc(v_dAssignment_5501_);
lean_inc(v_eAssignment_5500_);
lean_inc(v_lAssignment_5499_);
lean_inc(v_userNames_5498_);
lean_inc(v_decls_5497_);
lean_inc(v_lDecls_5496_);
lean_inc(v_mvarCounter_5495_);
lean_inc(v_lmvarCounter_5494_);
lean_inc(v_levelAssignDepth_5493_);
lean_inc(v_depth_5492_);
lean_dec(v_mctx_5484_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5517_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5510_; 
v___x_5507_ = lean_box(0);
v___x_5508_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(v_eAssignment_5500_, v_mvarId_5479_, v_val_5480_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 8, v___x_5508_);
v___x_5510_ = v___x_5505_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_depth_5492_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v_levelAssignDepth_5493_);
lean_ctor_set(v_reuseFailAlloc_5516_, 2, v_lmvarCounter_5494_);
lean_ctor_set(v_reuseFailAlloc_5516_, 3, v_mvarCounter_5495_);
lean_ctor_set(v_reuseFailAlloc_5516_, 4, v_lDecls_5496_);
lean_ctor_set(v_reuseFailAlloc_5516_, 5, v_decls_5497_);
lean_ctor_set(v_reuseFailAlloc_5516_, 6, v_userNames_5498_);
lean_ctor_set(v_reuseFailAlloc_5516_, 7, v_lAssignment_5499_);
lean_ctor_set(v_reuseFailAlloc_5516_, 8, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5516_, 9, v_dAssignment_5501_);
lean_ctor_set(v_reuseFailAlloc_5516_, 10, v_instanceTypedMVars_5502_);
lean_ctor_set(v_reuseFailAlloc_5516_, 11, v_synthNormMemo_5503_);
v___x_5510_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5512_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 0, v___x_5510_);
v___x_5512_ = v___x_5490_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v_cache_5485_);
lean_ctor_set(v_reuseFailAlloc_5515_, 2, v_zetaDeltaFVarIds_5486_);
lean_ctor_set(v_reuseFailAlloc_5515_, 3, v_postponed_5487_);
lean_ctor_set(v_reuseFailAlloc_5515_, 4, v_diag_5488_);
v___x_5512_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5513_ = lean_st_ref_put(v___y_5481_, v___x_5512_);
v___x_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5514_, 0, v___x_5507_);
return v___x_5514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg___boxed(lean_object* v_mvarId_5519_, lean_object* v_val_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_5519_, v_val_5520_, v___y_5521_);
lean_dec(v___y_5521_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(lean_object* v___x_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_){
_start:
{
if (lean_obj_tag(v_a_5525_) == 0)
{
lean_object* v___x_5527_; 
v___x_5527_ = l_List_reverse___redArg(v_a_5526_);
return v___x_5527_;
}
else
{
lean_object* v_head_5528_; lean_object* v_toGoalState_5529_; lean_object* v_tail_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5577_; 
v_head_5528_ = lean_ctor_get(v_a_5525_, 0);
lean_inc(v_head_5528_);
v_toGoalState_5529_ = lean_ctor_get(v_head_5528_, 0);
lean_inc_ref(v_toGoalState_5529_);
v_tail_5530_ = lean_ctor_get(v_a_5525_, 1);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_a_5525_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v_a_5525_, 0);
lean_dec(v_unused_5578_);
v___x_5532_ = v_a_5525_;
v_isShared_5533_ = v_isSharedCheck_5577_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_tail_5530_);
lean_dec(v_a_5525_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5577_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_mvarId_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5575_; 
v_mvarId_5534_ = lean_ctor_get(v_head_5528_, 1);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_head_5528_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_head_5528_, 0);
lean_dec(v_unused_5576_);
v___x_5536_ = v_head_5528_;
v_isShared_5537_ = v_isSharedCheck_5575_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_mvarId_5534_);
lean_dec(v_head_5528_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5575_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v_nextDeclIdx_5538_; lean_object* v_enodeMap_5539_; lean_object* v_exprs_5540_; lean_object* v_parents_5541_; lean_object* v_congrTable_5542_; lean_object* v_appMap_5543_; lean_object* v_indicesFound_5544_; lean_object* v_toProcess_5545_; lean_object* v_internalizing_5546_; uint8_t v_inconsistent_5547_; lean_object* v_nextIdx_5548_; lean_object* v_newRawFacts_5549_; lean_object* v_facts_5550_; lean_object* v_extThms_5551_; lean_object* v_ematch_5552_; lean_object* v_inj_5553_; lean_object* v_split_5554_; lean_object* v_clean_5555_; lean_object* v_sstates_5556_; lean_object* v_goalStack_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5574_; 
v_nextDeclIdx_5538_ = lean_ctor_get(v_toGoalState_5529_, 0);
v_enodeMap_5539_ = lean_ctor_get(v_toGoalState_5529_, 1);
v_exprs_5540_ = lean_ctor_get(v_toGoalState_5529_, 2);
v_parents_5541_ = lean_ctor_get(v_toGoalState_5529_, 3);
v_congrTable_5542_ = lean_ctor_get(v_toGoalState_5529_, 4);
v_appMap_5543_ = lean_ctor_get(v_toGoalState_5529_, 5);
v_indicesFound_5544_ = lean_ctor_get(v_toGoalState_5529_, 6);
v_toProcess_5545_ = lean_ctor_get(v_toGoalState_5529_, 7);
v_internalizing_5546_ = lean_ctor_get(v_toGoalState_5529_, 8);
v_inconsistent_5547_ = lean_ctor_get_uint8(v_toGoalState_5529_, sizeof(void*)*19);
v_nextIdx_5548_ = lean_ctor_get(v_toGoalState_5529_, 9);
v_newRawFacts_5549_ = lean_ctor_get(v_toGoalState_5529_, 10);
v_facts_5550_ = lean_ctor_get(v_toGoalState_5529_, 11);
v_extThms_5551_ = lean_ctor_get(v_toGoalState_5529_, 12);
v_ematch_5552_ = lean_ctor_get(v_toGoalState_5529_, 13);
v_inj_5553_ = lean_ctor_get(v_toGoalState_5529_, 14);
v_split_5554_ = lean_ctor_get(v_toGoalState_5529_, 15);
v_clean_5555_ = lean_ctor_get(v_toGoalState_5529_, 16);
v_sstates_5556_ = lean_ctor_get(v_toGoalState_5529_, 17);
v_goalStack_5557_ = lean_ctor_get(v_toGoalState_5529_, 18);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_toGoalState_5529_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5559_ = v_toGoalState_5529_;
v_isShared_5560_ = v_isSharedCheck_5574_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_goalStack_5557_);
lean_inc(v_sstates_5556_);
lean_inc(v_clean_5555_);
lean_inc(v_split_5554_);
lean_inc(v_inj_5553_);
lean_inc(v_ematch_5552_);
lean_inc(v_extThms_5551_);
lean_inc(v_facts_5550_);
lean_inc(v_newRawFacts_5549_);
lean_inc(v_nextIdx_5548_);
lean_inc(v_internalizing_5546_);
lean_inc(v_toProcess_5545_);
lean_inc(v_indicesFound_5544_);
lean_inc(v_appMap_5543_);
lean_inc(v_congrTable_5542_);
lean_inc(v_parents_5541_);
lean_inc(v_exprs_5540_);
lean_inc(v_enodeMap_5539_);
lean_inc(v_nextDeclIdx_5538_);
lean_dec(v_toGoalState_5529_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5574_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5565_; 
v___x_5561_ = lean_unsigned_to_nat(0u);
v___x_5562_ = lean_array_get_size(v___x_5524_);
v___x_5563_ = l_Array_extract___redArg(v_goalStack_5557_, v___x_5561_, v___x_5562_);
lean_dec_ref(v_goalStack_5557_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 18, v___x_5563_);
v___x_5565_ = v___x_5559_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_nextDeclIdx_5538_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v_enodeMap_5539_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_exprs_5540_);
lean_ctor_set(v_reuseFailAlloc_5573_, 3, v_parents_5541_);
lean_ctor_set(v_reuseFailAlloc_5573_, 4, v_congrTable_5542_);
lean_ctor_set(v_reuseFailAlloc_5573_, 5, v_appMap_5543_);
lean_ctor_set(v_reuseFailAlloc_5573_, 6, v_indicesFound_5544_);
lean_ctor_set(v_reuseFailAlloc_5573_, 7, v_toProcess_5545_);
lean_ctor_set(v_reuseFailAlloc_5573_, 8, v_internalizing_5546_);
lean_ctor_set(v_reuseFailAlloc_5573_, 9, v_nextIdx_5548_);
lean_ctor_set(v_reuseFailAlloc_5573_, 10, v_newRawFacts_5549_);
lean_ctor_set(v_reuseFailAlloc_5573_, 11, v_facts_5550_);
lean_ctor_set(v_reuseFailAlloc_5573_, 12, v_extThms_5551_);
lean_ctor_set(v_reuseFailAlloc_5573_, 13, v_ematch_5552_);
lean_ctor_set(v_reuseFailAlloc_5573_, 14, v_inj_5553_);
lean_ctor_set(v_reuseFailAlloc_5573_, 15, v_split_5554_);
lean_ctor_set(v_reuseFailAlloc_5573_, 16, v_clean_5555_);
lean_ctor_set(v_reuseFailAlloc_5573_, 17, v_sstates_5556_);
lean_ctor_set(v_reuseFailAlloc_5573_, 18, v___x_5563_);
lean_ctor_set_uint8(v_reuseFailAlloc_5573_, sizeof(void*)*19, v_inconsistent_5547_);
v___x_5565_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
lean_object* v___x_5567_; 
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 0, v___x_5565_);
v___x_5567_ = v___x_5536_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_mvarId_5534_);
v___x_5567_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5569_; 
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 1, v_a_5526_);
lean_ctor_set(v___x_5532_, 0, v___x_5567_);
v___x_5569_ = v___x_5532_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5567_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_a_5526_);
v___x_5569_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
v_a_5525_ = v_tail_5530_;
v_a_5526_ = v___x_5569_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2___boxed(lean_object* v___x_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_5579_, v_a_5580_, v_a_5581_);
lean_dec_ref(v___x_5579_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(lean_object* v___x_5583_, lean_object* v_gs_5584_){
_start:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5585_ = lean_box(0);
v___x_5586_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__2(v___x_5583_, v_gs_5584_, v___x_5585_);
return v___x_5586_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0___boxed(lean_object* v___x_5587_, lean_object* v_gs_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5587_, v_gs_5588_);
lean_dec_ref(v___x_5587_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(lean_object* v_kp_5590_, lean_object* v_snd_5591_, lean_object* v___x_5592_, uint8_t v_stopAtFirstFailure_5593_, lean_object* v___x_5594_, lean_object* v_as_x27_5595_, lean_object* v_b_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
if (lean_obj_tag(v_as_x27_5595_) == 0)
{
lean_object* v___x_5607_; 
lean_dec(v___x_5592_);
lean_dec_ref(v_kp_5590_);
v___x_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5607_, 0, v_b_5596_);
return v___x_5607_;
}
else
{
lean_object* v_snd_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5743_; 
v_snd_5608_ = lean_ctor_get(v_b_5596_, 1);
v_isSharedCheck_5743_ = !lean_is_exclusive(v_b_5596_);
if (v_isSharedCheck_5743_ == 0)
{
lean_object* v_unused_5744_; 
v_unused_5744_ = lean_ctor_get(v_b_5596_, 0);
lean_dec(v_unused_5744_);
v___x_5610_ = v_b_5596_;
v_isShared_5611_ = v_isSharedCheck_5743_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_snd_5608_);
lean_dec(v_b_5596_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5743_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v_head_5612_; lean_object* v_tail_5613_; lean_object* v_fst_5614_; lean_object* v_snd_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5742_; 
v_head_5612_ = lean_ctor_get(v_as_x27_5595_, 0);
v_tail_5613_ = lean_ctor_get(v_as_x27_5595_, 1);
v_fst_5614_ = lean_ctor_get(v_snd_5608_, 0);
v_snd_5615_ = lean_ctor_get(v_snd_5608_, 1);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_snd_5608_);
if (v_isSharedCheck_5742_ == 0)
{
v___x_5617_ = v_snd_5608_;
v_isShared_5618_ = v_isSharedCheck_5742_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_snd_5615_);
lean_inc(v_fst_5614_);
lean_dec(v_snd_5608_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5742_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; 
v___x_5619_ = lean_box(0);
lean_inc_ref(v_kp_5590_);
lean_inc(v___y_5605_);
lean_inc_ref(v___y_5604_);
lean_inc(v___y_5603_);
lean_inc_ref(v___y_5602_);
lean_inc(v___y_5601_);
lean_inc_ref(v___y_5600_);
lean_inc(v___y_5599_);
lean_inc_ref(v___y_5598_);
lean_inc(v___y_5597_);
lean_inc(v_head_5612_);
v___x_5620_ = lean_apply_11(v_kp_5590_, v_head_5612_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, lean_box(0));
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5733_; 
v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5733_ == 0)
{
v___x_5623_ = v___x_5620_;
v_isShared_5624_ = v_isSharedCheck_5733_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5620_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5733_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
if (lean_obj_tag(v_a_5621_) == 0)
{
lean_object* v_seq_5625_; lean_object* v_mvarId_5626_; lean_object* v___x_5627_; 
lean_del_object(v___x_5623_);
v_seq_5625_ = lean_ctor_get(v_a_5621_, 0);
v_mvarId_5626_ = lean_ctor_get(v_head_5612_, 1);
lean_inc(v_mvarId_5626_);
v___x_5627_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_getFalseProof_x3f(v_mvarId_5626_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5628_);
lean_dec_ref_known(v___x_5627_, 1);
if (lean_obj_tag(v_a_5628_) == 1)
{
lean_object* v_val_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5679_; 
lean_dec_ref(v_kp_5590_);
v_val_5629_ = lean_ctor_get(v_a_5628_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v_a_5628_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5631_ = v_a_5628_;
v_isShared_5632_ = v_isSharedCheck_5679_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_val_5629_);
lean_dec(v_a_5628_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5679_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5633_; 
v___x_5633_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5591_, v___y_5599_);
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_object* v_a_5634_; lean_object* v___x_5635_; 
v_a_5634_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_a_5634_);
lean_dec_ref_known(v___x_5633_, 1);
v___x_5635_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5634_, v_val_5629_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; lean_object* v___x_5637_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_a_5636_);
lean_dec_ref_known(v___x_5635_, 1);
v___x_5637_ = l_Lean_MVarId_assignFalseProof(v___x_5592_, v_a_5636_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
if (lean_obj_tag(v___x_5637_) == 0)
{
lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5653_; 
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; 
v_unused_5654_ = lean_ctor_get(v___x_5637_, 0);
lean_dec(v_unused_5654_);
v___x_5639_ = v___x_5637_;
v_isShared_5640_ = v_isSharedCheck_5653_;
goto v_resetjp_5638_;
}
else
{
lean_dec(v___x_5637_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5653_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 0, v_a_5621_);
v___x_5642_ = v___x_5631_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5621_);
v___x_5642_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5644_; 
if (v_isShared_5618_ == 0)
{
v___x_5644_ = v___x_5617_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v_snd_5615_);
v___x_5644_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5646_; 
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 1, v___x_5644_);
lean_ctor_set(v___x_5610_, 0, v___x_5642_);
v___x_5646_ = v___x_5610_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5642_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v___x_5644_);
v___x_5646_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 0, v___x_5646_);
v___x_5648_ = v___x_5639_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
lean_del_object(v___x_5631_);
lean_dec_ref_known(v_a_5621_, 1);
lean_del_object(v___x_5617_);
lean_dec(v_snd_5615_);
lean_dec(v_fst_5614_);
lean_del_object(v___x_5610_);
v_a_5655_ = lean_ctor_get(v___x_5637_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5657_ = v___x_5637_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_dec(v___x_5637_);
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
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
lean_del_object(v___x_5631_);
lean_dec_ref_known(v_a_5621_, 1);
lean_del_object(v___x_5617_);
lean_dec(v_snd_5615_);
lean_dec(v_fst_5614_);
lean_del_object(v___x_5610_);
lean_dec(v___x_5592_);
v_a_5663_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___x_5635_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___x_5635_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
else
{
lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5678_; 
lean_del_object(v___x_5631_);
lean_dec(v_val_5629_);
lean_dec_ref_known(v_a_5621_, 1);
lean_del_object(v___x_5617_);
lean_dec(v_snd_5615_);
lean_dec(v_fst_5614_);
lean_del_object(v___x_5610_);
lean_dec(v___x_5592_);
v_a_5671_ = lean_ctor_get(v___x_5633_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v___x_5633_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5673_ = v___x_5633_;
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5633_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5676_; 
if (v_isShared_5674_ == 0)
{
v___x_5676_ = v___x_5673_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
}
}
}
else
{
uint8_t v___x_5680_; 
lean_inc(v_seq_5625_);
lean_dec(v_a_5628_);
lean_dec_ref_known(v_a_5621_, 1);
v___x_5680_ = l_List_isEmpty___redArg(v_seq_5625_);
if (v___x_5680_ == 0)
{
lean_object* v___x_5681_; lean_object* v___x_5683_; 
v___x_5681_ = lean_array_push(v_fst_5614_, v_seq_5625_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 0, v___x_5681_);
v___x_5683_ = v___x_5617_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5681_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_snd_5615_);
v___x_5683_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
lean_object* v___x_5685_; 
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 1, v___x_5683_);
lean_ctor_set(v___x_5610_, 0, v___x_5619_);
v___x_5685_ = v___x_5610_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
v_as_x27_5595_ = v_tail_5613_;
v_b_5596_ = v___x_5685_;
goto _start;
}
}
}
else
{
lean_object* v___x_5690_; 
lean_dec(v_seq_5625_);
if (v_isShared_5618_ == 0)
{
v___x_5690_ = v___x_5617_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v_snd_5615_);
v___x_5690_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5692_; 
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 1, v___x_5690_);
lean_ctor_set(v___x_5610_, 0, v___x_5619_);
v___x_5692_ = v___x_5610_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5694_, 1, v___x_5690_);
v___x_5692_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
v_as_x27_5595_ = v_tail_5613_;
v_b_5596_ = v___x_5692_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec_ref_known(v_a_5621_, 1);
lean_del_object(v___x_5617_);
lean_dec(v_snd_5615_);
lean_dec(v_fst_5614_);
lean_del_object(v___x_5610_);
lean_dec(v___x_5592_);
lean_dec_ref(v_kp_5590_);
v_a_5696_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___x_5627_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5627_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
else
{
if (v_stopAtFirstFailure_5593_ == 0)
{
lean_object* v_gs_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5708_; 
lean_del_object(v___x_5623_);
v_gs_5704_ = lean_ctor_get(v_a_5621_, 0);
lean_inc(v_gs_5704_);
lean_dec_ref_known(v_a_5621_, 1);
v___x_5705_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5594_, v_gs_5704_);
v___x_5706_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_5615_, v___x_5705_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 1, v___x_5706_);
v___x_5708_ = v___x_5617_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5706_);
v___x_5708_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
lean_object* v___x_5710_; 
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 1, v___x_5708_);
lean_ctor_set(v___x_5610_, 0, v___x_5619_);
v___x_5710_ = v___x_5610_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
v_as_x27_5595_ = v_tail_5613_;
v_b_5596_ = v___x_5710_;
goto _start;
}
}
}
else
{
lean_object* v_gs_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5732_; 
lean_dec(v___x_5592_);
lean_dec_ref(v_kp_5590_);
v_gs_5714_ = lean_ctor_get(v_a_5621_, 0);
v_isSharedCheck_5732_ = !lean_is_exclusive(v_a_5621_);
if (v_isSharedCheck_5732_ == 0)
{
v___x_5716_ = v_a_5621_;
v_isShared_5717_ = v_isSharedCheck_5732_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_gs_5714_);
lean_dec(v_a_5621_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5732_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v___x_5718_; lean_object* v___x_5720_; 
v___x_5718_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___lam__0(v___x_5594_, v_gs_5714_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 0, v___x_5718_);
v___x_5720_ = v___x_5716_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v___x_5718_);
v___x_5720_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
lean_object* v___x_5721_; lean_object* v___x_5723_; 
v___x_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
if (v_isShared_5618_ == 0)
{
v___x_5723_ = v___x_5617_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5730_, 1, v_snd_5615_);
v___x_5723_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
lean_object* v___x_5725_; 
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 1, v___x_5723_);
lean_ctor_set(v___x_5610_, 0, v___x_5721_);
v___x_5725_ = v___x_5610_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v___x_5721_);
lean_ctor_set(v_reuseFailAlloc_5729_, 1, v___x_5723_);
v___x_5725_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
lean_object* v___x_5727_; 
if (v_isShared_5624_ == 0)
{
lean_ctor_set(v___x_5623_, 0, v___x_5725_);
v___x_5727_ = v___x_5623_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5725_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
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
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
lean_del_object(v___x_5617_);
lean_dec(v_snd_5615_);
lean_dec(v_fst_5614_);
lean_del_object(v___x_5610_);
lean_dec(v___x_5592_);
lean_dec_ref(v_kp_5590_);
v_a_5734_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5736_ = v___x_5620_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5620_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_a_5734_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_kp_5745_ = _args[0];
lean_object* v_snd_5746_ = _args[1];
lean_object* v___x_5747_ = _args[2];
lean_object* v_stopAtFirstFailure_5748_ = _args[3];
lean_object* v___x_5749_ = _args[4];
lean_object* v_as_x27_5750_ = _args[5];
lean_object* v_b_5751_ = _args[6];
lean_object* v___y_5752_ = _args[7];
lean_object* v___y_5753_ = _args[8];
lean_object* v___y_5754_ = _args[9];
lean_object* v___y_5755_ = _args[10];
lean_object* v___y_5756_ = _args[11];
lean_object* v___y_5757_ = _args[12];
lean_object* v___y_5758_ = _args[13];
lean_object* v___y_5759_ = _args[14];
lean_object* v___y_5760_ = _args[15];
lean_object* v___y_5761_ = _args[16];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_5762_; lean_object* v_res_5763_; 
v_stopAtFirstFailure_boxed_5762_ = lean_unbox(v_stopAtFirstFailure_5748_);
v_res_5763_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_5745_, v_snd_5746_, v___x_5747_, v_stopAtFirstFailure_boxed_5762_, v___x_5749_, v_as_x27_5750_, v_b_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v___y_5754_);
lean_dec_ref(v___y_5753_);
lean_dec(v___y_5752_);
lean_dec(v_as_x27_5750_);
lean_dec_ref(v___x_5749_);
lean_dec_ref(v_snd_5746_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(lean_object* v___x_5764_, lean_object* v_c_5765_, lean_object* v___x_5766_, lean_object* v___x_5767_, lean_object* v___x_5768_, uint8_t v_isRec_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_){
_start:
{
if (lean_obj_tag(v_a_5770_) == 0)
{
lean_object* v___x_5772_; 
lean_dec_ref(v___x_5768_);
lean_dec(v___x_5767_);
lean_dec_ref(v___x_5766_);
lean_dec_ref(v___x_5764_);
v___x_5772_ = lean_array_to_list(v_a_5771_);
return v___x_5772_;
}
else
{
lean_object* v_split_5773_; lean_object* v_head_5774_; lean_object* v_tail_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5829_; 
v_split_5773_ = lean_ctor_get(v___x_5764_, 15);
lean_inc_ref(v_split_5773_);
v_head_5774_ = lean_ctor_get(v_a_5770_, 0);
v_tail_5775_ = lean_ctor_get(v_a_5770_, 1);
v_isSharedCheck_5829_ = !lean_is_exclusive(v_a_5770_);
if (v_isSharedCheck_5829_ == 0)
{
v___x_5777_ = v_a_5770_;
v_isShared_5778_ = v_isSharedCheck_5829_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_tail_5775_);
lean_inc(v_head_5774_);
lean_dec(v_a_5770_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5829_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v_nextDeclIdx_5779_; lean_object* v_enodeMap_5780_; lean_object* v_exprs_5781_; lean_object* v_parents_5782_; lean_object* v_congrTable_5783_; lean_object* v_appMap_5784_; lean_object* v_indicesFound_5785_; lean_object* v_toProcess_5786_; lean_object* v_internalizing_5787_; uint8_t v_inconsistent_5788_; lean_object* v_nextIdx_5789_; lean_object* v_newRawFacts_5790_; lean_object* v_facts_5791_; lean_object* v_extThms_5792_; lean_object* v_ematch_5793_; lean_object* v_inj_5794_; lean_object* v_clean_5795_; lean_object* v_sstates_5796_; lean_object* v_num_5797_; lean_object* v_candidates_5798_; lean_object* v_added_5799_; lean_object* v_resolved_5800_; lean_object* v_trace_5801_; lean_object* v_lookaheads_5802_; lean_object* v_argPosMap_5803_; lean_object* v_argsAt_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5828_; 
v_nextDeclIdx_5779_ = lean_ctor_get(v___x_5764_, 0);
v_enodeMap_5780_ = lean_ctor_get(v___x_5764_, 1);
v_exprs_5781_ = lean_ctor_get(v___x_5764_, 2);
v_parents_5782_ = lean_ctor_get(v___x_5764_, 3);
v_congrTable_5783_ = lean_ctor_get(v___x_5764_, 4);
v_appMap_5784_ = lean_ctor_get(v___x_5764_, 5);
v_indicesFound_5785_ = lean_ctor_get(v___x_5764_, 6);
v_toProcess_5786_ = lean_ctor_get(v___x_5764_, 7);
v_internalizing_5787_ = lean_ctor_get(v___x_5764_, 8);
v_inconsistent_5788_ = lean_ctor_get_uint8(v___x_5764_, sizeof(void*)*19);
v_nextIdx_5789_ = lean_ctor_get(v___x_5764_, 9);
v_newRawFacts_5790_ = lean_ctor_get(v___x_5764_, 10);
v_facts_5791_ = lean_ctor_get(v___x_5764_, 11);
v_extThms_5792_ = lean_ctor_get(v___x_5764_, 12);
v_ematch_5793_ = lean_ctor_get(v___x_5764_, 13);
v_inj_5794_ = lean_ctor_get(v___x_5764_, 14);
v_clean_5795_ = lean_ctor_get(v___x_5764_, 16);
v_sstates_5796_ = lean_ctor_get(v___x_5764_, 17);
v_num_5797_ = lean_ctor_get(v_split_5773_, 0);
v_candidates_5798_ = lean_ctor_get(v_split_5773_, 1);
v_added_5799_ = lean_ctor_get(v_split_5773_, 2);
v_resolved_5800_ = lean_ctor_get(v_split_5773_, 3);
v_trace_5801_ = lean_ctor_get(v_split_5773_, 4);
v_lookaheads_5802_ = lean_ctor_get(v_split_5773_, 5);
v_argPosMap_5803_ = lean_ctor_get(v_split_5773_, 6);
v_argsAt_5804_ = lean_ctor_get(v_split_5773_, 7);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_split_5773_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5806_ = v_split_5773_;
v_isShared_5807_ = v_isSharedCheck_5828_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_argsAt_5804_);
lean_inc(v_argPosMap_5803_);
lean_inc(v_lookaheads_5802_);
lean_inc(v_trace_5801_);
lean_inc(v_resolved_5800_);
lean_inc(v_added_5799_);
lean_inc(v_candidates_5798_);
lean_inc(v_num_5797_);
lean_dec(v_split_5773_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5828_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v___x_5808_; lean_object* v___y_5810_; lean_object* v___x_5826_; uint8_t v___x_5827_; 
v___x_5808_ = lean_array_get_size(v_a_5771_);
v___x_5826_ = lean_unsigned_to_nat(0u);
v___x_5827_ = lean_nat_dec_lt(v___x_5826_, v___x_5808_);
if (v___x_5827_ == 0)
{
if (v_isRec_5769_ == 0)
{
v___y_5810_ = v_num_5797_;
goto v___jp_5809_;
}
else
{
goto v___jp_5823_;
}
}
else
{
goto v___jp_5823_;
}
v___jp_5809_:
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5814_; 
v___x_5811_ = l_Lean_Meta_Grind_SplitInfo_source(v_c_5765_);
lean_inc(v___x_5767_);
lean_inc_ref(v___x_5766_);
v___x_5812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5766_);
lean_ctor_set(v___x_5812_, 1, v___x_5808_);
lean_ctor_set(v___x_5812_, 2, v___x_5767_);
lean_ctor_set(v___x_5812_, 3, v___x_5811_);
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 1, v_trace_5801_);
lean_ctor_set(v___x_5777_, 0, v___x_5812_);
v___x_5814_ = v___x_5777_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5812_);
lean_ctor_set(v_reuseFailAlloc_5822_, 1, v_trace_5801_);
v___x_5814_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5816_; 
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 4, v___x_5814_);
lean_ctor_set(v___x_5806_, 0, v___y_5810_);
v___x_5816_ = v___x_5806_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v___y_5810_);
lean_ctor_set(v_reuseFailAlloc_5821_, 1, v_candidates_5798_);
lean_ctor_set(v_reuseFailAlloc_5821_, 2, v_added_5799_);
lean_ctor_set(v_reuseFailAlloc_5821_, 3, v_resolved_5800_);
lean_ctor_set(v_reuseFailAlloc_5821_, 4, v___x_5814_);
lean_ctor_set(v_reuseFailAlloc_5821_, 5, v_lookaheads_5802_);
lean_ctor_set(v_reuseFailAlloc_5821_, 6, v_argPosMap_5803_);
lean_ctor_set(v_reuseFailAlloc_5821_, 7, v_argsAt_5804_);
v___x_5816_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
lean_inc_ref(v___x_5768_);
lean_inc_ref(v_sstates_5796_);
lean_inc_ref(v_clean_5795_);
lean_inc_ref(v_inj_5794_);
lean_inc_ref(v_ematch_5793_);
lean_inc_ref(v_extThms_5792_);
lean_inc_ref(v_facts_5791_);
lean_inc_ref(v_newRawFacts_5790_);
lean_inc(v_nextIdx_5789_);
lean_inc_ref(v_internalizing_5787_);
lean_inc_ref(v_toProcess_5786_);
lean_inc_ref(v_indicesFound_5785_);
lean_inc_ref(v_appMap_5784_);
lean_inc_ref(v_congrTable_5783_);
lean_inc_ref(v_parents_5782_);
lean_inc_ref(v_exprs_5781_);
lean_inc_ref(v_enodeMap_5780_);
lean_inc(v_nextDeclIdx_5779_);
v___x_5817_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v___x_5817_, 0, v_nextDeclIdx_5779_);
lean_ctor_set(v___x_5817_, 1, v_enodeMap_5780_);
lean_ctor_set(v___x_5817_, 2, v_exprs_5781_);
lean_ctor_set(v___x_5817_, 3, v_parents_5782_);
lean_ctor_set(v___x_5817_, 4, v_congrTable_5783_);
lean_ctor_set(v___x_5817_, 5, v_appMap_5784_);
lean_ctor_set(v___x_5817_, 6, v_indicesFound_5785_);
lean_ctor_set(v___x_5817_, 7, v_toProcess_5786_);
lean_ctor_set(v___x_5817_, 8, v_internalizing_5787_);
lean_ctor_set(v___x_5817_, 9, v_nextIdx_5789_);
lean_ctor_set(v___x_5817_, 10, v_newRawFacts_5790_);
lean_ctor_set(v___x_5817_, 11, v_facts_5791_);
lean_ctor_set(v___x_5817_, 12, v_extThms_5792_);
lean_ctor_set(v___x_5817_, 13, v_ematch_5793_);
lean_ctor_set(v___x_5817_, 14, v_inj_5794_);
lean_ctor_set(v___x_5817_, 15, v___x_5816_);
lean_ctor_set(v___x_5817_, 16, v_clean_5795_);
lean_ctor_set(v___x_5817_, 17, v_sstates_5796_);
lean_ctor_set(v___x_5817_, 18, v___x_5768_);
lean_ctor_set_uint8(v___x_5817_, sizeof(void*)*19, v_inconsistent_5788_);
v___x_5818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5817_);
lean_ctor_set(v___x_5818_, 1, v_head_5774_);
v___x_5819_ = lean_array_push(v_a_5771_, v___x_5818_);
v_a_5770_ = v_tail_5775_;
v_a_5771_ = v___x_5819_;
goto _start;
}
}
}
v___jp_5823_:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_unsigned_to_nat(1u);
v___x_5825_ = lean_nat_add(v_num_5797_, v___x_5824_);
lean_dec(v_num_5797_);
v___y_5810_ = v___x_5825_;
goto v___jp_5809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3___boxed(lean_object* v___x_5830_, lean_object* v_c_5831_, lean_object* v___x_5832_, lean_object* v___x_5833_, lean_object* v___x_5834_, lean_object* v_isRec_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_){
_start:
{
uint8_t v_isRec_boxed_5838_; lean_object* v_res_5839_; 
v_isRec_boxed_5838_ = lean_unbox(v_isRec_5835_);
v_res_5839_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v___x_5830_, v_c_5831_, v___x_5832_, v___x_5833_, v___x_5834_, v_isRec_boxed_5838_, v_a_5836_, v_a_5837_);
lean_dec_ref(v_c_5831_);
return v_res_5839_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5851_ = lean_box(0);
v___x_5852_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__4));
v___x_5853_ = l_Lean_mkConst(v___x_5852_, v___x_5851_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(lean_object* v_goal_5854_, lean_object* v_c_5855_, lean_object* v_numCases_5856_, uint8_t v_isRec_5857_, lean_object* v_candidates_x3f_5858_, lean_object* v_kp_5859_, uint8_t v_stopAtFirstFailure_5860_, uint8_t v_compress_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v___x_5872_; 
v___x_5872_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_5863_);
if (lean_obj_tag(v___x_5872_) == 0)
{
lean_object* v_a_5873_; uint8_t v_trace_5874_; lean_object* v___x_5875_; 
v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
lean_inc(v_a_5873_);
lean_dec_ref_known(v___x_5872_, 1);
v_trace_5874_ = lean_ctor_get_uint8(v_a_5873_, sizeof(void*)*17);
lean_dec(v_a_5873_);
lean_inc_ref(v_goal_5854_);
v___x_5875_ = l_Lean_Meta_Grind_Goal_mkAuxMVar(v_goal_5854_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5875_) == 0)
{
lean_object* v_a_5876_; lean_object* v_mvarId_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___f_5880_; lean_object* v___x_5881_; lean_object* v___f_5882_; lean_object* v___x_5883_; 
v_a_5876_ = lean_ctor_get(v___x_5875_, 0);
lean_inc_n(v_a_5876_, 2);
lean_dec_ref_known(v___x_5875_, 1);
v_mvarId_5877_ = lean_ctor_get(v_goal_5854_, 1);
lean_inc(v_mvarId_5877_);
v___x_5878_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_5855_);
v___x_5879_ = lean_box(v_isRec_5857_);
lean_inc_ref_n(v_c_5855_, 2);
lean_inc_ref(v___x_5878_);
v___f_5880_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__0___boxed), 17, 5);
lean_closure_set(v___f_5880_, 0, v___x_5878_);
lean_closure_set(v___f_5880_, 1, v_c_5855_);
lean_closure_set(v___f_5880_, 2, v_a_5876_);
lean_closure_set(v___f_5880_, 3, v_numCases_5856_);
lean_closure_set(v___f_5880_, 4, v___x_5879_);
v___x_5881_ = lean_box(v_trace_5874_);
v___f_5882_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__1___boxed), 15, 5);
lean_closure_set(v___f_5882_, 0, v_goal_5854_);
lean_closure_set(v___f_5882_, 1, v___x_5881_);
lean_closure_set(v___f_5882_, 2, v___f_5880_);
lean_closure_set(v___f_5882_, 3, v_c_5855_);
lean_closure_set(v___f_5882_, 4, v_candidates_x3f_5858_);
v___x_5883_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_5877_, v___f_5882_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5883_) == 0)
{
lean_object* v_a_5884_; lean_object* v_fst_5885_; lean_object* v_snd_5886_; lean_object* v_toGoalState_5887_; lean_object* v_fst_5888_; lean_object* v_snd_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_6013_; 
v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
lean_inc(v_a_5884_);
lean_dec_ref_known(v___x_5883_, 1);
v_fst_5885_ = lean_ctor_get(v_a_5884_, 0);
lean_inc(v_fst_5885_);
v_snd_5886_ = lean_ctor_get(v_a_5884_, 1);
lean_inc(v_snd_5886_);
lean_dec(v_a_5884_);
v_toGoalState_5887_ = lean_ctor_get(v_snd_5886_, 0);
v_fst_5888_ = lean_ctor_get(v_fst_5885_, 0);
v_snd_5889_ = lean_ctor_get(v_fst_5885_, 1);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_fst_5885_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_5891_ = v_fst_5885_;
v_isShared_5892_ = v_isSharedCheck_6013_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_snd_5889_);
lean_inc(v_fst_5888_);
lean_dec(v_fst_5885_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_6013_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v_mvarId_5893_; lean_object* v_goalStack_5894_; lean_object* v___x_5895_; lean_object* v___x_5897_; 
v_mvarId_5893_ = lean_ctor_get(v_snd_5886_, 1);
lean_inc_n(v_mvarId_5893_, 2);
v_goalStack_5894_ = lean_ctor_get(v_toGoalState_5887_, 18);
v___x_5895_ = l_List_lengthTR___redArg(v_fst_5888_);
lean_inc_ref(v_toGoalState_5887_);
if (v_isShared_5892_ == 0)
{
lean_ctor_set(v___x_5891_, 1, v_toGoalState_5887_);
lean_ctor_set(v___x_5891_, 0, v_mvarId_5893_);
v___x_5897_ = v___x_5891_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_mvarId_5893_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v_toGoalState_5887_);
v___x_5897_ = v_reuseFailAlloc_6012_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; 
lean_inc_ref(v_goalStack_5894_);
v___x_5898_ = lean_array_push(v_goalStack_5894_, v___x_5897_);
v___x_5899_ = lean_unsigned_to_nat(0u);
v___x_5900_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__0));
lean_inc_ref(v_toGoalState_5887_);
v___x_5901_ = l_List_mapIdx_go___at___00Lean_Meta_Grind_Action_splitCore_spec__3(v_toGoalState_5887_, v_c_5855_, v___x_5878_, v___x_5895_, v___x_5898_, v_isRec_5857_, v_fst_5888_, v___x_5900_);
lean_dec_ref(v_c_5855_);
v___x_5902_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__2));
lean_inc(v_mvarId_5893_);
v___x_5903_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_5859_, v_snd_5886_, v_mvarId_5893_, v_stopAtFirstFailure_5860_, v_goalStack_5894_, v___x_5901_, v___x_5902_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
lean_dec(v___x_5901_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_6003_; 
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5906_ = v___x_5903_;
v_isShared_5907_ = v_isSharedCheck_6003_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5903_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_6003_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v_fst_5908_; 
v_fst_5908_ = lean_ctor_get(v_a_5904_, 0);
if (lean_obj_tag(v_fst_5908_) == 0)
{
lean_object* v_snd_5909_; lean_object* v_fst_5910_; lean_object* v_snd_5911_; lean_object* v___y_5913_; lean_object* v___y_5914_; lean_object* v___x_5961_; 
v_snd_5909_ = lean_ctor_get(v_a_5904_, 1);
lean_inc(v_snd_5909_);
lean_dec(v_a_5904_);
v_fst_5910_ = lean_ctor_get(v_snd_5909_, 0);
lean_inc(v_fst_5910_);
v_snd_5911_ = lean_ctor_get(v_snd_5909_, 1);
lean_inc(v_snd_5911_);
lean_dec(v_snd_5909_);
v___x_5961_ = l_Lean_Meta_Grind_getHoistedDecls___redArg(v_snd_5886_, v___y_5864_);
lean_dec(v_snd_5886_);
if (lean_obj_tag(v___x_5961_) == 0)
{
lean_object* v_a_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v_a_5965_; lean_object* v___x_5966_; 
v_a_5962_ = lean_ctor_get(v___x_5961_, 0);
lean_inc(v_a_5962_);
lean_dec_ref_known(v___x_5961_, 1);
v___x_5963_ = l_Lean_mkMVar(v_a_5876_);
v___x_5964_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_splitCore_spec__5___redArg(v___x_5963_, v___y_5868_);
v_a_5965_ = lean_ctor_get(v___x_5964_, 0);
lean_inc(v_a_5965_);
lean_dec_ref(v___x_5964_);
v___x_5966_ = l_Lean_Meta_Grind_mkHoistedDecls(v_a_5962_, v_a_5965_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5966_) == 0)
{
lean_object* v_a_5967_; lean_object* v___x_5968_; 
v_a_5967_ = lean_ctor_get(v___x_5966_, 0);
lean_inc(v_a_5967_);
lean_dec_ref_known(v___x_5966_, 1);
lean_inc(v_mvarId_5893_);
v___x_5968_ = l_Lean_MVarId_getType(v_mvarId_5893_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; uint8_t v___x_5970_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v___x_5970_ = l_Lean_Expr_isFalse(v_a_5969_);
lean_dec(v_a_5969_);
if (v___x_5970_ == 0)
{
lean_object* v___x_5971_; 
v___x_5971_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_5893_, v_a_5967_, v___y_5868_);
lean_dec_ref(v___x_5971_);
v___y_5913_ = v___y_5869_;
v___y_5914_ = v___y_5870_;
goto v___jp_5912_;
}
else
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; 
v___x_5972_ = lean_obj_once(&l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5, &l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5_once, _init_l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__5);
v___x_5973_ = l_Lean_Meta_mkExpectedPropHint(v_a_5967_, v___x_5972_);
v___x_5974_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_5893_, v___x_5973_, v___y_5868_);
lean_dec_ref(v___x_5974_);
v___y_5913_ = v___y_5869_;
v___y_5914_ = v___y_5870_;
goto v___jp_5912_;
}
}
else
{
lean_object* v_a_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_5982_; 
lean_dec(v_a_5967_);
lean_dec(v_snd_5911_);
lean_dec(v_fst_5910_);
lean_del_object(v___x_5906_);
lean_dec(v_mvarId_5893_);
lean_dec(v_snd_5889_);
v_a_5975_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5982_ == 0)
{
v___x_5977_ = v___x_5968_;
v_isShared_5978_ = v_isSharedCheck_5982_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_a_5975_);
lean_dec(v___x_5968_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_5982_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v___x_5980_; 
if (v_isShared_5978_ == 0)
{
v___x_5980_ = v___x_5977_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_a_5975_);
v___x_5980_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
return v___x_5980_;
}
}
}
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec(v_snd_5911_);
lean_dec(v_fst_5910_);
lean_del_object(v___x_5906_);
lean_dec(v_mvarId_5893_);
lean_dec(v_snd_5889_);
v_a_5983_ = lean_ctor_get(v___x_5966_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5966_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5966_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5966_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec(v_snd_5911_);
lean_dec(v_fst_5910_);
lean_del_object(v___x_5906_);
lean_dec(v_mvarId_5893_);
lean_dec(v_snd_5889_);
lean_dec(v_a_5876_);
v_a_5991_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5961_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5961_);
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
v___jp_5912_:
{
lean_object* v___x_5915_; uint8_t v___x_5916_; 
v___x_5915_ = lean_array_get_size(v_snd_5911_);
v___x_5916_ = lean_nat_dec_eq(v___x_5915_, v___x_5899_);
if (v___x_5916_ == 0)
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5920_; 
lean_dec(v_fst_5910_);
lean_dec(v_snd_5889_);
v___x_5917_ = lean_array_to_list(v_snd_5911_);
v___x_5918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 0, v___x_5918_);
v___x_5920_ = v___x_5906_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
v___x_5920_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
return v___x_5920_;
}
}
else
{
lean_dec(v_snd_5911_);
if (lean_obj_tag(v_snd_5889_) == 1)
{
lean_object* v_val_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5956_; 
lean_del_object(v___x_5906_);
v_val_5922_ = lean_ctor_get(v_snd_5889_, 0);
v_isSharedCheck_5956_ = !lean_is_exclusive(v_snd_5889_);
if (v_isSharedCheck_5956_ == 0)
{
v___x_5924_ = v_snd_5889_;
v_isShared_5925_ = v_isSharedCheck_5956_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_val_5922_);
lean_dec(v_snd_5889_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5956_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v___x_5926_; 
v___x_5926_ = l_Lean_Meta_Grind_SplitAnchorRefInfo_toSyntax___redArg(v_val_5922_, v___y_5913_);
lean_dec(v_val_5922_);
if (lean_obj_tag(v___x_5926_) == 0)
{
lean_object* v_a_5927_; lean_object* v___x_5928_; 
v_a_5927_ = lean_ctor_get(v___x_5926_, 0);
lean_inc(v_a_5927_);
lean_dec_ref_known(v___x_5926_, 1);
v___x_5928_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_Action_mkCasesResultSeq(v_a_5927_, v_fst_5910_, v_compress_5861_, v___y_5913_, v___y_5914_);
if (lean_obj_tag(v___x_5928_) == 0)
{
lean_object* v_a_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5939_; 
v_a_5929_ = lean_ctor_get(v___x_5928_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5928_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5931_ = v___x_5928_;
v_isShared_5932_ = v_isSharedCheck_5939_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_a_5929_);
lean_dec(v___x_5928_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5939_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v___x_5934_; 
if (v_isShared_5925_ == 0)
{
lean_ctor_set_tag(v___x_5924_, 0);
lean_ctor_set(v___x_5924_, 0, v_a_5929_);
v___x_5934_ = v___x_5924_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5929_);
v___x_5934_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
lean_object* v___x_5936_; 
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 0, v___x_5934_);
v___x_5936_ = v___x_5931_;
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
}
}
else
{
lean_object* v_a_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5947_; 
lean_del_object(v___x_5924_);
v_a_5940_ = lean_ctor_get(v___x_5928_, 0);
v_isSharedCheck_5947_ = !lean_is_exclusive(v___x_5928_);
if (v_isSharedCheck_5947_ == 0)
{
v___x_5942_ = v___x_5928_;
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_a_5940_);
lean_dec(v___x_5928_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5945_; 
if (v_isShared_5943_ == 0)
{
v___x_5945_ = v___x_5942_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_a_5940_);
v___x_5945_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
return v___x_5945_;
}
}
}
}
else
{
lean_object* v_a_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5955_; 
lean_del_object(v___x_5924_);
lean_dec(v_fst_5910_);
v_a_5948_ = lean_ctor_get(v___x_5926_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5926_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5950_ = v___x_5926_;
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_a_5948_);
lean_dec(v___x_5926_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5953_; 
if (v_isShared_5951_ == 0)
{
v___x_5953_ = v___x_5950_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_a_5948_);
v___x_5953_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
return v___x_5953_;
}
}
}
}
}
else
{
lean_object* v___x_5957_; lean_object* v___x_5959_; 
lean_dec(v_fst_5910_);
lean_dec(v_snd_5889_);
v___x_5957_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___closed__3));
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 0, v___x_5957_);
v___x_5959_ = v___x_5906_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v___x_5957_);
v___x_5959_ = v_reuseFailAlloc_5960_;
goto v_reusejp_5958_;
}
v_reusejp_5958_:
{
return v___x_5959_;
}
}
}
}
}
else
{
lean_object* v_val_5999_; lean_object* v___x_6001_; 
lean_inc_ref(v_fst_5908_);
lean_dec(v_a_5904_);
lean_dec(v_mvarId_5893_);
lean_dec(v_snd_5889_);
lean_dec(v_snd_5886_);
lean_dec(v_a_5876_);
v_val_5999_ = lean_ctor_get(v_fst_5908_, 0);
lean_inc(v_val_5999_);
lean_dec_ref_known(v_fst_5908_, 1);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 0, v_val_5999_);
v___x_6001_ = v___x_5906_;
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
lean_dec(v_mvarId_5893_);
lean_dec(v_snd_5889_);
lean_dec(v_snd_5886_);
lean_dec(v_a_5876_);
v_a_6004_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5903_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5903_);
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
}
}
else
{
lean_object* v_a_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6021_; 
lean_dec_ref(v___x_5878_);
lean_dec(v_a_5876_);
lean_dec_ref(v_kp_5859_);
lean_dec_ref(v_c_5855_);
v_a_6014_ = lean_ctor_get(v___x_5883_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_6016_ = v___x_5883_;
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_a_6014_);
lean_dec(v___x_5883_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6019_; 
if (v_isShared_6017_ == 0)
{
v___x_6019_ = v___x_6016_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_a_6014_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
return v___x_6019_;
}
}
}
}
else
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
lean_dec_ref(v_kp_5859_);
lean_dec(v_candidates_x3f_5858_);
lean_dec(v_numCases_5856_);
lean_dec_ref(v_c_5855_);
lean_dec_ref(v_goal_5854_);
v_a_6022_ = lean_ctor_get(v___x_5875_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_5875_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_5875_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_5875_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
return v___x_6027_;
}
}
}
}
else
{
lean_object* v_a_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6037_; 
lean_dec_ref(v_kp_5859_);
lean_dec(v_candidates_x3f_5858_);
lean_dec(v_numCases_5856_);
lean_dec_ref(v_c_5855_);
lean_dec_ref(v_goal_5854_);
v_a_6030_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6032_ = v___x_5872_;
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_a_6030_);
lean_dec(v___x_5872_);
v___x_6032_ = lean_box(0);
v_isShared_6033_ = v_isSharedCheck_6037_;
goto v_resetjp_6031_;
}
v_resetjp_6031_:
{
lean_object* v___x_6035_; 
if (v_isShared_6033_ == 0)
{
v___x_6035_ = v___x_6032_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_a_6030_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
return v___x_6035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_goal_6038_ = _args[0];
lean_object* v_c_6039_ = _args[1];
lean_object* v_numCases_6040_ = _args[2];
lean_object* v_isRec_6041_ = _args[3];
lean_object* v_candidates_x3f_6042_ = _args[4];
lean_object* v_kp_6043_ = _args[5];
lean_object* v_stopAtFirstFailure_6044_ = _args[6];
lean_object* v_compress_6045_ = _args[7];
lean_object* v___y_6046_ = _args[8];
lean_object* v___y_6047_ = _args[9];
lean_object* v___y_6048_ = _args[10];
lean_object* v___y_6049_ = _args[11];
lean_object* v___y_6050_ = _args[12];
lean_object* v___y_6051_ = _args[13];
lean_object* v___y_6052_ = _args[14];
lean_object* v___y_6053_ = _args[15];
lean_object* v___y_6054_ = _args[16];
lean_object* v___y_6055_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6056_; uint8_t v_stopAtFirstFailure_boxed_6057_; uint8_t v_compress_boxed_6058_; lean_object* v_res_6059_; 
v_isRec_boxed_6056_ = lean_unbox(v_isRec_6041_);
v_stopAtFirstFailure_boxed_6057_ = lean_unbox(v_stopAtFirstFailure_6044_);
v_compress_boxed_6058_ = lean_unbox(v_compress_6045_);
v_res_6059_ = l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2(v_goal_6038_, v_c_6039_, v_numCases_6040_, v_isRec_boxed_6056_, v_candidates_x3f_6042_, v_kp_6043_, v_stopAtFirstFailure_boxed_6057_, v_compress_boxed_6058_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v___y_6046_);
return v_res_6059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg(lean_object* v_c_6060_, lean_object* v_numCases_6061_, uint8_t v_isRec_6062_, uint8_t v_stopAtFirstFailure_6063_, uint8_t v_compress_6064_, lean_object* v_candidates_x3f_6065_, lean_object* v_goal_6066_, lean_object* v_kp_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___f_6081_; lean_object* v___x_6082_; 
v___x_6078_ = lean_box(v_isRec_6062_);
v___x_6079_ = lean_box(v_stopAtFirstFailure_6063_);
v___x_6080_ = lean_box(v_compress_6064_);
lean_inc_ref(v_goal_6066_);
v___f_6081_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___redArg___lam__2___boxed), 18, 8);
lean_closure_set(v___f_6081_, 0, v_goal_6066_);
lean_closure_set(v___f_6081_, 1, v_c_6060_);
lean_closure_set(v___f_6081_, 2, v_numCases_6061_);
lean_closure_set(v___f_6081_, 3, v___x_6078_);
lean_closure_set(v___f_6081_, 4, v_candidates_x3f_6065_);
lean_closure_set(v___f_6081_, 5, v_kp_6067_);
lean_closure_set(v___f_6081_, 6, v___x_6079_);
lean_closure_set(v___f_6081_, 7, v___x_6080_);
v___x_6082_ = l_Lean_Meta_Grind_withHoistedDecls___redArg(v_goal_6066_, v___f_6081_, v_a_6068_, v_a_6069_, v_a_6070_, v_a_6071_, v_a_6072_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___redArg___boxed(lean_object** _args){
lean_object* v_c_6083_ = _args[0];
lean_object* v_numCases_6084_ = _args[1];
lean_object* v_isRec_6085_ = _args[2];
lean_object* v_stopAtFirstFailure_6086_ = _args[3];
lean_object* v_compress_6087_ = _args[4];
lean_object* v_candidates_x3f_6088_ = _args[5];
lean_object* v_goal_6089_ = _args[6];
lean_object* v_kp_6090_ = _args[7];
lean_object* v_a_6091_ = _args[8];
lean_object* v_a_6092_ = _args[9];
lean_object* v_a_6093_ = _args[10];
lean_object* v_a_6094_ = _args[11];
lean_object* v_a_6095_ = _args[12];
lean_object* v_a_6096_ = _args[13];
lean_object* v_a_6097_ = _args[14];
lean_object* v_a_6098_ = _args[15];
lean_object* v_a_6099_ = _args[16];
lean_object* v_a_6100_ = _args[17];
_start:
{
uint8_t v_isRec_boxed_6101_; uint8_t v_stopAtFirstFailure_boxed_6102_; uint8_t v_compress_boxed_6103_; lean_object* v_res_6104_; 
v_isRec_boxed_6101_ = lean_unbox(v_isRec_6085_);
v_stopAtFirstFailure_boxed_6102_ = lean_unbox(v_stopAtFirstFailure_6086_);
v_compress_boxed_6103_ = lean_unbox(v_compress_6087_);
v_res_6104_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6083_, v_numCases_6084_, v_isRec_boxed_6101_, v_stopAtFirstFailure_boxed_6102_, v_compress_boxed_6103_, v_candidates_x3f_6088_, v_goal_6089_, v_kp_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_, v_a_6095_, v_a_6096_, v_a_6097_, v_a_6098_, v_a_6099_);
lean_dec(v_a_6099_);
lean_dec_ref(v_a_6098_);
lean_dec(v_a_6097_);
lean_dec_ref(v_a_6096_);
lean_dec(v_a_6095_);
lean_dec_ref(v_a_6094_);
lean_dec(v_a_6093_);
lean_dec_ref(v_a_6092_);
lean_dec(v_a_6091_);
return v_res_6104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore(lean_object* v_c_6105_, lean_object* v_numCases_6106_, uint8_t v_isRec_6107_, uint8_t v_stopAtFirstFailure_6108_, uint8_t v_compress_6109_, lean_object* v_candidates_x3f_6110_, lean_object* v_goal_6111_, lean_object* v_x_6112_, lean_object* v_kp_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = l_Lean_Meta_Grind_Action_splitCore___redArg(v_c_6105_, v_numCases_6106_, v_isRec_6107_, v_stopAtFirstFailure_6108_, v_compress_6109_, v_candidates_x3f_6110_, v_goal_6111_, v_kp_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitCore___boxed(lean_object** _args){
lean_object* v_c_6125_ = _args[0];
lean_object* v_numCases_6126_ = _args[1];
lean_object* v_isRec_6127_ = _args[2];
lean_object* v_stopAtFirstFailure_6128_ = _args[3];
lean_object* v_compress_6129_ = _args[4];
lean_object* v_candidates_x3f_6130_ = _args[5];
lean_object* v_goal_6131_ = _args[6];
lean_object* v_x_6132_ = _args[7];
lean_object* v_kp_6133_ = _args[8];
lean_object* v_a_6134_ = _args[9];
lean_object* v_a_6135_ = _args[10];
lean_object* v_a_6136_ = _args[11];
lean_object* v_a_6137_ = _args[12];
lean_object* v_a_6138_ = _args[13];
lean_object* v_a_6139_ = _args[14];
lean_object* v_a_6140_ = _args[15];
lean_object* v_a_6141_ = _args[16];
lean_object* v_a_6142_ = _args[17];
lean_object* v_a_6143_ = _args[18];
_start:
{
uint8_t v_isRec_boxed_6144_; uint8_t v_stopAtFirstFailure_boxed_6145_; uint8_t v_compress_boxed_6146_; lean_object* v_res_6147_; 
v_isRec_boxed_6144_ = lean_unbox(v_isRec_6127_);
v_stopAtFirstFailure_boxed_6145_ = lean_unbox(v_stopAtFirstFailure_6128_);
v_compress_boxed_6146_ = lean_unbox(v_compress_6129_);
v_res_6147_ = l_Lean_Meta_Grind_Action_splitCore(v_c_6125_, v_numCases_6126_, v_isRec_boxed_6144_, v_stopAtFirstFailure_boxed_6145_, v_compress_boxed_6146_, v_candidates_x3f_6130_, v_goal_6131_, v_x_6132_, v_kp_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_, v_a_6140_, v_a_6141_, v_a_6142_);
lean_dec(v_a_6142_);
lean_dec_ref(v_a_6141_);
lean_dec(v_a_6140_);
lean_dec_ref(v_a_6139_);
lean_dec(v_a_6138_);
lean_dec_ref(v_a_6137_);
lean_dec(v_a_6136_);
lean_dec_ref(v_a_6135_);
lean_dec(v_a_6134_);
lean_dec_ref(v_x_6132_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(lean_object* v_kp_6148_, lean_object* v_snd_6149_, lean_object* v___x_6150_, uint8_t v_stopAtFirstFailure_6151_, lean_object* v___x_6152_, lean_object* v_as_6153_, lean_object* v_as_x27_6154_, lean_object* v_b_6155_, lean_object* v_a_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v___x_6167_; 
v___x_6167_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___redArg(v_kp_6148_, v_snd_6149_, v___x_6150_, v_stopAtFirstFailure_6151_, v___x_6152_, v_as_x27_6154_, v_b_6155_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
return v___x_6167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4___boxed(lean_object** _args){
lean_object* v_kp_6168_ = _args[0];
lean_object* v_snd_6169_ = _args[1];
lean_object* v___x_6170_ = _args[2];
lean_object* v_stopAtFirstFailure_6171_ = _args[3];
lean_object* v___x_6172_ = _args[4];
lean_object* v_as_6173_ = _args[5];
lean_object* v_as_x27_6174_ = _args[6];
lean_object* v_b_6175_ = _args[7];
lean_object* v_a_6176_ = _args[8];
lean_object* v___y_6177_ = _args[9];
lean_object* v___y_6178_ = _args[10];
lean_object* v___y_6179_ = _args[11];
lean_object* v___y_6180_ = _args[12];
lean_object* v___y_6181_ = _args[13];
lean_object* v___y_6182_ = _args[14];
lean_object* v___y_6183_ = _args[15];
lean_object* v___y_6184_ = _args[16];
lean_object* v___y_6185_ = _args[17];
lean_object* v___y_6186_ = _args[18];
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6187_; lean_object* v_res_6188_; 
v_stopAtFirstFailure_boxed_6187_ = lean_unbox(v_stopAtFirstFailure_6171_);
v_res_6188_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Action_splitCore_spec__4(v_kp_6168_, v_snd_6169_, v___x_6170_, v_stopAtFirstFailure_boxed_6187_, v___x_6172_, v_as_6173_, v_as_x27_6174_, v_b_6175_, v_a_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_);
lean_dec(v___y_6185_);
lean_dec_ref(v___y_6184_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec(v_as_x27_6174_);
lean_dec(v_as_6173_);
lean_dec_ref(v___x_6172_);
lean_dec_ref(v_snd_6169_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(lean_object* v_mvarId_6189_, lean_object* v_val_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_){
_start:
{
lean_object* v___x_6201_; 
v___x_6201_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___redArg(v_mvarId_6189_, v_val_6190_, v___y_6197_);
return v___x_6201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6___boxed(lean_object* v_mvarId_6202_, lean_object* v_val_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6(v_mvarId_6202_, v_val_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
lean_dec(v___y_6212_);
lean_dec_ref(v___y_6211_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
return v_res_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6(lean_object* v_00_u03b2_6215_, lean_object* v_x_6216_, lean_object* v_x_6217_, lean_object* v_x_6218_){
_start:
{
lean_object* v___x_6219_; 
v___x_6219_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6___redArg(v_x_6216_, v_x_6217_, v_x_6218_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(lean_object* v_00_u03b2_6220_, lean_object* v_x_6221_, size_t v_x_6222_, size_t v_x_6223_, lean_object* v_x_6224_, lean_object* v_x_6225_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___redArg(v_x_6221_, v_x_6222_, v_x_6223_, v_x_6224_, v_x_6225_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7___boxed(lean_object* v_00_u03b2_6227_, lean_object* v_x_6228_, lean_object* v_x_6229_, lean_object* v_x_6230_, lean_object* v_x_6231_, lean_object* v_x_6232_){
_start:
{
size_t v_x_68616__boxed_6233_; size_t v_x_68617__boxed_6234_; lean_object* v_res_6235_; 
v_x_68616__boxed_6233_ = lean_unbox_usize(v_x_6229_);
lean_dec(v_x_6229_);
v_x_68617__boxed_6234_ = lean_unbox_usize(v_x_6230_);
lean_dec(v_x_6230_);
v_res_6235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7(v_00_u03b2_6227_, v_x_6228_, v_x_68616__boxed_6233_, v_x_68617__boxed_6234_, v_x_6231_, v_x_6232_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_6236_, lean_object* v_n_6237_, lean_object* v_k_6238_, lean_object* v_v_6239_){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8___redArg(v_n_6237_, v_k_6238_, v_v_6239_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_6241_, size_t v_depth_6242_, lean_object* v_keys_6243_, lean_object* v_vals_6244_, lean_object* v_heq_6245_, lean_object* v_i_6246_, lean_object* v_entries_6247_){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___redArg(v_depth_6242_, v_keys_6243_, v_vals_6244_, v_i_6246_, v_entries_6247_);
return v___x_6248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_6249_, lean_object* v_depth_6250_, lean_object* v_keys_6251_, lean_object* v_vals_6252_, lean_object* v_heq_6253_, lean_object* v_i_6254_, lean_object* v_entries_6255_){
_start:
{
size_t v_depth_boxed_6256_; lean_object* v_res_6257_; 
v_depth_boxed_6256_ = lean_unbox_usize(v_depth_6250_);
lean_dec(v_depth_6250_);
v_res_6257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__9(v_00_u03b2_6249_, v_depth_boxed_6256_, v_keys_6251_, v_vals_6252_, v_heq_6253_, v_i_6254_, v_entries_6255_);
lean_dec_ref(v_vals_6252_);
lean_dec_ref(v_keys_6251_);
return v_res_6257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_6258_, lean_object* v_x_6259_, lean_object* v_x_6260_, lean_object* v_x_6261_, lean_object* v_x_6262_){
_start:
{
lean_object* v___x_6263_; 
v___x_6263_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_Action_splitCore_spec__6_spec__6_spec__7_spec__8_spec__9___redArg(v_x_6259_, v_x_6260_, v_x_6261_, v_x_6262_);
return v___x_6263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0(lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v___x_6277_; 
v___x_6277_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_6264_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
return v___x_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__0___boxed(lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Lean_Meta_Grind_Action_splitNext___lam__0(v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6279_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1(lean_object* v_goal_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_){
_start:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6303_ = lean_st_mk_ref(v_goal_6292_);
v___x_6304_ = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(v___x_6303_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_);
if (lean_obj_tag(v___x_6304_) == 0)
{
lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6314_; 
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6314_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6314_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6314_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6314_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6312_; 
v___x_6309_ = lean_st_ref_get(v___x_6303_);
lean_dec(v___x_6303_);
v___x_6310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6310_, 0, v_a_6305_);
lean_ctor_set(v___x_6310_, 1, v___x_6309_);
if (v_isShared_6308_ == 0)
{
lean_ctor_set(v___x_6307_, 0, v___x_6310_);
v___x_6312_ = v___x_6307_;
goto v_reusejp_6311_;
}
else
{
lean_object* v_reuseFailAlloc_6313_; 
v_reuseFailAlloc_6313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6313_, 0, v___x_6310_);
v___x_6312_ = v_reuseFailAlloc_6313_;
goto v_reusejp_6311_;
}
v_reusejp_6311_:
{
return v___x_6312_;
}
}
}
else
{
lean_object* v_a_6315_; lean_object* v___x_6317_; uint8_t v_isShared_6318_; uint8_t v_isSharedCheck_6322_; 
lean_dec(v___x_6303_);
v_a_6315_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6322_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6322_ == 0)
{
v___x_6317_ = v___x_6304_;
v_isShared_6318_ = v_isSharedCheck_6322_;
goto v_resetjp_6316_;
}
else
{
lean_inc(v_a_6315_);
lean_dec(v___x_6304_);
v___x_6317_ = lean_box(0);
v_isShared_6318_ = v_isSharedCheck_6322_;
goto v_resetjp_6316_;
}
v_resetjp_6316_:
{
lean_object* v___x_6320_; 
if (v_isShared_6318_ == 0)
{
v___x_6320_ = v___x_6317_;
goto v_reusejp_6319_;
}
else
{
lean_object* v_reuseFailAlloc_6321_; 
v_reuseFailAlloc_6321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6321_, 0, v_a_6315_);
v___x_6320_ = v_reuseFailAlloc_6321_;
goto v_reusejp_6319_;
}
v_reusejp_6319_:
{
return v___x_6320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed(lean_object* v_goal_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_){
_start:
{
lean_object* v_res_6334_; 
v_res_6334_ = l_Lean_Meta_Grind_Action_splitNext___lam__1(v_goal_6323_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_);
lean_dec(v___y_6332_);
lean_dec_ref(v___y_6331_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
lean_dec(v___y_6326_);
lean_dec_ref(v___y_6325_);
lean_dec(v___y_6324_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2(lean_object* v___y_6335_, lean_object* v___f_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6350_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 14, 1);
lean_closure_set(v___x_6350_, 0, v___y_6335_);
v___x_6351_ = l_Lean_Meta_Grind_Action_andThen(v___x_6350_, v___f_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
return v___x_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed(lean_object* v___y_6352_, lean_object* v___f_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_){
_start:
{
lean_object* v_res_6367_; 
v_res_6367_ = l_Lean_Meta_Grind_Action_splitNext___lam__2(v___y_6352_, v___f_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_);
lean_dec(v___y_6365_);
lean_dec_ref(v___y_6364_);
lean_dec(v___y_6363_);
lean_dec_ref(v___y_6362_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec(v___y_6359_);
lean_dec_ref(v___y_6358_);
lean_dec(v___y_6357_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext(uint8_t v_stopAtFirstFailure_6369_, uint8_t v_compress_6370_, lean_object* v_goal_6371_, lean_object* v_kna_6372_, lean_object* v_kp_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_, lean_object* v_a_6377_, lean_object* v_a_6378_, lean_object* v_a_6379_, lean_object* v_a_6380_, lean_object* v_a_6381_, lean_object* v_a_6382_){
_start:
{
lean_object* v_toGoalState_6384_; lean_object* v_split_6385_; lean_object* v_mvarId_6386_; lean_object* v_candidates_6387_; lean_object* v___f_6388_; lean_object* v___f_6389_; lean_object* v___x_6390_; 
v_toGoalState_6384_ = lean_ctor_get(v_goal_6371_, 0);
v_split_6385_ = lean_ctor_get(v_toGoalState_6384_, 15);
v_mvarId_6386_ = lean_ctor_get(v_goal_6371_, 1);
lean_inc(v_mvarId_6386_);
v_candidates_6387_ = lean_ctor_get(v_split_6385_, 1);
lean_inc(v_candidates_6387_);
v___f_6388_ = ((lean_object*)(l_Lean_Meta_Grind_Action_splitNext___closed__0));
v___f_6389_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__1___boxed), 11, 1);
lean_closure_set(v___f_6389_, 0, v_goal_6371_);
v___x_6390_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_splitCore_spec__1___redArg(v_mvarId_6386_, v___f_6389_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_);
if (lean_obj_tag(v___x_6390_) == 0)
{
lean_object* v_a_6391_; lean_object* v_fst_6392_; 
v_a_6391_ = lean_ctor_get(v___x_6390_, 0);
lean_inc(v_a_6391_);
lean_dec_ref_known(v___x_6390_, 1);
v_fst_6392_ = lean_ctor_get(v_a_6391_, 0);
if (lean_obj_tag(v_fst_6392_) == 1)
{
lean_object* v_snd_6393_; lean_object* v_c_6394_; lean_object* v_numCases_6395_; uint8_t v_isRec_6396_; lean_object* v___y_6398_; lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; uint8_t v___x_6411_; 
lean_inc_ref(v_fst_6392_);
v_snd_6393_ = lean_ctor_get(v_a_6391_, 1);
lean_inc(v_snd_6393_);
lean_dec(v_a_6391_);
v_c_6394_ = lean_ctor_get(v_fst_6392_, 0);
lean_inc_ref(v_c_6394_);
v_numCases_6395_ = lean_ctor_get(v_fst_6392_, 1);
lean_inc(v_numCases_6395_);
v_isRec_6396_ = lean_ctor_get_uint8(v_fst_6392_, sizeof(void*)*2);
lean_dec_ref_known(v_fst_6392_, 2);
v___x_6406_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_c_6394_);
v___x_6407_ = l_Lean_Meta_Grind_Goal_getGeneration(v_snd_6393_, v___x_6406_);
lean_dec_ref(v___x_6406_);
v___x_6408_ = lean_unsigned_to_nat(1u);
v___x_6411_ = lean_nat_dec_lt(v___x_6408_, v_numCases_6395_);
if (v___x_6411_ == 0)
{
if (v_isRec_6396_ == 0)
{
v___y_6398_ = v___x_6407_;
goto v___jp_6397_;
}
else
{
goto v___jp_6409_;
}
}
else
{
goto v___jp_6409_;
}
v___jp_6397_:
{
lean_object* v___f_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___f_6399_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitNext___lam__2___boxed), 15, 2);
lean_closure_set(v___f_6399_, 0, v___y_6398_);
lean_closure_set(v___f_6399_, 1, v___f_6388_);
v___x_6400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6400_, 0, v_candidates_6387_);
v___x_6401_ = lean_box(v_isRec_6396_);
v___x_6402_ = lean_box(v_stopAtFirstFailure_6369_);
v___x_6403_ = lean_box(v_compress_6370_);
v___x_6404_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_splitCore___boxed), 19, 6);
lean_closure_set(v___x_6404_, 0, v_c_6394_);
lean_closure_set(v___x_6404_, 1, v_numCases_6395_);
lean_closure_set(v___x_6404_, 2, v___x_6401_);
lean_closure_set(v___x_6404_, 3, v___x_6402_);
lean_closure_set(v___x_6404_, 4, v___x_6403_);
lean_closure_set(v___x_6404_, 5, v___x_6400_);
v___x_6405_ = l_Lean_Meta_Grind_Action_andThen(v___x_6404_, v___f_6399_, v_snd_6393_, v_kna_6372_, v_kp_6373_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_);
return v___x_6405_;
}
v___jp_6409_:
{
lean_object* v___x_6410_; 
v___x_6410_ = lean_nat_add(v___x_6407_, v___x_6408_);
lean_dec(v___x_6407_);
v___y_6398_ = v___x_6410_;
goto v___jp_6397_;
}
}
else
{
lean_object* v_snd_6412_; lean_object* v___x_6413_; 
lean_dec(v_candidates_6387_);
lean_dec_ref(v_kp_6373_);
v_snd_6412_ = lean_ctor_get(v_a_6391_, 1);
lean_inc(v_snd_6412_);
lean_dec(v_a_6391_);
lean_inc(v_a_6382_);
lean_inc_ref(v_a_6381_);
lean_inc(v_a_6380_);
lean_inc_ref(v_a_6379_);
lean_inc(v_a_6378_);
lean_inc_ref(v_a_6377_);
lean_inc(v_a_6376_);
lean_inc_ref(v_a_6375_);
lean_inc(v_a_6374_);
v___x_6413_ = lean_apply_11(v_kna_6372_, v_snd_6412_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_, lean_box(0));
return v___x_6413_;
}
}
else
{
lean_object* v_a_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6421_; 
lean_dec(v_candidates_6387_);
lean_dec_ref(v_kp_6373_);
lean_dec_ref(v_kna_6372_);
v_a_6414_ = lean_ctor_get(v___x_6390_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6390_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6416_ = v___x_6390_;
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_a_6414_);
lean_dec(v___x_6390_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v___x_6419_; 
if (v_isShared_6417_ == 0)
{
v___x_6419_ = v___x_6416_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
return v___x_6419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object* v_stopAtFirstFailure_6422_, lean_object* v_compress_6423_, lean_object* v_goal_6424_, lean_object* v_kna_6425_, lean_object* v_kp_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_, lean_object* v_a_6436_){
_start:
{
uint8_t v_stopAtFirstFailure_boxed_6437_; uint8_t v_compress_boxed_6438_; lean_object* v_res_6439_; 
v_stopAtFirstFailure_boxed_6437_ = lean_unbox(v_stopAtFirstFailure_6422_);
v_compress_boxed_6438_ = lean_unbox(v_compress_6423_);
v_res_6439_ = l_Lean_Meta_Grind_Action_splitNext(v_stopAtFirstFailure_boxed_6437_, v_compress_boxed_6438_, v_goal_6424_, v_kna_6425_, v_kp_6426_, v_a_6427_, v_a_6428_, v_a_6429_, v_a_6430_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_, v_a_6435_);
lean_dec(v_a_6435_);
lean_dec_ref(v_a_6434_);
lean_dec(v_a_6433_);
lean_dec_ref(v_a_6432_);
lean_dec(v_a_6431_);
lean_dec_ref(v_a_6430_);
lean_dec(v_a_6429_);
lean_dec_ref(v_a_6428_);
lean_dec(v_a_6427_);
return v_res_6439_;
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
