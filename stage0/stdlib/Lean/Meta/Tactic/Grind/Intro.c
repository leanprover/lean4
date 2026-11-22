// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Injection import Lean.Meta.Tactic.Grind.Core import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.MarkAccessible import Lean.Meta.Tactic.Grind.Anchor import Init.Data.List.MapIdx import Init.Grind.Util
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_isEagerSplit___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_setIntroBase(lean_object*, uint64_t);
lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerFVarAnchor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
uint8_t l_Lean_Meta_Grind_isMatchCondCandidate(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_Grind_isInterpreted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedGoal_default;
lean_object* l_Lean_Meta_Grind_Solvers_mkActionCore();
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "alreadyNorm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 221, 60, 184, 251, 204, 208, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`grind` internal error, binder expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "intro_with_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 88, 152, 82, 213, 6, 119, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "intro_with_eq'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 115, 213, 198, 106, 77, 45, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object**);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object*, uint8_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Action_intro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_intro___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_intro___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_intros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_intros___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_intros___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_intros___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Action_intros___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_ungroup___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_intros___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_intros___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Solvers_mkAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Solvers_mkAction___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Solvers_mkAction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 1:
{
lean_object* v_fvarId_7_; lean_object* v_goal_8_; lean_object* v___x_9_; 
v_fvarId_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_fvarId_7_);
v_goal_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_goal_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_fvarId_7_, v_goal_8_);
return v___x_9_;
}
case 3:
{
lean_object* v_fvarId_10_; lean_object* v_goal_11_; lean_object* v___x_12_; 
v_fvarId_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_fvarId_10_);
v_goal_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_goal_11_);
lean_dec_ref_known(v_t_5_, 2);
v___x_12_ = lean_apply_2(v_k_6_, v_fvarId_10_, v_goal_11_);
return v___x_12_;
}
default: 
{
lean_object* v_goal_13_; lean_object* v___x_14_; 
v_goal_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_goal_13_);
lean_dec_ref(v_t_5_);
v___x_14_ = lean_apply_1(v_k_6_, v_goal_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim___redArg(lean_object* v_t_27_, lean_object* v_done_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_27_, v_done_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_done_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_31_, v_done_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim___redArg(lean_object* v_t_35_, lean_object* v_newHyp_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_35_, v_newHyp_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_newHyp_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_39_, v_newHyp_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim___redArg(lean_object* v_t_43_, lean_object* v_newDepHyp_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_43_, v_newDepHyp_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_newDepHyp_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_47_, v_newDepHyp_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim___redArg(lean_object* v_t_51_, lean_object* v_newLocal_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_51_, v_newLocal_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_newLocal_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_55_, v_newLocal_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = l_Lean_Meta_Grind_instInhabitedGoal_default;
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0, &l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0);
return v___x_61_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_Grind_instInhabitedIntroResult_default;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object* v_e_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = l_Lean_Expr_cleanupAnnotations(v_e_70_);
v___x_72_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v___x_71_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3));
v___x_76_ = l_Lean_Expr_isConstOf(v___x_74_, v___x_75_);
lean_dec_ref(v___x_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v___x_71_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v_arg_78_; lean_object* v___x_79_; 
v_arg_78_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_78_);
lean_dec_ref(v___x_71_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_arg_78_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___boxed(lean_object* v_e_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_80_);
lean_dec_ref(v_e_80_);
return v_res_81_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(lean_object* v_type_94_){
_start:
{
lean_object* v_type_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_type_95_ = l_Lean_Expr_consumeMData(v_type_94_);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1));
v___x_97_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3));
v___x_99_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5));
v___x_101_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7));
v___x_103_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_102_);
lean_dec_ref(v_type_95_);
return v___x_103_;
}
else
{
lean_dec_ref(v_type_95_);
return v___x_101_;
}
}
else
{
lean_dec_ref(v_type_95_);
return v___x_99_;
}
}
else
{
lean_dec_ref(v_type_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___boxed(lean_object* v_type_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_type_104_);
lean_dec_ref(v_type_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(lean_object* v_e_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = l_Lean_Expr_cleanupAnnotations(v_e_117_);
v___x_119_ = l_Lean_Expr_isApp(v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_118_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
lean_dec_ref(v___x_118_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_123_ = l_Lean_Expr_isApp(v___x_122_);
if (v___x_123_ == 0)
{
lean_dec_ref(v___x_122_);
lean_dec_ref(v___x_120_);
lean_dec_ref(v___x_118_);
return v___x_123_;
}
else
{
lean_object* v_arg_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc_ref(v_arg_124_);
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_122_);
lean_dec_ref(v___x_122_);
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
lean_dec_ref(v___x_118_);
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5));
v___x_129_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_128_);
lean_dec_ref(v___x_125_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_arg_124_);
lean_dec_ref(v___x_120_);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_arg_124_);
lean_dec_ref(v_arg_124_);
if (v___x_130_ == 0)
{
lean_dec_ref(v___x_120_);
return v___x_130_;
}
else
{
lean_object* v_arg_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_arg_131_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_131_);
lean_dec_ref(v___x_120_);
v___x_132_ = l_Lean_Expr_consumeMData(v_arg_131_);
lean_dec_ref(v_arg_131_);
v___x_133_ = l_Lean_Expr_isRawNatLit(v___x_132_);
lean_dec_ref(v___x_132_);
return v___x_133_;
}
}
}
else
{
lean_object* v_arg_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
lean_dec_ref(v___x_125_);
lean_dec_ref(v___x_120_);
v_arg_134_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_arg_134_);
lean_dec_ref(v___x_118_);
v___x_135_ = l_Lean_Expr_cleanupAnnotations(v_arg_134_);
lean_dec_ref(v_arg_134_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v___x_135_);
lean_dec_ref(v_arg_124_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
lean_dec_ref(v___x_135_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
v___x_140_ = l_Lean_Expr_isApp(v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_139_);
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_139_);
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_142_);
lean_dec_ref(v___x_141_);
if (v___x_143_ == 0)
{
lean_dec_ref(v___x_139_);
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_143_;
}
else
{
lean_object* v_arg_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_arg_144_ = lean_ctor_get(v___x_139_, 1);
lean_inc_ref(v_arg_144_);
lean_dec_ref(v___x_139_);
v___x_145_ = l_Lean_Expr_consumeMData(v_arg_124_);
v___x_146_ = l_Lean_Expr_consumeMData(v_arg_144_);
lean_dec_ref(v_arg_144_);
v___x_147_ = lean_expr_eqv(v___x_145_, v___x_146_);
lean_dec_ref(v___x_146_);
lean_dec_ref(v___x_145_);
if (v___x_147_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_arg_124_);
lean_dec_ref(v_arg_124_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_137_);
return v___x_148_;
}
else
{
lean_object* v_arg_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_arg_149_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_arg_149_);
lean_dec_ref(v___x_137_);
v___x_150_ = l_Lean_Expr_consumeMData(v_arg_149_);
lean_dec_ref(v_arg_149_);
v___x_151_ = l_Lean_Expr_isRawNatLit(v___x_150_);
lean_dec_ref(v___x_150_);
return v___x_151_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___boxed(lean_object* v_e_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_e_152_);
lean_dec_ref(v_e_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Expr_hasLooseBVars(v_e_155_);
if (v___x_165_ == 0)
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_Expr_isTrue(v_e_155_);
if (v___x_166_ == 0)
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_Expr_isFalse(v_e_155_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_inc_ref(v_e_155_);
v___x_168_ = l_Lean_Meta_Grind_isInterpreted(v_e_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; uint8_t v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v___x_170_ = lean_unbox(v_a_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_180_);
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_e_155_);
lean_dec_ref(v_e_155_);
v___x_175_ = lean_box(v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_dec_ref(v_e_155_);
return v___x_168_;
}
}
else
{
lean_dec_ref(v_e_155_);
return v___x_168_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
v___jp_161_:
{
uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 0;
v___x_163_ = lean_box(v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue___boxed(lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0(void){
_start:
{
lean_object* v___x_191_; lean_object* v_dummy_192_; 
v___x_191_ = lean_box(0);
v_dummy_192_ = l_Lean_Expr_sort___override(v___x_191_);
return v_dummy_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Expr_getAppFn(v_e_198_);
v___x_205_ = l_Lean_Expr_isBVar(v___x_204_);
v___x_206_ = 1;
if (v___x_205_ == 0)
{
lean_object* v___x_207_; 
lean_inc_ref(v_e_198_);
v___x_207_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_314_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_314_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_314_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_314_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___x_272_; 
v___x_272_ = lean_unbox(v_a_208_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_inc_ref(v_e_198_);
v___x_273_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_198_, v_a_200_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_303_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_303_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_303_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_303_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = l_Lean_Expr_cleanupAnnotations(v_a_274_);
lean_dec(v_a_274_);
v___x_279_ = l_Lean_Expr_isApp(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_278_);
v___x_281_ = l_Lean_Expr_isApp(v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_280_);
v___x_283_ = l_Lean_Expr_isApp(v___x_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v___x_282_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_282_);
lean_dec_ref(v___x_282_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v___x_284_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
lean_dec_ref(v___x_284_);
v___x_287_ = l_Lean_Expr_isApp(v___x_286_);
if (v___x_287_ == 0)
{
lean_dec_ref(v___x_286_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_286_);
lean_dec_ref(v___x_286_);
v___x_289_ = l_Lean_Expr_isApp(v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v___x_288_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_288_);
lean_dec_ref(v___x_288_);
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_290_, v___x_291_);
lean_dec_ref(v___x_290_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v_arg_293_; uint8_t v___x_294_; 
lean_del_object(v___x_210_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v_arg_293_ = lean_ctor_get(v___x_278_, 1);
lean_inc_ref(v_arg_293_);
lean_dec_ref(v___x_278_);
v___x_294_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_arg_293_);
if (v___x_294_ == 0)
{
lean_object* v_arg_295_; lean_object* v___x_296_; 
lean_del_object(v___x_276_);
lean_dec(v_a_208_);
v_arg_295_ = lean_ctor_get(v___x_280_, 1);
lean_inc_ref(v_arg_295_);
lean_dec_ref(v___x_280_);
v___x_296_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_arg_293_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = lean_unbox(v_a_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_arg_295_);
return v___x_296_;
}
else
{
lean_dec_ref_known(v___x_296_, 1);
v_e_198_ = v_arg_295_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_295_);
return v___x_296_;
}
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_arg_293_);
lean_dec_ref(v___x_280_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_a_208_);
v___x_301_ = v___x_276_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_208_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
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
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_210_);
lean_dec(v_a_208_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v_a_304_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_273_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_273_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_del_object(v___x_210_);
lean_dec(v_a_208_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v___x_312_ = lean_box(v___x_206_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
v___jp_212_:
{
if (lean_obj_tag(v___x_204_) == 4)
{
lean_object* v_declName_217_; lean_object* v___x_218_; lean_object* v_env_219_; uint8_t v___x_220_; lean_object* v___x_221_; 
v_declName_217_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_declName_217_);
lean_dec_ref_known(v___x_204_, 2);
v___x_218_ = lean_st_ref_get(v___y_216_);
v_env_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_env_219_);
lean_dec(v___x_218_);
v___x_220_ = lean_unbox(v_a_208_);
v___x_221_ = l_Lean_Environment_find_x3f(v_env_219_, v_declName_217_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 1)
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
if (lean_obj_tag(v_val_222_) == 6)
{
lean_object* v_val_223_; lean_object* v_numParams_224_; lean_object* v_numFields_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_dec(v_a_208_);
v_val_223_ = lean_ctor_get(v_val_222_, 0);
lean_inc_ref(v_val_223_);
lean_dec_ref_known(v_val_222_, 1);
v_numParams_224_ = lean_ctor_get(v_val_223_, 3);
lean_inc(v_numParams_224_);
v_numFields_225_ = lean_ctor_get(v_val_223_, 4);
lean_inc(v_numFields_225_);
lean_dec_ref(v_val_223_);
v___x_226_ = l_Lean_Expr_getAppNumArgs(v_e_198_);
v___x_227_ = lean_nat_add(v_numParams_224_, v_numFields_225_);
lean_dec(v_numFields_225_);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v___x_226_);
lean_dec(v_numParams_224_);
lean_dec_ref(v_e_198_);
v___x_229_ = lean_box(v___x_228_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_229_);
v___x_231_ = v___x_210_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
else
{
lean_object* v_dummy_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_210_);
v_dummy_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0);
lean_inc(v___x_226_);
v___x_234_ = lean_mk_array(v___x_226_, v_dummy_233_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_sub(v___x_226_, v___x_235_);
lean_dec(v___x_226_);
v___x_237_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_198_, v___x_234_, v___x_236_);
v___x_238_ = lean_array_get_size(v___x_237_);
v___x_239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0));
v___x_240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v___x_238_, v___x_237_, v_numParams_224_, v___x_239_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec_ref(v___x_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_254_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_254_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_fst_245_; 
v_fst_245_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_fst_245_);
lean_dec(v_a_241_);
if (lean_obj_tag(v_fst_245_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_box(v___x_206_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_246_);
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v_val_250_; lean_object* v___x_252_; 
v_val_250_ = lean_ctor_get(v_fst_245_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v_fst_245_, 1);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_val_250_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_val_250_);
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
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_240_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_240_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_val_222_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_264_ = v___x_210_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_208_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v___x_221_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_267_ = v___x_210_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_208_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v___x_270_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_270_ = v___x_210_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_208_);
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
}
else
{
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
return v___x_207_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v___x_315_ = lean_box(v___x_206_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(lean_object* v_upperBound_317_, lean_object* v___x_318_, lean_object* v_a_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_lt(v_a_319_, v_upperBound_317_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec(v_a_319_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_b_320_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v_b_320_);
v___x_328_ = l_Lean_instInhabitedExpr;
v___x_329_ = lean_box(0);
v___x_330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0));
v___x_331_ = lean_array_get_borrowed(v___x_328_, v___x_318_, v_a_319_);
lean_inc(v___x_331_);
v___x_332_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v___x_331_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_346_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_346_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
uint8_t v___x_337_; 
v___x_337_ = lean_unbox(v_a_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_a_319_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_333_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_329_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_339_);
v___x_341_ = v___x_335_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_335_);
lean_dec(v_a_333_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_a_319_, v___x_343_);
lean_dec(v_a_319_);
v_a_319_ = v___x_344_;
v_b_320_ = v___x_330_;
goto _start;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_319_);
v_a_347_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_332_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_332_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___boxed(lean_object* v_upperBound_355_, lean_object* v___x_356_, lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v_upperBound_355_, v___x_356_, v_a_357_, v_b_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___x_356_);
lean_dec(v_upperBound_355_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(lean_object* v_upperBound_372_, lean_object* v___x_373_, lean_object* v_inst_374_, lean_object* v_R_375_, lean_object* v_a_376_, lean_object* v_b_377_, lean_object* v_c_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v_upperBound_372_, v___x_373_, v_a_376_, v_b_377_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___boxed(lean_object* v_upperBound_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_c_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(v_upperBound_385_, v___x_386_, v_inst_387_, v_R_388_, v_a_389_, v_b_390_, v_c_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v___x_386_);
lean_dec(v_upperBound_385_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
if (lean_obj_tag(v_e_404_) == 7)
{
lean_object* v_binderType_410_; lean_object* v_body_411_; lean_object* v_rhs_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___x_422_; 
v_binderType_410_ = lean_ctor_get(v_e_404_, 1);
lean_inc_ref(v_binderType_410_);
v_body_411_ = lean_ctor_get(v_e_404_, 2);
lean_inc_ref(v_body_411_);
lean_dec_ref_known(v_e_404_, 3);
v___x_422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_410_, v_a_406_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_Expr_cleanupAnnotations(v_a_423_);
lean_dec(v_a_423_);
v___x_425_ = l_Lean_Expr_isApp(v___x_424_);
if (v___x_425_ == 0)
{
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_424_);
v___x_428_ = l_Lean_Expr_isApp(v___x_427_);
if (v___x_428_ == 0)
{
lean_dec_ref(v___x_427_);
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_427_);
lean_dec_ref(v___x_427_);
v___x_431_ = l_Lean_Expr_isApp(v___x_430_);
if (v___x_431_ == 0)
{
lean_dec_ref(v___x_430_);
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v_arg_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_arg_433_ = lean_ctor_get(v___x_424_, 1);
lean_inc_ref(v_arg_433_);
lean_dec_ref(v___x_424_);
v___x_434_ = l_Lean_Expr_appFnCleanup___redArg(v___x_430_);
lean_dec_ref(v___x_430_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1));
v___x_436_ = l_Lean_Expr_isConstOf(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Expr_isApp(v___x_434_);
if (v___x_437_ == 0)
{
lean_dec_ref(v___x_434_);
lean_dec_ref(v_arg_433_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_434_);
lean_dec_ref(v___x_434_);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3));
v___x_441_ = l_Lean_Expr_isConstOf(v___x_439_, v___x_440_);
lean_dec_ref(v___x_439_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_arg_433_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
v_rhs_413_ = v_arg_433_;
v___y_414_ = v_a_405_;
v___y_415_ = v_a_406_;
v___y_416_ = v_a_407_;
v___y_417_ = v_a_408_;
goto v___jp_412_;
}
}
}
else
{
lean_dec_ref(v___x_434_);
v_rhs_413_ = v_arg_433_;
v___y_414_ = v_a_405_;
v___y_415_ = v_a_406_;
v___y_416_ = v_a_407_;
v___y_417_ = v_a_408_;
goto v___jp_412_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_body_411_);
v_a_443_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_422_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_422_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
v___jp_412_:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v_rhs_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; uint8_t v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = lean_unbox(v_a_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v_body_411_);
return v___x_418_;
}
else
{
lean_dec_ref_known(v___x_418_, 1);
v_e_404_ = v_body_411_;
v_a_405_ = v___y_414_;
v_a_406_ = v___y_415_;
v_a_407_ = v___y_416_;
v_a_408_ = v___y_417_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_411_);
return v___x_418_;
}
}
}
else
{
uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v_e_404_);
v___x_451_ = 1;
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(v_e_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_461_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_e_461_);
v___x_468_ = lean_box(v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
lean_inc_ref(v_e_478_);
v___x_490_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(v_e_478_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_478_);
if (lean_obj_tag(v___x_493_) == 1)
{
lean_object* v_val_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
lean_dec_ref(v_e_478_);
v_val_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = 1;
v___x_496_ = l_Lean_Meta_Sym_canon(v_val_494_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Lean_Meta_Sym_shareCommon(v_a_497_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_504_, 0, v_a_499_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2, v___x_495_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_498_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_498_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_496_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_496_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v___x_493_);
lean_inc(v_a_488_);
lean_inc_ref(v_a_487_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc(v_a_479_);
v___x_525_ = lean_grind_preprocess(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_478_);
lean_inc(v_a_488_);
lean_inc_ref(v_a_487_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc(v_a_479_);
v___x_527_ = lean_grind_preprocess(v___x_526_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_527_;
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_e_478_);
v_a_528_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_490_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_490_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object* v_e_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_549_, lean_object* v_str_550_, lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
uint8_t v_decide_553_; 
v_decide_553_ = lean_nat_dec_eq(v_a_551_, v___x_549_);
if (v_decide_553_ == 0)
{
uint32_t v___x_554_; uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_string_utf8_get_fast(v_str_550_, v_a_551_);
v___x_555_ = 95;
v___x_556_ = lean_uint32_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_string_utf8_next_fast(v_str_550_, v_a_551_);
lean_dec(v_a_551_);
v_a_551_ = v___x_558_;
v_b_552_ = v___x_557_;
goto _start;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_a_551_);
return v___x_560_;
}
}
else
{
lean_dec(v_a_551_);
lean_inc(v_b_552_);
return v_b_552_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_561_, lean_object* v_str_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_561_, v_str_562_, v_a_563_, v_b_564_);
lean_dec(v_b_564_);
lean_dec_ref(v_str_562_);
lean_dec(v___x_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_572_, lean_object* v_type_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; 
if (lean_obj_tag(v_name_572_) == 1)
{
lean_object* v_str_607_; lean_object* v___y_609_; lean_object* v_searcher_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_str_607_ = lean_ctor_get(v_name_572_, 1);
lean_inc_ref(v_str_607_);
lean_dec_ref_known(v_name_572_, 2);
v_searcher_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_string_utf8_byte_size(v_str_607_);
v___x_629_ = lean_box(0);
v___x_630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_628_, v_str_607_, v_searcher_627_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
v___y_609_ = v___x_628_;
goto v___jp_608_;
}
else
{
lean_object* v_val_631_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___y_609_ = v_val_631_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_610_; uint8_t v_decide_611_; 
v___x_610_ = lean_string_utf8_byte_size(v_str_607_);
v_decide_611_ = lean_nat_dec_eq(v___y_609_, v___x_610_);
if (v_decide_611_ == 0)
{
lean_object* v___x_612_; lean_object* v_suffix_613_; uint8_t v___x_614_; 
v___x_612_ = lean_string_utf8_next_fast(v_str_607_, v___y_609_);
lean_inc_ref(v_str_607_);
v_suffix_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_613_, 0, v_str_607_);
lean_ctor_set(v_suffix_613_, 1, v___x_612_);
lean_ctor_set(v_suffix_613_, 2, v___x_610_);
v___x_614_ = l_String_Slice_isNat(v_suffix_613_);
lean_dec_ref_known(v_suffix_613_, 3);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v___y_609_);
lean_dec_ref(v_type_573_);
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Name_str___override(v___x_615_, v_str_607_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_nat_dec_eq(v___y_609_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref(v_type_573_);
v___x_620_ = lean_string_utf8_extract_fast(v_str_607_, v___x_618_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v_str_607_);
v___x_621_ = lean_box(0);
v___x_622_ = l_Lean_Name_str___override(v___x_621_, v___x_620_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
lean_dec(v___y_609_);
lean_dec_ref(v_str_607_);
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___y_609_);
lean_dec_ref(v_type_573_);
v___x_624_ = lean_box(0);
v___x_625_ = l_Lean_Name_str___override(v___x_624_, v_str_607_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_dec(v_name_572_);
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_isProp(v_type_573_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_598_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_598_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_594_);
v___x_596_ = v___x_587_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_584_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_584_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_632_, lean_object* v_type_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_632_, v_type_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v_str_642_, lean_object* v_inst_643_, lean_object* v_R_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v_c_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_640_, v_str_642_, v_a_645_, v_b_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v_str_651_, lean_object* v_inst_652_, lean_object* v_R_653_, lean_object* v_a_654_, lean_object* v_b_655_, lean_object* v_c_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_649_, v___x_650_, v_str_651_, v_inst_652_, v_R_653_, v_a_654_, v_b_655_, v_c_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_str_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_658_, lean_object* v_i_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_keys_658_);
v___x_662_ = lean_nat_dec_lt(v_i_659_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec(v_i_659_);
return v___x_662_;
}
else
{
lean_object* v_k_x27_663_; uint8_t v___x_664_; 
v_k_x27_663_ = lean_array_fget_borrowed(v_keys_658_, v_i_659_);
v___x_664_ = lean_name_eq(v_k_660_, v_k_x27_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_i_659_, v___x_665_);
lean_dec(v_i_659_);
v_i_659_ = v___x_666_;
goto _start;
}
else
{
lean_dec(v_i_659_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_668_, lean_object* v_i_669_, lean_object* v_k_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_668_, v_i_669_, v_k_670_);
lean_dec(v_k_670_);
lean_dec_ref(v_keys_668_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_673_, size_t v_x_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v_es_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v_j_680_; lean_object* v___x_681_; 
v_es_676_ = lean_ctor_get(v_x_673_, 0);
v___x_677_ = lean_box(2);
v___x_678_ = ((size_t)31ULL);
v___x_679_ = lean_usize_land(v_x_674_, v___x_678_);
v_j_680_ = lean_usize_to_nat(v___x_679_);
v___x_681_ = lean_array_get_borrowed(v___x_677_, v_es_676_, v_j_680_);
lean_dec(v_j_680_);
switch(lean_obj_tag(v___x_681_))
{
case 0:
{
lean_object* v_key_682_; uint8_t v___x_683_; 
v_key_682_ = lean_ctor_get(v___x_681_, 0);
v___x_683_ = lean_name_eq(v_x_675_, v_key_682_);
return v___x_683_;
}
case 1:
{
lean_object* v_node_684_; size_t v___x_685_; size_t v___x_686_; 
v_node_684_ = lean_ctor_get(v___x_681_, 0);
v___x_685_ = ((size_t)5ULL);
v___x_686_ = lean_usize_shift_right(v_x_674_, v___x_685_);
v_x_673_ = v_node_684_;
v_x_674_ = v___x_686_;
goto _start;
}
default: 
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
}
else
{
lean_object* v_ks_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_ks_689_ = lean_ctor_get(v_x_673_, 0);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_689_, v___x_690_, v_x_675_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
size_t v_x_33592__boxed_695_; uint8_t v_res_696_; lean_object* v_r_697_; 
v_x_33592__boxed_695_ = lean_unbox_usize(v_x_693_);
lean_dec(v_x_693_);
v_res_696_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_692_, v_x_33592__boxed_695_, v_x_694_);
lean_dec(v_x_694_);
lean_dec_ref(v_x_692_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
uint64_t v___y_701_; 
if (lean_obj_tag(v_x_699_) == 0)
{
uint64_t v___x_704_; 
v___x_704_ = 1723ULL;
v___y_701_ = v___x_704_;
goto v___jp_700_;
}
else
{
uint64_t v_hash_705_; 
v_hash_705_ = lean_ctor_get_uint64(v_x_699_, sizeof(void*)*2);
v___y_701_ = v_hash_705_;
goto v___jp_700_;
}
v___jp_700_:
{
size_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_uint64_to_usize(v___y_701_);
v___x_703_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_698_, v___x_702_, v_x_699_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_x_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_734_; 
v_snd_714_ = lean_ctor_get(v_a_711_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_a_711_, 0);
lean_dec(v_unused_735_);
v___x_716_ = v_a_711_;
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_dec(v_a_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_toGoalState_722_; lean_object* v_clean_723_; lean_object* v_used_724_; uint8_t v___x_725_; 
lean_inc(v_snd_714_);
lean_inc(v_a_710_);
v___x_718_ = lean_name_append_index_after(v_a_710_, v_snd_714_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v_snd_714_, v___x_719_);
lean_dec(v_snd_714_);
v___x_721_ = lean_st_ref_get(v___y_712_);
v_toGoalState_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_toGoalState_722_);
lean_dec(v___x_721_);
v_clean_723_ = lean_ctor_get(v_toGoalState_722_, 16);
lean_inc_ref(v_clean_723_);
lean_dec_ref(v_toGoalState_722_);
v_used_724_ = lean_ctor_get(v_clean_723_, 0);
lean_inc_ref(v_used_724_);
lean_dec_ref(v_clean_723_);
v___x_725_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_724_, v___x_718_);
lean_dec_ref(v_used_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v_a_710_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_720_);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_720_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
else
{
lean_object* v___x_731_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_720_);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_731_ = v___x_716_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_720_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_711_ = v___x_731_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_736_, v_a_737_, v___y_738_);
lean_dec(v___y_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_ks_745_; lean_object* v_vs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
v_ks_745_ = lean_ctor_get(v_x_741_, 0);
v_vs_746_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_vs_746_);
lean_inc(v_ks_745_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_ks_745_);
v___x_751_ = lean_nat_dec_lt(v_x_742_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_x_742_);
v___x_752_ = lean_array_push(v_ks_745_, v_x_743_);
v___x_753_ = lean_array_push(v_vs_746_, v_x_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_ks_745_, v_x_742_);
v___x_758_ = lean_name_eq(v_x_743_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; 
if (v_isShared_749_ == 0)
{
v___x_760_ = v___x_748_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_746_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_742_, v___x_761_);
lean_dec(v_x_742_);
v_x_741_ = v___x_760_;
v_x_742_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_array_fset(v_ks_745_, v_x_742_, v_x_743_);
v___x_766_ = lean_array_fset(v_vs_746_, v_x_742_, v_x_744_);
lean_dec(v_x_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_766_);
lean_ctor_set(v___x_748_, 0, v___x_765_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_771_, v___x_774_, v_k_772_, v_v_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_777_, size_t v_x_778_, size_t v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_es_782_; size_t v___x_783_; size_t v___x_784_; lean_object* v_j_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_es_782_ = lean_ctor_get(v_x_777_, 0);
v___x_783_ = ((size_t)31ULL);
v___x_784_ = lean_usize_land(v_x_778_, v___x_783_);
v_j_785_ = lean_usize_to_nat(v___x_784_);
v___x_786_ = lean_array_get_size(v_es_782_);
v___x_787_ = lean_nat_dec_lt(v_j_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_dec(v_j_785_);
lean_dec(v_x_781_);
lean_dec(v_x_780_);
return v_x_777_;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_826_; 
lean_inc_ref(v_es_782_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_x_777_, 0);
lean_dec(v_unused_827_);
v___x_789_ = v_x_777_;
v_isShared_790_ = v_isSharedCheck_826_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_826_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_v_791_; lean_object* v___x_792_; lean_object* v_xs_x27_793_; lean_object* v___y_795_; 
v_v_791_ = lean_array_fget(v_es_782_, v_j_785_);
v___x_792_ = lean_box(0);
v_xs_x27_793_ = lean_array_fset(v_es_782_, v_j_785_, v___x_792_);
switch(lean_obj_tag(v_v_791_))
{
case 0:
{
lean_object* v_key_800_; lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
v_key_800_ = lean_ctor_get(v_v_791_, 0);
v_val_801_ = lean_ctor_get(v_v_791_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v_v_791_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_inc(v_key_800_);
lean_dec(v_v_791_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint8_t v___x_805_; 
v___x_805_ = lean_name_eq(v_x_780_, v_key_800_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_803_);
v___x_806_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_800_, v_val_801_, v_x_780_, v_x_781_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___y_795_ = v___x_807_;
goto v___jp_794_;
}
else
{
lean_object* v___x_809_; 
lean_dec(v_val_801_);
lean_dec(v_key_800_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_x_781_);
lean_ctor_set(v___x_803_, 0, v_x_780_);
v___x_809_ = v___x_803_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_x_780_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_x_781_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_795_ = v___x_809_;
goto v___jp_794_;
}
}
}
}
case 1:
{
lean_object* v_node_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_824_; 
v_node_812_ = lean_ctor_get(v_v_791_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_824_ == 0)
{
v___x_814_ = v_v_791_;
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_node_812_);
lean_dec(v_v_791_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_816_ = ((size_t)5ULL);
v___x_817_ = lean_usize_shift_right(v_x_778_, v___x_816_);
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_x_779_, v___x_818_);
v___x_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_812_, v___x_817_, v___x_819_, v_x_780_, v_x_781_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_820_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v___y_795_ = v___x_822_;
goto v___jp_794_;
}
}
}
default: 
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_x_780_);
lean_ctor_set(v___x_825_, 1, v_x_781_);
v___y_795_ = v___x_825_;
goto v___jp_794_;
}
}
v___jp_794_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_array_fset(v_xs_x27_793_, v_j_785_, v___y_795_);
lean_dec(v_j_785_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_796_);
v___x_798_ = v___x_789_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
else
{
lean_object* v_ks_828_; lean_object* v_vs_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_847_; 
v_ks_828_ = lean_ctor_get(v_x_777_, 0);
v_vs_829_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_847_ == 0)
{
v___x_831_ = v_x_777_;
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_vs_829_);
lean_inc(v_ks_828_);
lean_dec(v_x_777_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_ks_828_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_vs_829_);
v___x_834_ = v_reuseFailAlloc_846_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v_newNode_835_; size_t v___x_836_; uint8_t v___x_837_; 
v_newNode_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_834_, v_x_780_, v_x_781_);
v___x_836_ = ((size_t)7ULL);
v___x_837_ = lean_usize_dec_le(v___x_836_, v_x_779_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_835_);
v___x_839_ = lean_unsigned_to_nat(4u);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
if (v___x_840_ == 0)
{
lean_object* v_ks_841_; lean_object* v_vs_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_ks_841_ = lean_ctor_get(v_newNode_835_, 0);
lean_inc_ref(v_ks_841_);
v_vs_842_ = lean_ctor_get(v_newNode_835_, 1);
lean_inc_ref(v_vs_842_);
lean_dec_ref(v_newNode_835_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_779_, v_ks_841_, v_vs_842_, v___x_843_, v___x_844_);
lean_dec_ref(v_vs_842_);
lean_dec_ref(v_ks_841_);
return v___x_845_;
}
else
{
return v_newNode_835_;
}
}
else
{
return v_newNode_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_848_, lean_object* v_keys_849_, lean_object* v_vals_850_, lean_object* v_i_851_, lean_object* v_entries_852_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_array_get_size(v_keys_849_);
v___x_854_ = lean_nat_dec_lt(v_i_851_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v_i_851_);
return v_entries_852_;
}
else
{
lean_object* v_k_855_; lean_object* v_v_856_; uint64_t v___y_858_; 
v_k_855_ = lean_array_fget_borrowed(v_keys_849_, v_i_851_);
v_v_856_ = lean_array_fget_borrowed(v_vals_850_, v_i_851_);
if (lean_obj_tag(v_k_855_) == 0)
{
uint64_t v___x_869_; 
v___x_869_ = 1723ULL;
v___y_858_ = v___x_869_;
goto v___jp_857_;
}
else
{
uint64_t v_hash_870_; 
v_hash_870_ = lean_ctor_get_uint64(v_k_855_, sizeof(void*)*2);
v___y_858_ = v_hash_870_;
goto v___jp_857_;
}
v___jp_857_:
{
size_t v_h_859_; size_t v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v_h_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_h_859_ = lean_uint64_to_usize(v___y_858_);
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_sub(v_depth_848_, v___x_862_);
v___x_864_ = lean_usize_mul(v___x_860_, v___x_863_);
v_h_865_ = lean_usize_shift_right(v_h_859_, v___x_864_);
v___x_866_ = lean_nat_add(v_i_851_, v___x_861_);
lean_dec(v_i_851_);
lean_inc(v_v_856_);
lean_inc(v_k_855_);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_852_, v_h_865_, v_depth_848_, v_k_855_, v_v_856_);
v_i_851_ = v___x_866_;
v_entries_852_ = v___x_867_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_i_874_, lean_object* v_entries_875_){
_start:
{
size_t v_depth_boxed_876_; lean_object* v_res_877_; 
v_depth_boxed_876_ = lean_unbox_usize(v_depth_871_);
lean_dec(v_depth_871_);
v_res_877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_876_, v_keys_872_, v_vals_873_, v_i_874_, v_entries_875_);
lean_dec_ref(v_vals_873_);
lean_dec_ref(v_keys_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
size_t v_x_33772__boxed_883_; size_t v_x_33773__boxed_884_; lean_object* v_res_885_; 
v_x_33772__boxed_883_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_x_33773__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_878_, v_x_33772__boxed_883_, v_x_33773__boxed_884_, v_x_881_, v_x_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
uint64_t v___y_890_; 
if (lean_obj_tag(v_x_887_) == 0)
{
uint64_t v___x_894_; 
v___x_894_ = 1723ULL;
v___y_890_ = v___x_894_;
goto v___jp_889_;
}
else
{
uint64_t v_hash_895_; 
v_hash_895_ = lean_ctor_get_uint64(v_x_887_, sizeof(void*)*2);
v___y_890_ = v_hash_895_;
goto v___jp_889_;
}
v___jp_889_:
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_uint64_to_usize(v___y_890_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_886_, v___x_891_, v___x_892_, v_x_887_, v_x_888_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_896_, lean_object* v_vals_897_, lean_object* v_i_898_, lean_object* v_k_899_){
_start:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_keys_896_);
v___x_901_ = lean_nat_dec_lt(v_i_898_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v_i_898_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
lean_object* v_k_x27_903_; uint8_t v___x_904_; 
v_k_x27_903_ = lean_array_fget_borrowed(v_keys_896_, v_i_898_);
v___x_904_ = lean_name_eq(v_k_899_, v_k_x27_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_i_898_, v___x_905_);
lean_dec(v_i_898_);
v_i_898_ = v___x_906_;
goto _start;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_array_fget_borrowed(v_vals_897_, v_i_898_);
lean_dec(v_i_898_);
lean_inc(v___x_908_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_910_, v_vals_911_, v_i_912_, v_k_913_);
lean_dec(v_k_913_);
lean_dec_ref(v_vals_911_);
lean_dec_ref(v_keys_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_915_, size_t v_x_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_es_918_; lean_object* v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v_j_922_; lean_object* v___x_923_; 
v_es_918_ = lean_ctor_get(v_x_915_, 0);
v___x_919_ = lean_box(2);
v___x_920_ = ((size_t)31ULL);
v___x_921_ = lean_usize_land(v_x_916_, v___x_920_);
v_j_922_ = lean_usize_to_nat(v___x_921_);
v___x_923_ = lean_array_get_borrowed(v___x_919_, v_es_918_, v_j_922_);
lean_dec(v_j_922_);
switch(lean_obj_tag(v___x_923_))
{
case 0:
{
lean_object* v_key_924_; lean_object* v_val_925_; uint8_t v___x_926_; 
v_key_924_ = lean_ctor_get(v___x_923_, 0);
v_val_925_ = lean_ctor_get(v___x_923_, 1);
v___x_926_ = lean_name_eq(v_x_917_, v_key_924_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_box(0);
return v___x_927_;
}
else
{
lean_object* v___x_928_; 
lean_inc(v_val_925_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_val_925_);
return v___x_928_;
}
}
case 1:
{
lean_object* v_node_929_; size_t v___x_930_; size_t v___x_931_; 
v_node_929_ = lean_ctor_get(v___x_923_, 0);
v___x_930_ = ((size_t)5ULL);
v___x_931_ = lean_usize_shift_right(v_x_916_, v___x_930_);
v_x_915_ = v_node_929_;
v_x_916_ = v___x_931_;
goto _start;
}
default: 
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
}
}
else
{
lean_object* v_ks_934_; lean_object* v_vs_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_ks_934_ = lean_ctor_get(v_x_915_, 0);
v_vs_935_ = lean_ctor_get(v_x_915_, 1);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_934_, v_vs_935_, v___x_936_, v_x_917_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_33962__boxed_941_; lean_object* v_res_942_; 
v_x_33962__boxed_941_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_942_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_938_, v_x_33962__boxed_941_, v_x_940_);
lean_dec(v_x_940_);
lean_dec_ref(v_x_938_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint64_t v___y_946_; 
if (lean_obj_tag(v_x_944_) == 0)
{
uint64_t v___x_949_; 
v___x_949_ = 1723ULL;
v___y_946_ = v___x_949_;
goto v___jp_945_;
}
else
{
uint64_t v_hash_950_; 
v_hash_950_ = lean_ctor_get_uint64(v_x_944_, sizeof(void*)*2);
v___y_946_ = v_hash_950_;
goto v___jp_945_;
}
v___jp_945_:
{
size_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_uint64_to_usize(v___y_946_);
v___x_948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_943_, v___x_947_, v_x_944_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_951_, v_x_952_);
lean_dec(v_x_952_);
lean_dec_ref(v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_957_, lean_object* v_type_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_name_971_; lean_object* v___y_972_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v_name_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_961_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1193_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1193_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1193_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v_clean_1158_; 
v_clean_1158_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*18 + 16);
lean_dec(v_a_1133_);
if (v_clean_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_957_);
if (lean_obj_tag(v___x_1159_) == 1)
{
lean_object* v_val_1160_; lean_object* v___x_1162_; 
lean_dec_ref(v_type_958_);
lean_dec(v_name_957_);
v_val_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v___x_1159_, 1);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_val_1160_);
v___x_1162_ = v___x_1135_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_val_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
uint8_t v___x_1164_; 
lean_dec(v___x_1159_);
v___x_1164_ = l_Lean_Name_hasMacroScopes(v_name_957_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_del_object(v___x_1135_);
lean_dec_ref(v_type_958_);
v___x_1165_ = l_Lean_Core_mkFreshUserName(v_name_957_, v_a_967_, v_a_968_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = l_Lean_Name_eraseMacroScopes(v_name_957_);
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_1168_ = lean_name_eq(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_1170_ = lean_name_eq(v___x_1166_, v___x_1169_);
lean_dec(v___x_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v_type_958_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_name_957_);
v___x_1172_ = v___x_1135_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_name_957_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
else
{
lean_del_object(v___x_1135_);
goto v___jp_1137_;
}
}
else
{
lean_dec(v___x_1166_);
lean_del_object(v___x_1135_);
goto v___jp_1137_;
}
}
}
}
else
{
uint8_t v___x_1174_; 
lean_del_object(v___x_1135_);
v___x_1174_ = l_Lean_Name_hasMacroScopes(v_name_957_);
if (v___x_1174_ == 0)
{
v_name_1107_ = v_name_957_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1175_ = l_Lean_Name_eraseMacroScopes(v_name_957_);
lean_dec(v_name_957_);
v___x_1189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_1190_ = lean_name_eq(v___x_1175_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_1192_ = lean_name_eq(v___x_1175_, v___x_1191_);
if (v___x_1192_ == 0)
{
v_name_1107_ = v___x_1175_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
goto v___jp_1176_;
}
}
else
{
goto v___jp_1176_;
}
v___jp_1176_:
{
lean_object* v___x_1177_; 
lean_inc_ref(v_type_958_);
v___x_1177_ = l_Lean_Meta_isProp(v_type_958_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___x_1179_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1179_ == 0)
{
v_name_1107_ = v___x_1175_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___x_1175_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_1107_ = v___x_1180_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___x_1175_);
lean_dec_ref(v_type_958_);
v_a_1181_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1177_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_isProp(v_type_958_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_unbox(v_a_1139_);
lean_dec(v_a_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1145_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_name_957_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_name_957_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1141_);
lean_dec(v_name_957_);
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_1148_ = l_Lean_Core_mkFreshUserName(v___x_1147_, v_a_967_, v_a_968_);
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_name_957_);
v_a_1150_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1138_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1138_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_type_958_);
lean_dec(v_name_957_);
v_a_1194_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1132_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1132_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
v___jp_970_:
{
lean_object* v___x_973_; lean_object* v_toGoalState_974_; lean_object* v_clean_975_; lean_object* v_mvarId_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1025_; 
v___x_973_ = lean_st_ref_take(v___y_972_);
v_toGoalState_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_toGoalState_974_);
v_clean_975_ = lean_ctor_get(v_toGoalState_974_, 16);
lean_inc_ref(v_clean_975_);
v_mvarId_976_ = lean_ctor_get(v___x_973_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_1026_);
v___x_978_ = v___x_973_;
v_isShared_979_ = v_isSharedCheck_1025_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_mvarId_976_);
lean_dec(v___x_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1025_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_nextDeclIdx_980_; lean_object* v_enodeMap_981_; lean_object* v_exprs_982_; lean_object* v_parents_983_; lean_object* v_congrTable_984_; lean_object* v_appMap_985_; lean_object* v_indicesFound_986_; lean_object* v_toProcess_987_; lean_object* v_internalizing_988_; uint8_t v_inconsistent_989_; lean_object* v_nextIdx_990_; lean_object* v_newRawFacts_991_; lean_object* v_facts_992_; lean_object* v_extThms_993_; lean_object* v_ematch_994_; lean_object* v_inj_995_; lean_object* v_split_996_; lean_object* v_sstates_997_; lean_object* v_goalStack_998_; uint64_t v_introBase_999_; lean_object* v_numIntros_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1023_; 
v_nextDeclIdx_980_ = lean_ctor_get(v_toGoalState_974_, 0);
v_enodeMap_981_ = lean_ctor_get(v_toGoalState_974_, 1);
v_exprs_982_ = lean_ctor_get(v_toGoalState_974_, 2);
v_parents_983_ = lean_ctor_get(v_toGoalState_974_, 3);
v_congrTable_984_ = lean_ctor_get(v_toGoalState_974_, 4);
v_appMap_985_ = lean_ctor_get(v_toGoalState_974_, 5);
v_indicesFound_986_ = lean_ctor_get(v_toGoalState_974_, 6);
v_toProcess_987_ = lean_ctor_get(v_toGoalState_974_, 7);
v_internalizing_988_ = lean_ctor_get(v_toGoalState_974_, 8);
v_inconsistent_989_ = lean_ctor_get_uint8(v_toGoalState_974_, sizeof(void*)*20 + 8);
v_nextIdx_990_ = lean_ctor_get(v_toGoalState_974_, 9);
v_newRawFacts_991_ = lean_ctor_get(v_toGoalState_974_, 10);
v_facts_992_ = lean_ctor_get(v_toGoalState_974_, 11);
v_extThms_993_ = lean_ctor_get(v_toGoalState_974_, 12);
v_ematch_994_ = lean_ctor_get(v_toGoalState_974_, 13);
v_inj_995_ = lean_ctor_get(v_toGoalState_974_, 14);
v_split_996_ = lean_ctor_get(v_toGoalState_974_, 15);
v_sstates_997_ = lean_ctor_get(v_toGoalState_974_, 17);
v_goalStack_998_ = lean_ctor_get(v_toGoalState_974_, 18);
v_introBase_999_ = lean_ctor_get_uint64(v_toGoalState_974_, sizeof(void*)*20);
v_numIntros_1000_ = lean_ctor_get(v_toGoalState_974_, 19);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_toGoalState_974_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v_toGoalState_974_, 16);
lean_dec(v_unused_1024_);
v___x_1002_ = v_toGoalState_974_;
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_numIntros_1000_);
lean_inc(v_goalStack_998_);
lean_inc(v_sstates_997_);
lean_inc(v_split_996_);
lean_inc(v_inj_995_);
lean_inc(v_ematch_994_);
lean_inc(v_extThms_993_);
lean_inc(v_facts_992_);
lean_inc(v_newRawFacts_991_);
lean_inc(v_nextIdx_990_);
lean_inc(v_internalizing_988_);
lean_inc(v_toProcess_987_);
lean_inc(v_indicesFound_986_);
lean_inc(v_appMap_985_);
lean_inc(v_congrTable_984_);
lean_inc(v_parents_983_);
lean_inc(v_exprs_982_);
lean_inc(v_enodeMap_981_);
lean_inc(v_nextDeclIdx_980_);
lean_dec(v_toGoalState_974_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_used_1004_; lean_object* v_next_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1022_; 
v_used_1004_ = lean_ctor_get(v_clean_975_, 0);
v_next_1005_ = lean_ctor_get(v_clean_975_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_clean_975_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1007_ = v_clean_975_;
v_isShared_1008_ = v_isSharedCheck_1022_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_next_1005_);
lean_inc(v_used_1004_);
lean_dec(v_clean_975_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1022_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_box(0);
lean_inc(v_name_971_);
v___x_1010_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_1004_, v_name_971_, v___x_1009_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_next_1005_);
v___x_1012_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 16, v___x_1012_);
v___x_1014_ = v___x_1002_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_nextDeclIdx_980_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_enodeMap_981_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_exprs_982_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_parents_983_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_congrTable_984_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_appMap_985_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_indicesFound_986_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_toProcess_987_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_internalizing_988_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_nextIdx_990_);
lean_ctor_set(v_reuseFailAlloc_1020_, 10, v_newRawFacts_991_);
lean_ctor_set(v_reuseFailAlloc_1020_, 11, v_facts_992_);
lean_ctor_set(v_reuseFailAlloc_1020_, 12, v_extThms_993_);
lean_ctor_set(v_reuseFailAlloc_1020_, 13, v_ematch_994_);
lean_ctor_set(v_reuseFailAlloc_1020_, 14, v_inj_995_);
lean_ctor_set(v_reuseFailAlloc_1020_, 15, v_split_996_);
lean_ctor_set(v_reuseFailAlloc_1020_, 16, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 17, v_sstates_997_);
lean_ctor_set(v_reuseFailAlloc_1020_, 18, v_goalStack_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 19, v_numIntros_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*20 + 8, v_inconsistent_989_);
lean_ctor_set_uint64(v_reuseFailAlloc_1020_, sizeof(void*)*20, v_introBase_999_);
v___x_1014_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1014_);
v___x_1016_ = v___x_978_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_mvarId_976_);
v___x_1016_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_st_ref_put(v___y_972_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_name_971_);
return v___x_1018_;
}
}
}
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1036_);
lean_ctor_set(v___x_1041_, 1, v___y_1040_);
lean_inc(v___y_1033_);
v___x_1042_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_1033_, v___x_1041_, v___y_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1046_; lean_object* v_toGoalState_1047_; lean_object* v_clean_1048_; lean_object* v_mvarId_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1096_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_fst_1044_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_fst_1044_);
v_snd_1045_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_snd_1045_);
lean_dec(v_a_1043_);
v___x_1046_ = lean_st_ref_take(v___y_1039_);
v_toGoalState_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_toGoalState_1047_);
v_clean_1048_ = lean_ctor_get(v_toGoalState_1047_, 16);
lean_inc_ref(v_clean_1048_);
v_mvarId_1049_ = lean_ctor_get(v___x_1046_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1046_, 0);
lean_dec(v_unused_1097_);
v___x_1051_ = v___x_1046_;
v_isShared_1052_ = v_isSharedCheck_1096_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_mvarId_1049_);
lean_dec(v___x_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1096_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_nextDeclIdx_1053_; lean_object* v_enodeMap_1054_; lean_object* v_exprs_1055_; lean_object* v_parents_1056_; lean_object* v_congrTable_1057_; lean_object* v_appMap_1058_; lean_object* v_indicesFound_1059_; lean_object* v_toProcess_1060_; lean_object* v_internalizing_1061_; uint8_t v_inconsistent_1062_; lean_object* v_nextIdx_1063_; lean_object* v_newRawFacts_1064_; lean_object* v_facts_1065_; lean_object* v_extThms_1066_; lean_object* v_ematch_1067_; lean_object* v_inj_1068_; lean_object* v_split_1069_; lean_object* v_sstates_1070_; lean_object* v_goalStack_1071_; uint64_t v_introBase_1072_; lean_object* v_numIntros_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1094_; 
v_nextDeclIdx_1053_ = lean_ctor_get(v_toGoalState_1047_, 0);
v_enodeMap_1054_ = lean_ctor_get(v_toGoalState_1047_, 1);
v_exprs_1055_ = lean_ctor_get(v_toGoalState_1047_, 2);
v_parents_1056_ = lean_ctor_get(v_toGoalState_1047_, 3);
v_congrTable_1057_ = lean_ctor_get(v_toGoalState_1047_, 4);
v_appMap_1058_ = lean_ctor_get(v_toGoalState_1047_, 5);
v_indicesFound_1059_ = lean_ctor_get(v_toGoalState_1047_, 6);
v_toProcess_1060_ = lean_ctor_get(v_toGoalState_1047_, 7);
v_internalizing_1061_ = lean_ctor_get(v_toGoalState_1047_, 8);
v_inconsistent_1062_ = lean_ctor_get_uint8(v_toGoalState_1047_, sizeof(void*)*20 + 8);
v_nextIdx_1063_ = lean_ctor_get(v_toGoalState_1047_, 9);
v_newRawFacts_1064_ = lean_ctor_get(v_toGoalState_1047_, 10);
v_facts_1065_ = lean_ctor_get(v_toGoalState_1047_, 11);
v_extThms_1066_ = lean_ctor_get(v_toGoalState_1047_, 12);
v_ematch_1067_ = lean_ctor_get(v_toGoalState_1047_, 13);
v_inj_1068_ = lean_ctor_get(v_toGoalState_1047_, 14);
v_split_1069_ = lean_ctor_get(v_toGoalState_1047_, 15);
v_sstates_1070_ = lean_ctor_get(v_toGoalState_1047_, 17);
v_goalStack_1071_ = lean_ctor_get(v_toGoalState_1047_, 18);
v_introBase_1072_ = lean_ctor_get_uint64(v_toGoalState_1047_, sizeof(void*)*20);
v_numIntros_1073_ = lean_ctor_get(v_toGoalState_1047_, 19);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_toGoalState_1047_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_toGoalState_1047_, 16);
lean_dec(v_unused_1095_);
v___x_1075_ = v_toGoalState_1047_;
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_numIntros_1073_);
lean_inc(v_goalStack_1071_);
lean_inc(v_sstates_1070_);
lean_inc(v_split_1069_);
lean_inc(v_inj_1068_);
lean_inc(v_ematch_1067_);
lean_inc(v_extThms_1066_);
lean_inc(v_facts_1065_);
lean_inc(v_newRawFacts_1064_);
lean_inc(v_nextIdx_1063_);
lean_inc(v_internalizing_1061_);
lean_inc(v_toProcess_1060_);
lean_inc(v_indicesFound_1059_);
lean_inc(v_appMap_1058_);
lean_inc(v_congrTable_1057_);
lean_inc(v_parents_1056_);
lean_inc(v_exprs_1055_);
lean_inc(v_enodeMap_1054_);
lean_inc(v_nextDeclIdx_1053_);
lean_dec(v_toGoalState_1047_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_used_1077_; lean_object* v_next_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1093_; 
v_used_1077_ = lean_ctor_get(v_clean_1048_, 0);
v_next_1078_ = lean_ctor_get(v_clean_1048_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_clean_1048_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1080_ = v_clean_1048_;
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_next_1078_);
lean_inc(v_used_1077_);
lean_dec(v_clean_1048_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_1078_, v___y_1033_, v_snd_1045_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_used_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 16, v___x_1084_);
v___x_1086_ = v___x_1075_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_nextDeclIdx_1053_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_enodeMap_1054_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_exprs_1055_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_parents_1056_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_congrTable_1057_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_appMap_1058_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v_indicesFound_1059_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_toProcess_1060_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_internalizing_1061_);
lean_ctor_set(v_reuseFailAlloc_1091_, 9, v_nextIdx_1063_);
lean_ctor_set(v_reuseFailAlloc_1091_, 10, v_newRawFacts_1064_);
lean_ctor_set(v_reuseFailAlloc_1091_, 11, v_facts_1065_);
lean_ctor_set(v_reuseFailAlloc_1091_, 12, v_extThms_1066_);
lean_ctor_set(v_reuseFailAlloc_1091_, 13, v_ematch_1067_);
lean_ctor_set(v_reuseFailAlloc_1091_, 14, v_inj_1068_);
lean_ctor_set(v_reuseFailAlloc_1091_, 15, v_split_1069_);
lean_ctor_set(v_reuseFailAlloc_1091_, 16, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1091_, 17, v_sstates_1070_);
lean_ctor_set(v_reuseFailAlloc_1091_, 18, v_goalStack_1071_);
lean_ctor_set(v_reuseFailAlloc_1091_, 19, v_numIntros_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*20 + 8, v_inconsistent_1062_);
lean_ctor_set_uint64(v_reuseFailAlloc_1091_, sizeof(void*)*20, v_introBase_1072_);
v___x_1086_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1086_);
v___x_1088_ = v___x_1051_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_mvarId_1049_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_st_ref_put(v___y_1039_, v___x_1088_);
v_name_971_ = v_fst_1044_;
v___y_972_ = v___y_1039_;
goto v___jp_970_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v___y_1033_);
v_a_1098_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1042_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1042_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1118_; lean_object* v_toGoalState_1119_; lean_object* v_clean_1120_; lean_object* v_used_1121_; uint8_t v___x_1122_; 
v___x_1118_ = lean_st_ref_get(v___y_1108_);
v_toGoalState_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_toGoalState_1119_);
lean_dec(v___x_1118_);
v_clean_1120_ = lean_ctor_get(v_toGoalState_1119_, 16);
lean_inc_ref(v_clean_1120_);
lean_dec_ref(v_toGoalState_1119_);
v_used_1121_ = lean_ctor_get(v_clean_1120_, 0);
lean_inc_ref(v_used_1121_);
lean_dec_ref(v_clean_1120_);
v___x_1122_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_1121_, v_name_1107_);
lean_dec_ref(v_used_1121_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v_type_958_);
v_name_971_ = v_name_1107_;
v___y_972_ = v___y_1108_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1123_; 
lean_inc(v_name_1107_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_1107_, v_type_958_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v_toGoalState_1126_; lean_object* v_clean_1127_; lean_object* v_next_1128_; lean_object* v___x_1129_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_st_ref_get(v___y_1108_);
v_toGoalState_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_toGoalState_1126_);
lean_dec(v___x_1125_);
v_clean_1127_ = lean_ctor_get(v_toGoalState_1126_, 16);
lean_inc_ref(v_clean_1127_);
lean_dec_ref(v_toGoalState_1126_);
v_next_1128_ = lean_ctor_get(v_clean_1127_, 1);
lean_inc_ref(v_next_1128_);
lean_dec_ref(v_clean_1127_);
v___x_1129_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_1128_, v_a_1124_);
lean_dec_ref(v_next_1128_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___y_1028_ = v___y_1109_;
v___y_1029_ = v___y_1115_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1110_;
v___y_1032_ = v___y_1112_;
v___y_1033_ = v_a_1124_;
v___y_1034_ = v___y_1111_;
v___y_1035_ = v___y_1114_;
v___y_1036_ = v_name_1107_;
v___y_1037_ = v___y_1113_;
v___y_1038_ = v___y_1117_;
v___y_1039_ = v___y_1108_;
v___y_1040_ = v_val_1130_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1131_; 
lean_dec(v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___y_1028_ = v___y_1109_;
v___y_1029_ = v___y_1115_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1110_;
v___y_1032_ = v___y_1112_;
v___y_1033_ = v_a_1124_;
v___y_1034_ = v___y_1111_;
v___y_1035_ = v___y_1114_;
v___y_1036_ = v_name_1107_;
v___y_1037_ = v___y_1113_;
v___y_1038_ = v___y_1117_;
v___y_1039_ = v___y_1108_;
v___y_1040_ = v___x_1131_;
goto v___jp_1027_;
}
}
else
{
lean_dec(v_name_1107_);
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_1202_, lean_object* v_type_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_1202_, v_type_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_1217_, v_x_1218_, v_x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_1222_, v_x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_1225_, v_x_1226_, v_x_1227_);
lean_dec(v_x_1227_);
lean_dec_ref(v_x_1226_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_1230_, lean_object* v_inst_1231_, lean_object* v_a_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_1230_, v_a_1232_, v___y_1233_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_1245_, lean_object* v_inst_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_1245_, v_inst_1246_, v_a_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_1264_, v_x_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, size_t v_x_1270_, size_t v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_1269_, v_x_1270_, v_x_1271_, v_x_1272_, v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
size_t v_x_34456__boxed_1281_; size_t v_x_34457__boxed_1282_; lean_object* v_res_1283_; 
v_x_34456__boxed_1281_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_x_34457__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_1275_, v_x_1276_, v_x_34456__boxed_1281_, v_x_34457__boxed_1282_, v_x_1279_, v_x_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, size_t v_x_1286_, lean_object* v_x_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_1285_, v_x_1286_, v_x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
size_t v_x_34473__boxed_1293_; uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_x_34473__boxed_1293_ = lean_unbox_usize(v_x_1291_);
lean_dec(v_x_1291_);
v_res_1294_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_1289_, v_x_1290_, v_x_34473__boxed_1293_, v_x_1292_);
lean_dec(v_x_1292_);
lean_dec_ref(v_x_1290_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, size_t v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_1297_, v_x_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
size_t v_x_34484__boxed_1305_; lean_object* v_res_1306_; 
v_x_34484__boxed_1305_ = lean_unbox_usize(v_x_1303_);
lean_dec(v_x_1303_);
v_res_1306_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_1301_, v_x_1302_, v_x_34484__boxed_1305_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec_ref(v_x_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1307_, lean_object* v_n_1308_, lean_object* v_k_1309_, lean_object* v_v_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_1308_, v_k_1309_, v_v_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1312_, size_t v_depth_1313_, lean_object* v_keys_1314_, lean_object* v_vals_1315_, lean_object* v_heq_1316_, lean_object* v_i_1317_, lean_object* v_entries_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_1313_, v_keys_1314_, v_vals_1315_, v_i_1317_, v_entries_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1320_, lean_object* v_depth_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_heq_1324_, lean_object* v_i_1325_, lean_object* v_entries_1326_){
_start:
{
size_t v_depth_boxed_1327_; lean_object* v_res_1328_; 
v_depth_boxed_1327_ = lean_unbox_usize(v_depth_1321_);
lean_dec(v_depth_1321_);
v_res_1328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_1320_, v_depth_boxed_1327_, v_keys_1322_, v_vals_1323_, v_heq_1324_, v_i_1325_, v_entries_1326_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1329_, lean_object* v_keys_1330_, lean_object* v_vals_1331_, lean_object* v_heq_1332_, lean_object* v_i_1333_, lean_object* v_k_1334_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_1330_, v_i_1333_, v_k_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1336_, lean_object* v_keys_1337_, lean_object* v_vals_1338_, lean_object* v_heq_1339_, lean_object* v_i_1340_, lean_object* v_k_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_1336_, v_keys_1337_, v_vals_1338_, v_heq_1339_, v_i_1340_, v_k_1341_);
lean_dec(v_k_1341_);
lean_dec_ref(v_vals_1338_);
lean_dec_ref(v_keys_1337_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_1345_, v_vals_1346_, v_i_1348_, v_k_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1351_, lean_object* v_keys_1352_, lean_object* v_vals_1353_, lean_object* v_heq_1354_, lean_object* v_i_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_1351_, v_keys_1352_, v_vals_1353_, v_heq_1354_, v_i_1355_, v_k_1356_);
lean_dec(v_k_1356_);
lean_dec_ref(v_vals_1353_);
lean_dec_ref(v_keys_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1359_, v_x_1360_, v_x_1361_, v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_env_1371_; uint8_t v___x_1372_; lean_object* v_env_1373_; lean_object* v___x_1374_; lean_object* v_toCold_1375_; lean_object* v_mctx_1376_; lean_object* v_lctx_1377_; lean_object* v_options_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = 0;
v_env_1373_ = l_Lean_Environment_setRecordingDeps(v_env_1371_, v___x_1372_);
v___x_1374_ = lean_st_ref_get(v___y_1366_);
v_toCold_1375_ = lean_ctor_get(v___y_1367_, 0);
v_mctx_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_mctx_1376_);
lean_dec(v___x_1374_);
v_lctx_1377_ = lean_ctor_get(v___y_1365_, 2);
v_options_1378_ = lean_ctor_get(v_toCold_1375_, 2);
lean_inc_ref(v_options_1378_);
lean_inc_ref(v_lctx_1377_);
v___x_1379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1379_, 0, v_env_1373_);
lean_ctor_set(v___x_1379_, 1, v_mctx_1376_);
lean_ctor_set(v___x_1379_, 2, v_lctx_1377_);
lean_ctor_set(v___x_1379_, 3, v_options_1378_);
v___x_1380_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v_msgData_1364_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_ref_1395_; lean_object* v___x_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1405_; 
v_ref_1395_ = lean_ctor_get(v___y_1392_, 2);
v___x_1396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_inc(v_ref_1395_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_ref_1395_);
lean_ctor_set(v___x_1401_, 1, v_a_1397_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 1);
lean_ctor_set(v___x_1399_, 0, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___x_1492_; lean_object* v_mvarId_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_st_ref_get(v_a_1416_);
v_mvarId_1493_ = lean_ctor_get(v___x_1492_, 1);
lean_inc(v_mvarId_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = l_Lean_MVarId_getType(v_mvarId_1493_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
switch(lean_obj_tag(v_a_1495_))
{
case 7:
{
lean_object* v_binderName_1496_; lean_object* v_binderType_1497_; 
v_binderName_1496_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_binderName_1496_);
v_binderType_1497_ = lean_ctor_get(v_a_1495_, 1);
lean_inc_ref(v_binderType_1497_);
lean_dec_ref_known(v_a_1495_, 3);
v_fst_1428_ = v_binderName_1496_;
v_snd_1429_ = v_binderType_1497_;
v___y_1430_ = v_a_1416_;
v___y_1431_ = v_a_1417_;
v___y_1432_ = v_a_1418_;
v___y_1433_ = v_a_1419_;
v___y_1434_ = v_a_1420_;
v___y_1435_ = v_a_1421_;
v___y_1436_ = v_a_1422_;
v___y_1437_ = v_a_1423_;
v___y_1438_ = v_a_1424_;
v___y_1439_ = v_a_1425_;
goto v___jp_1427_;
}
case 8:
{
lean_object* v_declName_1498_; lean_object* v_type_1499_; 
v_declName_1498_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_declName_1498_);
v_type_1499_ = lean_ctor_get(v_a_1495_, 1);
lean_inc_ref(v_type_1499_);
lean_dec_ref_known(v_a_1495_, 4);
v_fst_1428_ = v_declName_1498_;
v_snd_1429_ = v_type_1499_;
v___y_1430_ = v_a_1416_;
v___y_1431_ = v_a_1417_;
v___y_1432_ = v_a_1418_;
v___y_1433_ = v_a_1419_;
v___y_1434_ = v_a_1420_;
v___y_1435_ = v_a_1421_;
v___y_1436_ = v_a_1422_;
v___y_1437_ = v_a_1423_;
v___y_1438_ = v_a_1424_;
v___y_1439_ = v_a_1425_;
goto v___jp_1427_;
}
default: 
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1495_);
v___x_1500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1501_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1500_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1494_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1494_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
v___jp_1427_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1428_, v_snd_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v_mvarId_1443_; lean_object* v___x_1444_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_st_ref_get(v___y_1430_);
v_mvarId_1443_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_mvarId_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_MVarId_intro(v_mvarId_1443_, v_a_1441_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; lean_object* v_toGoalState_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1474_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_fst_1446_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_fst_1446_);
v_snd_1447_ = lean_ctor_get(v_a_1445_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_a_1445_);
v___x_1448_ = lean_st_ref_take(v___y_1430_);
v_toGoalState_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1448_, 1);
lean_dec(v_unused_1475_);
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_toGoalState_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_snd_1447_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_toGoalState_1449_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_snd_1447_);
v___x_1454_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_st_ref_put(v___y_1430_, v___x_1454_);
lean_inc(v_fst_1446_);
v___x_1456_ = l_Lean_Meta_Grind_registerFVarAnchor___redArg(v_fst_1446_, v___y_1430_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1456_, 0);
lean_dec(v_unused_1464_);
v___x_1458_ = v___x_1456_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v___x_1456_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v_fst_1446_);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_fst_1446_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_fst_1446_);
v_a_1465_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
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
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1444_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1444_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1440_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1440_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec(v_a_1518_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1531_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
lean_inc(v___y_1564_);
lean_inc_ref(v___y_1563_);
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
lean_inc(v___y_1560_);
lean_inc(v___y_1559_);
v___x_1570_ = lean_apply_11(v_x_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, lean_box(0));
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___f_1597_; lean_object* v___x_1598_; 
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc(v___y_1586_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1597_, 0, v_x_1585_);
lean_closure_set(v___f_1597_, 1, v___y_1586_);
lean_closure_set(v___f_1597_, 2, v___y_1587_);
lean_closure_set(v___f_1597_, 3, v___y_1588_);
lean_closure_set(v___f_1597_, 4, v___y_1589_);
lean_closure_set(v___f_1597_, 5, v___y_1590_);
lean_closure_set(v___f_1597_, 6, v___y_1591_);
v___x_1598_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1584_, v___f_1597_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1598_) == 0)
{
return v___x_1598_;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1607_, v_x_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec(v___y_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1621_, lean_object* v_mvarId_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1636_, lean_object* v_mvarId_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1636_, v_mvarId_1637_, v_x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v___y_1639_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
v___x_1662_ = lean_apply_10(v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; 
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1687_, 0, v_x_1676_);
lean_closure_set(v___f_1687_, 1, v___y_1677_);
lean_closure_set(v___f_1687_, 2, v___y_1678_);
lean_closure_set(v___f_1687_, 3, v___y_1679_);
lean_closure_set(v___f_1687_, 4, v___y_1680_);
lean_closure_set(v___f_1687_, 5, v___y_1681_);
v___x_1688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1675_, v___f_1687_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1710_, lean_object* v_mvarId_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1711_, v_x_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_mvarId_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1724_, v_mvarId_1725_, v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1738_, lean_object* v_generation_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
lean_inc(v_a_1738_);
v___x_1751_ = l_Lean_FVarId_getDecl___redArg(v_a_1738_, v___y_1746_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = l_Lean_LocalDecl_type(v_a_1752_);
lean_dec(v_a_1752_);
lean_inc_ref(v___x_1753_);
v___x_1754_ = l_Lean_Meta_isProp(v___x_1753_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; uint8_t v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = lean_unbox(v_a_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v___x_1753_);
lean_inc(v_a_1738_);
v___x_1757_ = l_Lean_FVarId_getDecl___redArg(v_a_1738_, v___y_1746_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unbox(v_a_1755_);
lean_dec(v_a_1755_);
v___x_1760_ = l_Lean_LocalDecl_value(v_a_1758_, v___x_1759_);
lean_dec(v_a_1758_);
v___x_1761_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1760_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
lean_inc(v_a_1738_);
v___x_1763_ = l_Lean_mkFVar(v_a_1738_);
v___x_1764_ = l_Lean_Meta_Sym_shareCommon(v___x_1763_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
lean_inc(v_a_1762_);
v___x_1766_ = l_Lean_Meta_Simp_Result_getProof(v_a_1762_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_expr_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_expr_1768_ = lean_ctor_get(v_a_1762_, 0);
lean_inc_ref(v_expr_1768_);
lean_dec(v_a_1762_);
v___x_1769_ = l_Lean_Meta_Grind_addNewEq(v_a_1765_, v_expr_1768_, v_a_1767_, v_generation_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1778_; 
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1769_, 0);
lean_dec(v_unused_1779_);
v___x_1771_ = v___x_1769_;
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1769_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_st_ref_get(v___y_1740_);
v___x_1774_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_a_1738_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_a_1738_);
v_a_1780_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1769_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1769_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1765_);
lean_dec(v_a_1762_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1788_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1766_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1766_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_a_1762_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1796_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1764_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1764_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1804_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1761_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1761_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1755_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1812_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1757_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1757_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v_a_1755_);
lean_dec(v_generation_1739_);
v___x_1820_ = lean_st_ref_get(v___y_1740_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1753_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1821_, v___x_1753_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_mvarId_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_mvarId_1824_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_mvarId_1824_);
lean_dec(v___x_1820_);
v___x_1825_ = l_Lean_mkFVar(v_a_1738_);
v___x_1826_ = l_Lean_MVarId_assert(v_mvarId_1824_, v_a_1823_, v___x_1753_, v___x_1825_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1845_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v_toGoalState_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1843_; 
v___x_1831_ = lean_st_ref_get(v___y_1740_);
v_toGoalState_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v___x_1831_, 1);
lean_dec(v_unused_1844_);
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_toGoalState_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_a_1827_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_toGoalState_1832_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1827_);
v___x_1837_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1838_);
v___x_1840_ = v___x_1829_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1826_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1826_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v___x_1820_);
lean_dec_ref(v___x_1753_);
lean_dec(v_a_1738_);
v_a_1854_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1822_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1822_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___x_1753_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1862_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1754_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1754_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1870_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1751_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1751_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1878_, lean_object* v_generation_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1878_, v_generation_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v_ks_1896_; lean_object* v_vs_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1921_; 
v_ks_1896_ = lean_ctor_get(v_x_1892_, 0);
v_vs_1897_ = lean_ctor_get(v_x_1892_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1892_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1899_ = v_x_1892_;
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_vs_1897_);
lean_inc(v_ks_1896_);
lean_dec(v_x_1892_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = lean_array_get_size(v_ks_1896_);
v___x_1902_ = lean_nat_dec_lt(v_x_1893_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_x_1893_);
v___x_1903_ = lean_array_push(v_ks_1896_, v_x_1894_);
v___x_1904_ = lean_array_push(v_vs_1897_, v_x_1895_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1904_);
lean_ctor_set(v___x_1899_, 0, v___x_1903_);
v___x_1906_ = v___x_1899_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v_k_x27_1908_; uint8_t v___x_1909_; 
v_k_x27_1908_ = lean_array_fget_borrowed(v_ks_1896_, v_x_1893_);
v___x_1909_ = l_Lean_instBEqMVarId_beq(v_x_1894_, v_k_x27_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1911_; 
if (v_isShared_1900_ == 0)
{
v___x_1911_ = v___x_1899_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_ks_1896_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_vs_1897_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_add(v_x_1893_, v___x_1912_);
lean_dec(v_x_1893_);
v_x_1892_ = v___x_1911_;
v_x_1893_ = v___x_1913_;
goto _start;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1916_ = lean_array_fset(v_ks_1896_, v_x_1893_, v_x_1894_);
v___x_1917_ = lean_array_fset(v_vs_1897_, v_x_1893_, v_x_1895_);
lean_dec(v_x_1893_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1917_);
lean_ctor_set(v___x_1899_, 0, v___x_1916_);
v___x_1919_ = v___x_1899_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1922_, lean_object* v_k_1923_, lean_object* v_v_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1922_, v___x_1925_, v_k_1923_, v_v_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1927_, size_t v_x_1928_, size_t v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v_es_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v_j_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_es_1932_ = lean_ctor_get(v_x_1927_, 0);
v___x_1933_ = ((size_t)31ULL);
v___x_1934_ = lean_usize_land(v_x_1928_, v___x_1933_);
v_j_1935_ = lean_usize_to_nat(v___x_1934_);
v___x_1936_ = lean_array_get_size(v_es_1932_);
v___x_1937_ = lean_nat_dec_lt(v_j_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_dec(v_j_1935_);
lean_dec(v_x_1931_);
lean_dec(v_x_1930_);
return v_x_1927_;
}
else
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1976_; 
lean_inc_ref(v_es_1932_);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_x_1927_, 0);
lean_dec(v_unused_1977_);
v___x_1939_ = v_x_1927_;
v_isShared_1940_ = v_isSharedCheck_1976_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v_x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1976_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_v_1941_; lean_object* v___x_1942_; lean_object* v_xs_x27_1943_; lean_object* v___y_1945_; 
v_v_1941_ = lean_array_fget(v_es_1932_, v_j_1935_);
v___x_1942_ = lean_box(0);
v_xs_x27_1943_ = lean_array_fset(v_es_1932_, v_j_1935_, v___x_1942_);
switch(lean_obj_tag(v_v_1941_))
{
case 0:
{
lean_object* v_key_1950_; lean_object* v_val_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1961_; 
v_key_1950_ = lean_ctor_get(v_v_1941_, 0);
v_val_1951_ = lean_ctor_get(v_v_1941_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_v_1941_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1953_ = v_v_1941_;
v_isShared_1954_ = v_isSharedCheck_1961_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_val_1951_);
lean_inc(v_key_1950_);
lean_dec(v_v_1941_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1961_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_instBEqMVarId_beq(v_x_1930_, v_key_1950_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_del_object(v___x_1953_);
v___x_1956_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1950_, v_val_1951_, v_x_1930_, v_x_1931_);
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
v___y_1945_ = v___x_1957_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_val_1951_);
lean_dec(v_key_1950_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_x_1931_);
lean_ctor_set(v___x_1953_, 0, v_x_1930_);
v___x_1959_ = v___x_1953_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_x_1930_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_x_1931_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1945_ = v___x_1959_;
goto v___jp_1944_;
}
}
}
}
case 1:
{
lean_object* v_node_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_node_1962_ = lean_ctor_get(v_v_1941_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_v_1941_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1964_ = v_v_1941_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_node_1962_);
lean_dec(v_v_1941_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
size_t v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1966_ = ((size_t)5ULL);
v___x_1967_ = lean_usize_shift_right(v_x_1928_, v___x_1966_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_x_1929_, v___x_1968_);
v___x_1970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1962_, v___x_1967_, v___x_1969_, v_x_1930_, v_x_1931_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1970_);
v___x_1972_ = v___x_1964_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1945_ = v___x_1972_;
goto v___jp_1944_;
}
}
}
default: 
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_x_1930_);
lean_ctor_set(v___x_1975_, 1, v_x_1931_);
v___y_1945_ = v___x_1975_;
goto v___jp_1944_;
}
}
v___jp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_array_fset(v_xs_x27_1943_, v_j_1935_, v___y_1945_);
lean_dec(v_j_1935_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1946_);
v___x_1948_ = v___x_1939_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_object* v_ks_1978_; lean_object* v_vs_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1997_; 
v_ks_1978_ = lean_ctor_get(v_x_1927_, 0);
v_vs_1979_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1981_ = v_x_1927_;
v_isShared_1982_ = v_isSharedCheck_1997_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_vs_1979_);
lean_inc(v_ks_1978_);
lean_dec(v_x_1927_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1997_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_ks_1978_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_vs_1979_);
v___x_1984_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v_newNode_1985_; size_t v___x_1986_; uint8_t v___x_1987_; 
v_newNode_1985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1984_, v_x_1930_, v_x_1931_);
v___x_1986_ = ((size_t)7ULL);
v___x_1987_ = lean_usize_dec_le(v___x_1986_, v_x_1929_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1985_);
v___x_1989_ = lean_unsigned_to_nat(4u);
v___x_1990_ = lean_nat_dec_lt(v___x_1988_, v___x_1989_);
lean_dec(v___x_1988_);
if (v___x_1990_ == 0)
{
lean_object* v_ks_1991_; lean_object* v_vs_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_ks_1991_ = lean_ctor_get(v_newNode_1985_, 0);
lean_inc_ref(v_ks_1991_);
v_vs_1992_ = lean_ctor_get(v_newNode_1985_, 1);
lean_inc_ref(v_vs_1992_);
lean_dec_ref(v_newNode_1985_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1929_, v_ks_1991_, v_vs_1992_, v___x_1993_, v___x_1994_);
lean_dec_ref(v_vs_1992_);
lean_dec_ref(v_ks_1991_);
return v___x_1995_;
}
else
{
return v_newNode_1985_;
}
}
else
{
return v_newNode_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1998_, lean_object* v_keys_1999_, lean_object* v_vals_2000_, lean_object* v_i_2001_, lean_object* v_entries_2002_){
_start:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_array_get_size(v_keys_1999_);
v___x_2004_ = lean_nat_dec_lt(v_i_2001_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec(v_i_2001_);
return v_entries_2002_;
}
else
{
lean_object* v_k_2005_; lean_object* v_v_2006_; uint64_t v___x_2007_; size_t v_h_2008_; size_t v___x_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; size_t v___x_2013_; size_t v_h_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_k_2005_ = lean_array_fget_borrowed(v_keys_1999_, v_i_2001_);
v_v_2006_ = lean_array_fget_borrowed(v_vals_2000_, v_i_2001_);
v___x_2007_ = l_Lean_instHashableMVarId_hash(v_k_2005_);
v_h_2008_ = lean_uint64_to_usize(v___x_2007_);
v___x_2009_ = ((size_t)5ULL);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_sub(v_depth_1998_, v___x_2011_);
v___x_2013_ = lean_usize_mul(v___x_2009_, v___x_2012_);
v_h_2014_ = lean_usize_shift_right(v_h_2008_, v___x_2013_);
v___x_2015_ = lean_nat_add(v_i_2001_, v___x_2010_);
lean_dec(v_i_2001_);
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
v___x_2016_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_2002_, v_h_2014_, v_depth_1998_, v_k_2005_, v_v_2006_);
v_i_2001_ = v___x_2015_;
v_entries_2002_ = v___x_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_2018_, lean_object* v_keys_2019_, lean_object* v_vals_2020_, lean_object* v_i_2021_, lean_object* v_entries_2022_){
_start:
{
size_t v_depth_boxed_2023_; lean_object* v_res_2024_; 
v_depth_boxed_2023_ = lean_unbox_usize(v_depth_2018_);
lean_dec(v_depth_2018_);
v_res_2024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_2023_, v_keys_2019_, v_vals_2020_, v_i_2021_, v_entries_2022_);
lean_dec_ref(v_vals_2020_);
lean_dec_ref(v_keys_2019_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
size_t v_x_160069__boxed_2030_; size_t v_x_160070__boxed_2031_; lean_object* v_res_2032_; 
v_x_160069__boxed_2030_ = lean_unbox_usize(v_x_2026_);
lean_dec(v_x_2026_);
v_x_160070__boxed_2031_ = lean_unbox_usize(v_x_2027_);
lean_dec(v_x_2027_);
v_res_2032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2025_, v_x_160069__boxed_2030_, v_x_160070__boxed_2031_, v_x_2028_, v_x_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
uint64_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = l_Lean_instHashableMVarId_hash(v_x_2034_);
v___x_2037_ = lean_uint64_to_usize(v___x_2036_);
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2033_, v___x_2037_, v___x_2038_, v_x_2034_, v_x_2035_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_2040_, lean_object* v_val_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v_mctx_2045_; lean_object* v_cache_2046_; lean_object* v_zetaDeltaFVarIds_2047_; lean_object* v_postponed_2048_; lean_object* v_diag_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2078_; 
v___x_2044_ = lean_st_ref_take(v___y_2042_);
v_mctx_2045_ = lean_ctor_get(v___x_2044_, 0);
v_cache_2046_ = lean_ctor_get(v___x_2044_, 1);
v_zetaDeltaFVarIds_2047_ = lean_ctor_get(v___x_2044_, 2);
v_postponed_2048_ = lean_ctor_get(v___x_2044_, 3);
v_diag_2049_ = lean_ctor_get(v___x_2044_, 4);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2051_ = v___x_2044_;
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_diag_2049_);
lean_inc(v_postponed_2048_);
lean_inc(v_zetaDeltaFVarIds_2047_);
lean_inc(v_cache_2046_);
lean_inc(v_mctx_2045_);
lean_dec(v___x_2044_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_depth_2053_; lean_object* v_levelAssignDepth_2054_; lean_object* v_lmvarCounter_2055_; lean_object* v_mvarCounter_2056_; lean_object* v_lDecls_2057_; lean_object* v_decls_2058_; lean_object* v_userNames_2059_; lean_object* v_lAssignment_2060_; lean_object* v_eAssignment_2061_; lean_object* v_dAssignment_2062_; lean_object* v_instanceTypedMVars_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2077_; 
v_depth_2053_ = lean_ctor_get(v_mctx_2045_, 0);
v_levelAssignDepth_2054_ = lean_ctor_get(v_mctx_2045_, 1);
v_lmvarCounter_2055_ = lean_ctor_get(v_mctx_2045_, 2);
v_mvarCounter_2056_ = lean_ctor_get(v_mctx_2045_, 3);
v_lDecls_2057_ = lean_ctor_get(v_mctx_2045_, 4);
v_decls_2058_ = lean_ctor_get(v_mctx_2045_, 5);
v_userNames_2059_ = lean_ctor_get(v_mctx_2045_, 6);
v_lAssignment_2060_ = lean_ctor_get(v_mctx_2045_, 7);
v_eAssignment_2061_ = lean_ctor_get(v_mctx_2045_, 8);
v_dAssignment_2062_ = lean_ctor_get(v_mctx_2045_, 9);
v_instanceTypedMVars_2063_ = lean_ctor_get(v_mctx_2045_, 10);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_mctx_2045_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2065_ = v_mctx_2045_;
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_instanceTypedMVars_2063_);
lean_inc(v_dAssignment_2062_);
lean_inc(v_eAssignment_2061_);
lean_inc(v_lAssignment_2060_);
lean_inc(v_userNames_2059_);
lean_inc(v_decls_2058_);
lean_inc(v_lDecls_2057_);
lean_inc(v_mvarCounter_2056_);
lean_inc(v_lmvarCounter_2055_);
lean_inc(v_levelAssignDepth_2054_);
lean_inc(v_depth_2053_);
lean_dec(v_mctx_2045_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_2061_, v_mvarId_2040_, v_val_2041_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 8, v___x_2068_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_depth_2053_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_levelAssignDepth_2054_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_lmvarCounter_2055_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_mvarCounter_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_lDecls_2057_);
lean_ctor_set(v_reuseFailAlloc_2076_, 5, v_decls_2058_);
lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_userNames_2059_);
lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_lAssignment_2060_);
lean_ctor_set(v_reuseFailAlloc_2076_, 8, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2076_, 9, v_dAssignment_2062_);
lean_ctor_set(v_reuseFailAlloc_2076_, 10, v_instanceTypedMVars_2063_);
v___x_2070_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2070_);
v___x_2072_ = v___x_2051_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_cache_2046_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_zetaDeltaFVarIds_2047_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_postponed_2048_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_diag_2049_);
v___x_2072_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_st_ref_put(v___y_2042_, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2067_);
return v___x_2074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_2079_, lean_object* v_val_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2079_, v_val_2080_, v___y_2081_);
lean_dec(v___y_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v_ngen_2087_; lean_object* v_namePrefix_2088_; lean_object* v_idx_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2119_; 
v___x_2086_ = lean_st_ref_get(v___y_2084_);
v_ngen_2087_ = lean_ctor_get(v___x_2086_, 2);
lean_inc_ref(v_ngen_2087_);
lean_dec(v___x_2086_);
v_namePrefix_2088_ = lean_ctor_get(v_ngen_2087_, 0);
v_idx_2089_ = lean_ctor_get(v_ngen_2087_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_ngen_2087_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2091_ = v_ngen_2087_;
v_isShared_2092_ = v_isSharedCheck_2119_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_idx_2089_);
lean_inc(v_namePrefix_2088_);
lean_dec(v_ngen_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2119_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_r_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc(v_idx_2089_);
lean_inc(v_namePrefix_2088_);
v_r_2093_ = l_Lean_Name_num___override(v_namePrefix_2088_, v_idx_2089_);
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_add(v_idx_2089_, v___x_2094_);
lean_dec(v_idx_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2095_);
v___x_2097_ = v___x_2091_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_namePrefix_2088_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v_env_2099_; lean_object* v_nextMacroScope_2100_; lean_object* v_auxDeclNGen_2101_; lean_object* v_traceState_2102_; lean_object* v_cache_2103_; lean_object* v_recordedDeps_2104_; lean_object* v_messages_2105_; lean_object* v_infoState_2106_; lean_object* v_snapshotTasks_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2116_; 
v___x_2098_ = lean_st_ref_take(v___y_2084_);
v_env_2099_ = lean_ctor_get(v___x_2098_, 0);
v_nextMacroScope_2100_ = lean_ctor_get(v___x_2098_, 1);
v_auxDeclNGen_2101_ = lean_ctor_get(v___x_2098_, 3);
v_traceState_2102_ = lean_ctor_get(v___x_2098_, 4);
v_cache_2103_ = lean_ctor_get(v___x_2098_, 5);
v_recordedDeps_2104_ = lean_ctor_get(v___x_2098_, 6);
v_messages_2105_ = lean_ctor_get(v___x_2098_, 7);
v_infoState_2106_ = lean_ctor_get(v___x_2098_, 8);
v_snapshotTasks_2107_ = lean_ctor_get(v___x_2098_, 9);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2098_, 2);
lean_dec(v_unused_2117_);
v___x_2109_ = v___x_2098_;
v_isShared_2110_ = v_isSharedCheck_2116_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snapshotTasks_2107_);
lean_inc(v_infoState_2106_);
lean_inc(v_messages_2105_);
lean_inc(v_recordedDeps_2104_);
lean_inc(v_cache_2103_);
lean_inc(v_traceState_2102_);
lean_inc(v_auxDeclNGen_2101_);
lean_inc(v_nextMacroScope_2100_);
lean_inc(v_env_2099_);
lean_dec(v___x_2098_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2116_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 2, v___x_2097_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_env_2099_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_nextMacroScope_2100_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_auxDeclNGen_2101_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_traceState_2102_);
lean_ctor_set(v_reuseFailAlloc_2115_, 5, v_cache_2103_);
lean_ctor_set(v_reuseFailAlloc_2115_, 6, v_recordedDeps_2104_);
lean_ctor_set(v_reuseFailAlloc_2115_, 7, v_messages_2105_);
lean_ctor_set(v_reuseFailAlloc_2115_, 8, v_infoState_2106_);
lean_ctor_set(v_reuseFailAlloc_2115_, 9, v_snapshotTasks_2107_);
v___x_2112_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_st_ref_put(v___y_2084_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_r_2093_);
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2120_);
lean_dec(v___y_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v___x_2134_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2132_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
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
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_2160_, lean_object* v_a_2161_, uint8_t v___x_2162_, uint8_t v___x_2163_, uint8_t v___x_2164_, lean_object* v_a_2165_, lean_object* v___x_2166_, lean_object* v_expr_2167_, lean_object* v___x_2168_, lean_object* v_val_2169_, lean_object* v_mvarId_2170_, lean_object* v___x_2171_, lean_object* v_a_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Meta_mkLambdaFVars(v___x_2160_, v_a_2161_, v___x_2162_, v___x_2163_, v___x_2162_, v___x_2163_, v___x_2164_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2165_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_mkConst(v___x_2186_, v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(5u);
v___x_2191_ = lean_mk_empty_array_with_capacity(v___x_2190_);
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2166_);
v___x_2193_ = lean_array_push(v___x_2192_, v_expr_2167_);
v___x_2194_ = lean_array_push(v___x_2193_, v___x_2168_);
v___x_2195_ = lean_array_push(v___x_2194_, v_val_2169_);
v___x_2196_ = lean_array_push(v___x_2195_, v_a_2185_);
v___x_2197_ = l_Lean_mkAppN(v___x_2189_, v___x_2196_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2170_, v___x_2197_, v___y_2180_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2217_);
v___x_2200_ = v___x_2198_;
v_isShared_2201_ = v_isSharedCheck_2216_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v___x_2198_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2216_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v_toGoalState_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2214_; 
v___x_2202_ = lean_st_ref_get(v___y_2173_);
v_toGoalState_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2202_, 1);
lean_dec(v_unused_2215_);
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2214_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_toGoalState_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2214_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2171_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_toGoalState_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2171_);
v___x_2208_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2172_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2209_);
v___x_2211_ = v___x_2200_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2172_);
lean_dec(v___x_2171_);
v_a_2218_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2198_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2198_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2172_);
lean_dec(v___x_2171_);
lean_dec(v_mvarId_2170_);
lean_dec_ref(v_val_2169_);
lean_dec_ref(v___x_2168_);
lean_dec_ref(v_expr_2167_);
lean_dec_ref(v___x_2166_);
lean_dec(v_a_2165_);
v_a_2226_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2184_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2184_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_2234_ = _args[0];
lean_object* v_a_2235_ = _args[1];
lean_object* v___x_2236_ = _args[2];
lean_object* v___x_2237_ = _args[3];
lean_object* v___x_2238_ = _args[4];
lean_object* v_a_2239_ = _args[5];
lean_object* v___x_2240_ = _args[6];
lean_object* v_expr_2241_ = _args[7];
lean_object* v___x_2242_ = _args[8];
lean_object* v_val_2243_ = _args[9];
lean_object* v_mvarId_2244_ = _args[10];
lean_object* v___x_2245_ = _args[11];
lean_object* v_a_2246_ = _args[12];
lean_object* v___y_2247_ = _args[13];
lean_object* v___y_2248_ = _args[14];
lean_object* v___y_2249_ = _args[15];
lean_object* v___y_2250_ = _args[16];
lean_object* v___y_2251_ = _args[17];
lean_object* v___y_2252_ = _args[18];
lean_object* v___y_2253_ = _args[19];
lean_object* v___y_2254_ = _args[20];
lean_object* v___y_2255_ = _args[21];
lean_object* v___y_2256_ = _args[22];
lean_object* v___y_2257_ = _args[23];
_start:
{
uint8_t v___x_160391__boxed_2258_; uint8_t v___x_160392__boxed_2259_; uint8_t v___x_160393__boxed_2260_; lean_object* v_res_2261_; 
v___x_160391__boxed_2258_ = lean_unbox(v___x_2236_);
v___x_160392__boxed_2259_ = lean_unbox(v___x_2237_);
v___x_160393__boxed_2260_ = lean_unbox(v___x_2238_);
v_res_2261_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_2234_, v_a_2235_, v___x_160391__boxed_2258_, v___x_160392__boxed_2259_, v___x_160393__boxed_2260_, v_a_2239_, v___x_2240_, v_expr_2241_, v___x_2242_, v_val_2243_, v_mvarId_2244_, v___x_2245_, v_a_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___x_2234_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_2267_, lean_object* v_a_2268_, uint8_t v___x_2269_, uint8_t v___x_2270_, uint8_t v___x_2271_, lean_object* v_a_2272_, lean_object* v___x_2273_, lean_object* v___x_2274_, lean_object* v_expr_2275_, lean_object* v___x_2276_, lean_object* v_val_2277_, lean_object* v_mvarId_2278_, lean_object* v___x_2279_, lean_object* v_a_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Meta_mkLambdaFVars(v___x_2267_, v_a_2268_, v___x_2269_, v___x_2270_, v___x_2269_, v___x_2270_, v___x_2271_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_a_2272_);
lean_ctor_set(v___x_2295_, 1, v___x_2273_);
v___x_2296_ = l_Lean_mkConst(v___x_2294_, v___x_2295_);
v___x_2297_ = lean_unsigned_to_nat(5u);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___x_2297_);
v___x_2299_ = lean_array_push(v___x_2298_, v___x_2274_);
v___x_2300_ = lean_array_push(v___x_2299_, v_expr_2275_);
v___x_2301_ = lean_array_push(v___x_2300_, v___x_2276_);
v___x_2302_ = lean_array_push(v___x_2301_, v_val_2277_);
v___x_2303_ = lean_array_push(v___x_2302_, v_a_2293_);
v___x_2304_ = l_Lean_mkAppN(v___x_2296_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2278_, v___x_2304_, v___y_2288_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2323_; 
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2305_, 0);
lean_dec(v_unused_2324_);
v___x_2307_ = v___x_2305_;
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v___x_2305_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v_toGoalState_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2321_; 
v___x_2309_ = lean_st_ref_get(v___y_2281_);
v_toGoalState_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2309_, 1);
lean_dec(v_unused_2322_);
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_toGoalState_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 1, v___x_2279_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_toGoalState_2310_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2279_);
v___x_2315_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2316_, 0, v_a_2280_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2316_);
v___x_2318_ = v___x_2307_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
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
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2280_);
lean_dec(v___x_2279_);
v_a_2325_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2305_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2305_);
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
lean_dec(v___x_2279_);
lean_dec(v_mvarId_2278_);
lean_dec_ref(v_val_2277_);
lean_dec_ref(v___x_2276_);
lean_dec_ref(v_expr_2275_);
lean_dec_ref(v___x_2274_);
lean_dec(v___x_2273_);
lean_dec(v_a_2272_);
v_a_2333_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2292_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2292_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_2341_ = _args[0];
lean_object* v_a_2342_ = _args[1];
lean_object* v___x_2343_ = _args[2];
lean_object* v___x_2344_ = _args[3];
lean_object* v___x_2345_ = _args[4];
lean_object* v_a_2346_ = _args[5];
lean_object* v___x_2347_ = _args[6];
lean_object* v___x_2348_ = _args[7];
lean_object* v_expr_2349_ = _args[8];
lean_object* v___x_2350_ = _args[9];
lean_object* v_val_2351_ = _args[10];
lean_object* v_mvarId_2352_ = _args[11];
lean_object* v___x_2353_ = _args[12];
lean_object* v_a_2354_ = _args[13];
lean_object* v___y_2355_ = _args[14];
lean_object* v___y_2356_ = _args[15];
lean_object* v___y_2357_ = _args[16];
lean_object* v___y_2358_ = _args[17];
lean_object* v___y_2359_ = _args[18];
lean_object* v___y_2360_ = _args[19];
lean_object* v___y_2361_ = _args[20];
lean_object* v___y_2362_ = _args[21];
lean_object* v___y_2363_ = _args[22];
lean_object* v___y_2364_ = _args[23];
lean_object* v___y_2365_ = _args[24];
_start:
{
uint8_t v___x_160573__boxed_2366_; uint8_t v___x_160574__boxed_2367_; uint8_t v___x_160575__boxed_2368_; lean_object* v_res_2369_; 
v___x_160573__boxed_2366_ = lean_unbox(v___x_2343_);
v___x_160574__boxed_2367_ = lean_unbox(v___x_2344_);
v___x_160575__boxed_2368_ = lean_unbox(v___x_2345_);
v_res_2369_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_2341_, v_a_2342_, v___x_160573__boxed_2366_, v___x_160574__boxed_2367_, v___x_160575__boxed_2368_, v_a_2346_, v___x_2347_, v___x_2348_, v_expr_2349_, v___x_2350_, v_val_2351_, v_mvarId_2352_, v___x_2353_, v_a_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___x_2341_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_2370_, lean_object* v_a_2371_, uint8_t v___x_2372_, uint8_t v___x_2373_, uint8_t v___x_2374_, lean_object* v_mvarId_2375_, lean_object* v___x_2376_, lean_object* v_a_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Meta_mkLambdaFVars(v___x_2370_, v_a_2371_, v___x_2372_, v___x_2373_, v___x_2372_, v___x_2373_, v___x_2374_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2375_, v_a_2390_, v___y_2385_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2409_; 
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2410_);
v___x_2393_ = v___x_2391_;
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v___x_2391_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v_toGoalState_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2407_; 
v___x_2395_ = lean_st_ref_get(v___y_2378_);
v_toGoalState_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; 
v_unused_2408_ = lean_ctor_get(v___x_2395_, 1);
lean_dec(v_unused_2408_);
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_toGoalState_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v___x_2376_);
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_toGoalState_2396_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2376_);
v___x_2401_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_a_2377_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2402_);
v___x_2404_ = v___x_2393_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
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
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_a_2377_);
lean_dec(v___x_2376_);
v_a_2411_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2391_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2391_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_a_2377_);
lean_dec(v___x_2376_);
lean_dec(v_mvarId_2375_);
v_a_2419_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2389_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2389_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2427_ = _args[0];
lean_object* v_a_2428_ = _args[1];
lean_object* v___x_2429_ = _args[2];
lean_object* v___x_2430_ = _args[3];
lean_object* v___x_2431_ = _args[4];
lean_object* v_mvarId_2432_ = _args[5];
lean_object* v___x_2433_ = _args[6];
lean_object* v_a_2434_ = _args[7];
lean_object* v___y_2435_ = _args[8];
lean_object* v___y_2436_ = _args[9];
lean_object* v___y_2437_ = _args[10];
lean_object* v___y_2438_ = _args[11];
lean_object* v___y_2439_ = _args[12];
lean_object* v___y_2440_ = _args[13];
lean_object* v___y_2441_ = _args[14];
lean_object* v___y_2442_ = _args[15];
lean_object* v___y_2443_ = _args[16];
lean_object* v___y_2444_ = _args[17];
lean_object* v___y_2445_ = _args[18];
_start:
{
uint8_t v___x_160744__boxed_2446_; uint8_t v___x_160745__boxed_2447_; uint8_t v___x_160746__boxed_2448_; lean_object* v_res_2449_; 
v___x_160744__boxed_2446_ = lean_unbox(v___x_2429_);
v___x_160745__boxed_2447_ = lean_unbox(v___x_2430_);
v___x_160746__boxed_2448_ = lean_unbox(v___x_2431_);
v_res_2449_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2427_, v_a_2428_, v___x_160744__boxed_2446_, v___x_160745__boxed_2447_, v___x_160746__boxed_2448_, v_mvarId_2432_, v___x_2433_, v_a_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___x_2427_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2452_, lean_object* v___x_2453_, lean_object* v_generation_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
lean_inc(v_mvarId_2452_);
v___x_2466_ = l_Lean_MVarId_getTag(v_mvarId_2452_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2453_, v_a_2467_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_n(v_a_2469_, 2);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2452_, v_a_2469_, v___y_2462_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; lean_object* v_toGoalState_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref_known(v___x_2470_, 1);
v___x_2471_ = lean_st_ref_get(v___y_2455_);
v_toGoalState_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2471_, 1);
lean_dec(v_unused_2482_);
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_toGoalState_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = l_Lean_Expr_mvarId_x21(v_a_2469_);
lean_dec(v_a_2469_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_toGoalState_2472_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2478_, v_generation_2454_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2469_);
lean_dec(v_generation_2454_);
v_a_2483_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2470_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2470_);
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
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v_generation_2454_);
lean_dec(v_mvarId_2452_);
v_a_2491_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2468_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2468_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_generation_2454_);
lean_dec_ref(v___x_2453_);
lean_dec(v_mvarId_2452_);
v_a_2499_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2466_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2466_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2507_, lean_object* v___x_2508_, lean_object* v_generation_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2507_, v___x_2508_, v_generation_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec(v___y_2510_);
return v_res_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_box(0);
v___x_2527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2));
v___x_2528_ = l_Lean_mkConst(v___x_2527_, v___x_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2529_, lean_object* v_generation_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_a_2543_; lean_object* v___y_2548_; lean_object* v___x_2558_; lean_object* v_mvarId_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2836_; 
lean_inc_ref(v_goal_2529_);
v___x_2541_ = lean_st_mk_ref(v_goal_2529_);
v___x_2558_ = lean_st_ref_get(v___x_2541_);
v_mvarId_2559_ = lean_ctor_get(v___x_2558_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2558_, 0);
lean_dec(v_unused_2837_);
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2836_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_mvarId_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2836_;
goto v_resetjp_2560_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_st_ref_get(v___x_2541_);
lean_dec(v___x_2541_);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v_a_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
v___jp_2547_:
{
if (lean_obj_tag(v___y_2548_) == 0)
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___y_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___y_2548_, 1);
v_a_2543_ = v_a_2549_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v___x_2541_);
v_a_2550_ = lean_ctor_get(v___y_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___y_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___y_2548_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___y_2548_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; uint8_t v___x_2565_; uint8_t v___x_2566_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l_Lean_Expr_isForall(v_a_2564_);
v___x_2566_ = 1;
if (v___x_2565_ == 0)
{
uint8_t v___x_2567_; 
lean_del_object(v___x_2561_);
v___x_2567_ = l_Lean_Expr_isLet(v_a_2564_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_dec(v_a_2564_);
lean_dec_ref(v___y_2536_);
lean_dec(v_generation_2530_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_goal_2529_);
v_a_2543_ = v___x_2568_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2569_; 
lean_dec_ref(v_goal_2529_);
v___x_2569_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2532_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; uint8_t v_zetaDelta_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v_zetaDelta_2571_ = lean_ctor_get_uint8(v_a_2570_, sizeof(void*)*18 + 19);
lean_dec(v_a_2570_);
if (v_zetaDelta_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_dec(v_a_2564_);
v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v_mvarId_2576_; lean_object* v___x_2577_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2574_, 0, v_a_2573_);
lean_closure_set(v___f_2574_, 1, v_generation_2530_);
v___x_2575_ = lean_st_ref_get(v___x_2541_);
v_mvarId_2576_ = lean_ctor_get(v___x_2575_, 1);
lean_inc(v_mvarId_2576_);
lean_dec(v___x_2575_);
v___x_2577_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2576_, v___f_2574_, v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2536_);
v___y_2548_ = v___x_2577_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
lean_dec(v_generation_2530_);
v_a_2578_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2572_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2572_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_mvarId_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; 
v___x_2586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2587_ = l_Lean_Meta_expandLet(v_a_2564_, v___x_2586_, v___x_2566_);
lean_dec(v_a_2564_);
v___x_2588_ = lean_st_ref_get(v___x_2541_);
v_mvarId_2589_ = lean_ctor_get(v___x_2588_, 1);
lean_inc_n(v_mvarId_2589_, 2);
lean_dec(v___x_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2590_, 0, v_mvarId_2589_);
lean_closure_set(v___f_2590_, 1, v___x_2587_);
lean_closure_set(v___f_2590_, 2, v_generation_2530_);
v___x_2591_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2589_, v___f_2590_, v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2536_);
v___y_2548_ = v___x_2591_;
goto v___jp_2547_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
lean_dec(v_generation_2530_);
v_a_2592_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2569_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2569_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
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
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec(v_generation_2530_);
lean_dec_ref(v_goal_2529_);
v___x_2600_ = l_Lean_Expr_bindingDomain_x21(v_a_2564_);
lean_inc_ref(v___x_2600_);
v___x_2601_ = l_Lean_Meta_isProp(v___x_2600_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
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
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec_ref(v___y_2536_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_st_ref_get(v___x_2541_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set_tag(v___x_2561_, 3);
lean_ctor_set(v___x_2561_, 1, v___x_2606_);
lean_ctor_set(v___x_2561_, 0, v_a_2605_);
v___x_2608_ = v___x_2561_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2605_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
v_a_2543_ = v___x_2608_;
goto v___jp_2542_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_del_object(v___x_2561_);
lean_dec(v___x_2541_);
v_a_2610_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2604_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2604_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v_mvarId_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2818_; 
lean_del_object(v___x_2561_);
v___x_2618_ = 0;
v___x_2619_ = lean_st_ref_get(v___x_2541_);
v_mvarId_2620_ = lean_ctor_get(v___x_2619_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2818_ == 0)
{
lean_object* v_unused_2819_; 
v_unused_2819_ = lean_ctor_get(v___x_2619_, 0);
lean_dec(v_unused_2819_);
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2818_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_mvarId_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2818_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; 
lean_inc(v_mvarId_2620_);
v___x_2624_ = l_Lean_MVarId_getTag(v_mvarId_2620_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = l_Lean_Expr_bindingBody_x21(v_a_2564_);
v___x_2627_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_n(v_a_2628_, 2);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = l_Lean_Meta_Grind_registerFVarAnchor___redArg(v_a_2628_, v___x_2541_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2629_, 1);
lean_inc(v_a_2628_);
v___x_2630_ = l_Lean_mkFVar(v_a_2628_);
lean_inc_ref(v___x_2600_);
v___x_2631_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2600_, v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v_lctx_2633_; lean_object* v_localInstances_2634_; lean_object* v_expr_2635_; lean_object* v_proof_x3f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v_lctx_2633_ = lean_ctor_get(v___y_2536_, 2);
v_localInstances_2634_ = lean_ctor_get(v___y_2536_, 3);
v_expr_2635_ = lean_ctor_get(v_a_2632_, 0);
lean_inc_ref_n(v_expr_2635_, 2);
v_proof_x3f_2636_ = lean_ctor_get(v_a_2632_, 1);
lean_inc(v_proof_x3f_2636_);
lean_dec(v_a_2632_);
v___x_2637_ = l_Lean_Expr_bindingName_x21(v_a_2564_);
lean_inc(v___x_2637_);
v___x_2638_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2637_, v_expr_2635_, v___x_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; uint8_t v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v_localInsts_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___x_2763_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = l_Lean_Expr_bindingInfo_x21(v_a_2564_);
v___x_2641_ = 0;
lean_inc_ref_n(v_expr_2635_, 2);
lean_inc(v_a_2628_);
lean_inc_ref(v_lctx_2633_);
v___x_2642_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2633_, v_a_2628_, v_a_2639_, v_expr_2635_, v___x_2640_, v___x_2641_);
v___x_2763_ = l_Lean_Meta_isClass_x3f(v_expr_2635_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
if (lean_obj_tag(v_a_2764_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2767_; 
v_val_2765_ = lean_ctor_get(v_a_2764_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v_a_2764_, 1);
lean_inc_ref(v___x_2630_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v___x_2630_);
lean_ctor_set(v___x_2622_, 0, v_val_2765_);
v___x_2767_ = v___x_2622_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_val_2765_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2630_);
v___x_2767_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; 
lean_inc_ref(v_localInstances_2634_);
v___x_2768_ = lean_array_push(v_localInstances_2634_, v___x_2767_);
lean_inc(v___x_2541_);
v_localInsts_2679_ = v___x_2768_;
v___y_2680_ = v___x_2541_;
v___y_2681_ = v___y_2531_;
v___y_2682_ = v___y_2532_;
v___y_2683_ = v___y_2533_;
v___y_2684_ = v___y_2534_;
v___y_2685_ = v___y_2535_;
v___y_2686_ = v___y_2536_;
v___y_2687_ = v___y_2537_;
v___y_2688_ = v___y_2538_;
v___y_2689_ = v___y_2539_;
goto v___jp_2678_;
}
}
else
{
lean_inc_ref(v_localInstances_2634_);
lean_dec(v_a_2764_);
lean_del_object(v___x_2622_);
lean_inc(v___x_2541_);
v_localInsts_2679_ = v_localInstances_2634_;
v___y_2680_ = v___x_2541_;
v___y_2681_ = v___y_2531_;
v___y_2682_ = v___y_2532_;
v___y_2683_ = v___y_2533_;
v___y_2684_ = v___y_2534_;
v___y_2685_ = v___y_2535_;
v___y_2686_ = v___y_2536_;
v___y_2687_ = v___y_2537_;
v___y_2688_ = v___y_2538_;
v___y_2689_ = v___y_2539_;
goto v___jp_2678_;
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v___x_2642_);
lean_dec(v___x_2637_);
lean_dec(v_proof_x3f_2636_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2770_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2763_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2763_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
v___jp_2643_:
{
uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = 2;
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2642_, v___y_2650_, v___y_2655_, v___x_2656_, v_a_2625_, v___x_2657_, v___y_2648_, v___y_2654_, v___y_2645_, v___y_2652_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_Expr_mvarId_x21(v_a_2659_);
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_mk_empty_array_with_capacity(v___x_2661_);
v___x_2663_ = lean_array_push(v___x_2662_, v___x_2630_);
v___x_2664_ = 1;
v___x_2665_ = lean_box(v___x_2618_);
v___x_2666_ = lean_box(v___x_2566_);
v___x_2667_ = lean_box(v___x_2664_);
lean_inc(v___x_2660_);
v___f_2668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2668_, 0, v___x_2663_);
lean_closure_set(v___f_2668_, 1, v_a_2659_);
lean_closure_set(v___f_2668_, 2, v___x_2665_);
lean_closure_set(v___f_2668_, 3, v___x_2666_);
lean_closure_set(v___f_2668_, 4, v___x_2667_);
lean_closure_set(v___f_2668_, 5, v_mvarId_2620_);
lean_closure_set(v___f_2668_, 6, v___x_2660_);
lean_closure_set(v___f_2668_, 7, v_a_2628_);
v___x_2669_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2660_, v___f_2668_, v___y_2649_, v___y_2644_, v___y_2647_, v___y_2651_, v___y_2646_, v___y_2653_, v___y_2648_, v___y_2654_, v___y_2645_, v___y_2652_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2649_);
v___y_2548_ = v___x_2669_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec(v_mvarId_2620_);
lean_dec(v___x_2541_);
v_a_2670_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2658_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2658_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
v___jp_2678_:
{
if (lean_obj_tag(v_proof_x3f_2636_) == 0)
{
uint8_t v___x_2690_; 
lean_dec(v___x_2637_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2600_);
v___x_2690_ = l_Lean_Expr_isArrow(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_expr_instantiate1(v___x_2626_, v___x_2630_);
lean_dec_ref(v___x_2626_);
v___y_2644_ = v___y_2681_;
v___y_2645_ = v___y_2688_;
v___y_2646_ = v___y_2684_;
v___y_2647_ = v___y_2682_;
v___y_2648_ = v___y_2686_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v_localInsts_2679_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2689_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___x_2691_;
goto v___jp_2643_;
}
else
{
v___y_2644_ = v___y_2681_;
v___y_2645_ = v___y_2688_;
v___y_2646_ = v___y_2684_;
v___y_2647_ = v___y_2682_;
v___y_2648_ = v___y_2686_;
v___y_2649_ = v___y_2680_;
v___y_2650_ = v_localInsts_2679_;
v___y_2651_ = v___y_2683_;
v___y_2652_ = v___y_2689_;
v___y_2653_ = v___y_2685_;
v___y_2654_ = v___y_2687_;
v___y_2655_ = v___x_2626_;
goto v___jp_2643_;
}
}
else
{
lean_object* v_val_2692_; uint8_t v___x_2693_; 
v_val_2692_ = lean_ctor_get(v_proof_x3f_2636_, 0);
lean_inc(v_val_2692_);
lean_dec_ref_known(v_proof_x3f_2636_, 1);
v___x_2693_ = l_Lean_Expr_isArrow(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_inc_ref(v___x_2626_);
lean_inc_ref_n(v___x_2600_, 2);
v___x_2694_ = l_Lean_mkLambda(v___x_2637_, v___x_2640_, v___x_2600_, v___x_2626_);
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3);
lean_inc_ref(v___x_2630_);
lean_inc(v_val_2692_);
lean_inc_ref(v_expr_2635_);
v___x_2697_ = l_Lean_mkApp4(v___x_2696_, v___x_2600_, v_expr_2635_, v_val_2692_, v___x_2630_);
v___x_2698_ = lean_expr_instantiate1(v___x_2626_, v___x_2697_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2626_);
lean_inc_ref(v___x_2698_);
v___x_2699_ = l_Lean_Meta_getLevel(v___x_2698_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = 2;
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2642_, v_localInsts_2679_, v___x_2698_, v___x_2701_, v_a_2625_, v___x_2702_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = l_Lean_Expr_mvarId_x21(v_a_2704_);
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
v___x_2708_ = lean_array_push(v___x_2707_, v___x_2630_);
v___x_2709_ = 1;
v___x_2710_ = lean_box(v___x_2693_);
v___x_2711_ = lean_box(v___x_2566_);
v___x_2712_ = lean_box(v___x_2709_);
lean_inc(v___x_2705_);
v___f_2713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2713_, 0, v___x_2708_);
lean_closure_set(v___f_2713_, 1, v_a_2704_);
lean_closure_set(v___f_2713_, 2, v___x_2710_);
lean_closure_set(v___f_2713_, 3, v___x_2711_);
lean_closure_set(v___f_2713_, 4, v___x_2712_);
lean_closure_set(v___f_2713_, 5, v_a_2700_);
lean_closure_set(v___f_2713_, 6, v___x_2695_);
lean_closure_set(v___f_2713_, 7, v___x_2600_);
lean_closure_set(v___f_2713_, 8, v_expr_2635_);
lean_closure_set(v___f_2713_, 9, v___x_2694_);
lean_closure_set(v___f_2713_, 10, v_val_2692_);
lean_closure_set(v___f_2713_, 11, v_mvarId_2620_);
lean_closure_set(v___f_2713_, 12, v___x_2705_);
lean_closure_set(v___f_2713_, 13, v_a_2628_);
v___x_2714_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2705_, v___f_2713_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
v___y_2548_ = v___x_2714_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2700_);
lean_dec_ref(v___x_2694_);
lean_dec(v_val_2692_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v___x_2541_);
v_a_2715_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2703_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2703_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___x_2698_);
lean_dec_ref(v___x_2694_);
lean_dec(v_val_2692_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
lean_dec_ref(v_localInsts_2679_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec(v_a_2625_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v___x_2541_);
v_a_2723_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2699_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2699_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v___x_2731_; 
lean_dec(v___x_2637_);
lean_inc_ref(v___x_2626_);
v___x_2731_ = l_Lean_Meta_getLevel(v___x_2626_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = 2;
v___x_2734_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_2626_);
v___x_2735_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2642_, v_localInsts_2679_, v___x_2626_, v___x_2733_, v_a_2625_, v___x_2734_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_Expr_mvarId_x21(v_a_2736_);
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_mk_empty_array_with_capacity(v___x_2738_);
v___x_2740_ = lean_array_push(v___x_2739_, v___x_2630_);
v___x_2741_ = 1;
v___x_2742_ = lean_box(v___x_2618_);
v___x_2743_ = lean_box(v___x_2566_);
v___x_2744_ = lean_box(v___x_2741_);
lean_inc(v___x_2737_);
v___f_2745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2745_, 0, v___x_2740_);
lean_closure_set(v___f_2745_, 1, v_a_2736_);
lean_closure_set(v___f_2745_, 2, v___x_2742_);
lean_closure_set(v___f_2745_, 3, v___x_2743_);
lean_closure_set(v___f_2745_, 4, v___x_2744_);
lean_closure_set(v___f_2745_, 5, v_a_2732_);
lean_closure_set(v___f_2745_, 6, v___x_2600_);
lean_closure_set(v___f_2745_, 7, v_expr_2635_);
lean_closure_set(v___f_2745_, 8, v___x_2626_);
lean_closure_set(v___f_2745_, 9, v_val_2692_);
lean_closure_set(v___f_2745_, 10, v_mvarId_2620_);
lean_closure_set(v___f_2745_, 11, v___x_2737_);
lean_closure_set(v___f_2745_, 12, v_a_2628_);
v___x_2746_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2737_, v___f_2745_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
v___y_2548_ = v___x_2746_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2732_);
lean_dec(v_val_2692_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v___x_2541_);
v_a_2747_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2735_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2735_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_val_2692_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2680_);
lean_dec_ref(v_localInsts_2679_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v___x_2541_);
v_a_2755_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2731_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2731_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v___x_2637_);
lean_dec(v_proof_x3f_2636_);
lean_dec_ref(v_expr_2635_);
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2778_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2638_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2638_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v___x_2630_);
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2786_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2631_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2631_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_a_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2794_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2629_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2629_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
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
lean_dec_ref(v___x_2626_);
lean_dec(v_a_2625_);
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2802_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2627_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2627_);
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
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_del_object(v___x_2622_);
lean_dec(v_mvarId_2620_);
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2810_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2624_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2624_);
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
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v___x_2600_);
lean_dec(v_a_2564_);
lean_del_object(v___x_2561_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
v_a_2820_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2601_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2601_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2561_);
lean_dec(v___x_2541_);
lean_dec_ref(v___y_2536_);
lean_dec(v_generation_2530_);
lean_dec_ref(v_goal_2529_);
v_a_2828_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2563_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2563_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2838_, lean_object* v_generation_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2838_, v_generation_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2851_, lean_object* v_generation_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_mvarId_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; 
v_mvarId_2863_ = lean_ctor_get(v_goal_2851_, 1);
lean_inc(v_mvarId_2863_);
v___f_2864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2864_, 0, v_goal_2851_);
lean_closure_set(v___f_2864_, 1, v_generation_2852_);
v___x_2865_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2863_, v___f_2864_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2874_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_fst_2870_; lean_object* v___x_2872_; 
v_fst_2870_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_fst_2870_);
lean_dec(v_a_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_fst_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_fst_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2865_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2865_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2883_, lean_object* v_generation_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2883_, v_generation_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2896_, lean_object* v_val_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2896_, v_val_2897_, v___y_2905_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2910_, lean_object* v_val_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2910_, v_val_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2949_, v_x_2950_, v_x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2953_, lean_object* v_x_2954_, size_t v_x_2955_, size_t v_x_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2954_, v_x_2955_, v_x_2956_, v_x_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_){
_start:
{
size_t v_x_161739__boxed_2966_; size_t v_x_161740__boxed_2967_; lean_object* v_res_2968_; 
v_x_161739__boxed_2966_ = lean_unbox_usize(v_x_2962_);
lean_dec(v_x_2962_);
v_x_161740__boxed_2967_ = lean_unbox_usize(v_x_2963_);
lean_dec(v_x_2963_);
v_res_2968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2960_, v_x_2961_, v_x_161739__boxed_2966_, v_x_161740__boxed_2967_, v_x_2964_, v_x_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2969_, lean_object* v_n_2970_, lean_object* v_k_2971_, lean_object* v_v_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2970_, v_k_2971_, v_v_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2974_, size_t v_depth_2975_, lean_object* v_keys_2976_, lean_object* v_vals_2977_, lean_object* v_heq_2978_, lean_object* v_i_2979_, lean_object* v_entries_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2975_, v_keys_2976_, v_vals_2977_, v_i_2979_, v_entries_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2982_, lean_object* v_depth_2983_, lean_object* v_keys_2984_, lean_object* v_vals_2985_, lean_object* v_heq_2986_, lean_object* v_i_2987_, lean_object* v_entries_2988_){
_start:
{
size_t v_depth_boxed_2989_; lean_object* v_res_2990_; 
v_depth_boxed_2989_ = lean_unbox_usize(v_depth_2983_);
lean_dec(v_depth_2983_);
v_res_2990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2982_, v_depth_boxed_2989_, v_keys_2984_, v_vals_2985_, v_heq_2986_, v_i_2987_, v_entries_2988_);
lean_dec_ref(v_vals_2985_);
lean_dec_ref(v_keys_2984_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2992_, v_x_2993_, v_x_2994_, v_x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Expr_getAppFn(v_type_2997_);
if (lean_obj_tag(v___x_3000_) == 4)
{
lean_object* v_declName_3001_; lean_object* v___x_3002_; 
v_declName_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_declName_3001_);
lean_dec_ref_known(v___x_3000_, 2);
v___x_3002_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_3001_, v_a_2998_);
lean_dec(v_declName_3001_);
return v___x_3002_;
}
else
{
uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec_ref(v___x_3000_);
v___x_3003_ = 0;
v___x_3004_ = lean_box(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_3006_, v_a_3007_);
lean_dec_ref(v_a_3007_);
lean_dec_ref(v_type_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_3010_, v_a_3012_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_type_3022_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3034_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
lean_ctor_set(v___x_3039_, 3, v___x_3038_);
lean_ctor_set(v___x_3039_, 4, v___x_3037_);
lean_ctor_set(v___x_3039_, 5, v___x_3037_);
lean_ctor_set(v___x_3039_, 6, v___x_3037_);
lean_ctor_set(v___x_3039_, 7, v___x_3037_);
lean_ctor_set(v___x_3039_, 8, v___x_3037_);
lean_ctor_set(v___x_3039_, 9, v___x_3037_);
lean_ctor_set(v___x_3039_, 10, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = lean_unsigned_to_nat(32u);
v___x_3041_ = lean_mk_empty_array_with_capacity(v___x_3040_);
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3043_ = ((size_t)5ULL);
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_unsigned_to_nat(32u);
v___x_3046_ = lean_mk_empty_array_with_capacity(v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_3048_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_3046_);
lean_ctor_set(v___x_3048_, 2, v___x_3044_);
lean_ctor_set(v___x_3048_, 3, v___x_3044_);
lean_ctor_set_usize(v___x_3048_, 4, v___x_3043_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_box(1);
v___x_3050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_3051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_3052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3050_);
lean_ctor_set(v___x_3052_, 2, v___x_3049_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_3070_ = l_Lean_stringToMessageData(v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_3086_, lean_object* v_declHint_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_env_3092_; uint8_t v___x_3093_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_st_ref_get(v___y_3088_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_env_3092_);
lean_dec(v___x_3091_);
v___x_3093_ = l_Lean_Name_isAnonymous(v_declHint_3087_);
if (v___x_3093_ == 0)
{
uint8_t v_isExporting_3094_; 
v_isExporting_3094_ = lean_ctor_get_uint8(v_env_3092_, sizeof(void*)*13);
if (v_isExporting_3094_ == 0)
{
lean_object* v___x_3095_; 
lean_dec_ref(v_env_3092_);
lean_dec(v_declHint_3087_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_msg_3086_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
lean_inc_ref(v_env_3092_);
v___x_3096_ = l_Lean_Environment_setExporting(v_env_3092_, v___x_3093_);
lean_inc(v_declHint_3087_);
lean_inc_ref(v___x_3096_);
v___x_3097_ = l_Lean_Environment_contains(v___x_3096_, v_declHint_3087_, v_isExporting_3094_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_dec_ref(v___x_3096_);
lean_dec_ref(v_env_3092_);
lean_dec(v_declHint_3087_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_msg_3086_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_c_3104_; lean_object* v___x_3105_; 
v___x_3099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_3100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_3101_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3096_);
v___x_3102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3096_);
lean_ctor_set(v___x_3102_, 1, v___x_3099_);
lean_ctor_set(v___x_3102_, 2, v___x_3100_);
lean_ctor_set(v___x_3102_, 3, v___x_3101_);
lean_inc(v_declHint_3087_);
v___x_3103_ = l_Lean_MessageData_ofConstName(v_declHint_3087_, v___x_3093_);
v_c_3104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3104_, 0, v___x_3102_);
lean_ctor_set(v_c_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3096_, v_declHint_3087_);
lean_dec_ref(v___x_3096_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec_ref(v_env_3092_);
lean_dec(v_declHint_3087_);
v___x_3106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v_c_3104_);
v___x_3108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Lean_MessageData_note(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_msg_3086_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
else
{
lean_object* v_val_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3166_; 
v_val_3113_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3115_ = v___x_3105_;
v_isShared_3116_ = v_isSharedCheck_3166_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_val_3113_);
lean_dec(v___x_3105_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3166_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v_modules_3118_; lean_object* v_moduleNames_3119_; lean_object* v_mod_3120_; uint8_t v___x_3135_; 
v___x_3117_ = l_Lean_Environment_header(v_env_3092_);
lean_dec_ref(v_env_3092_);
v_modules_3118_ = lean_ctor_get(v___x_3117_, 3);
lean_inc_ref(v_modules_3118_);
v_moduleNames_3119_ = lean_ctor_get(v___x_3117_, 4);
lean_inc_ref(v_moduleNames_3119_);
lean_dec_ref(v___x_3117_);
v_mod_3120_ = lean_array_get(v___x_3090_, v_moduleNames_3119_, v_val_3113_);
lean_dec_ref(v_moduleNames_3119_);
v___x_3135_ = l_Lean_isPrivateName(v_declHint_3087_);
lean_dec(v_declHint_3087_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = lean_array_get_size(v_modules_3118_);
v___x_3137_ = lean_nat_dec_lt(v_val_3113_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_dec_ref(v_modules_3118_);
lean_dec(v_val_3113_);
goto v___jp_3121_;
}
else
{
lean_object* v___x_3138_; lean_object* v_toImport_3139_; uint8_t v_isExported_3140_; 
v___x_3138_ = lean_array_fget(v_modules_3118_, v_val_3113_);
lean_dec(v_val_3113_);
lean_dec_ref(v_modules_3118_);
v_toImport_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_toImport_3139_);
lean_dec(v___x_3138_);
v_isExported_3140_ = lean_ctor_get_uint8(v_toImport_3139_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3139_);
if (v_isExported_3140_ == 0)
{
goto v___jp_3121_;
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_del_object(v___x_3115_);
v___x_3141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
lean_ctor_set(v___x_3142_, 1, v_c_3104_);
v___x_3143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_MessageData_ofName(v_mod_3120_);
lean_inc_ref(v___x_3145_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v___x_3145_);
v___x_3150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_3151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3149_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = l_Lean_MessageData_note(v___x_3151_);
v___x_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_msg_3086_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec_ref(v_modules_3118_);
lean_del_object(v___x_3115_);
lean_dec(v_val_3113_);
v___x_3155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v_c_3104_);
v___x_3157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_MessageData_ofName(v_mod_3120_);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_MessageData_note(v___x_3162_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_msg_3086_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
v___jp_3121_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v_c_3104_);
v___x_3124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_MessageData_ofName(v_mod_3120_);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_MessageData_note(v___x_3129_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_msg_3086_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set_tag(v___x_3115_, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3131_);
v___x_3133_ = v___x_3115_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
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
}
else
{
lean_object* v___x_3167_; 
lean_dec_ref(v_env_3092_);
lean_dec(v_declHint_3087_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_msg_3086_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_3168_, lean_object* v_declHint_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3168_, v_declHint_3169_, v___y_3170_);
lean_dec(v___y_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_3173_, lean_object* v_declHint_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3188_; 
v___x_3178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3173_, v_declHint_3174_, v___y_3176_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3188_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3188_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3183_ = l_Lean_unknownIdentifierMessageTag;
v___x_3184_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v_a_3179_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3184_);
v___x_3186_ = v___x_3181_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_3189_, lean_object* v_declHint_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3189_, v_declHint_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; lean_object* v_toCold_3200_; lean_object* v_env_3201_; lean_object* v_options_3202_; uint8_t v___x_3203_; lean_object* v_env_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3199_ = lean_st_ref_get(v___y_3197_);
v_toCold_3200_ = lean_ctor_get(v___y_3196_, 0);
v_env_3201_ = lean_ctor_get(v___x_3199_, 0);
lean_inc_ref(v_env_3201_);
lean_dec(v___x_3199_);
v_options_3202_ = lean_ctor_get(v_toCold_3200_, 2);
v___x_3203_ = 0;
v_env_3204_ = l_Lean_Environment_setRecordingDeps(v_env_3201_, v___x_3203_);
v___x_3205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_3206_ = lean_unsigned_to_nat(32u);
v___x_3207_ = lean_mk_empty_array_with_capacity(v___x_3206_);
lean_dec_ref(v___x_3207_);
v___x_3208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_3202_);
v___x_3209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3209_, 0, v_env_3204_);
lean_ctor_set(v___x_3209_, 1, v___x_3205_);
lean_ctor_set(v___x_3209_, 2, v___x_3208_);
lean_ctor_set(v___x_3209_, 3, v_options_3202_);
v___x_3210_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_msgData_3195_);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_ref_3221_; lean_object* v___x_3222_; lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3231_; 
v_ref_3221_ = lean_ctor_get(v___y_3218_, 2);
v___x_3222_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_3217_, v___y_3218_, v___y_3219_);
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_inc(v_ref_3221_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v_ref_3221_);
lean_ctor_set(v___x_3227_, 1, v_a_3223_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 1);
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3229_ = v___x_3225_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_3237_, lean_object* v_msg_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_toCold_3242_; lean_object* v_currRecDepth_3243_; lean_object* v_ref_3244_; uint16_t v_optionFlags_3245_; uint8_t v_suppressElabErrors_3246_; uint8_t v_checkDeprecated_3247_; uint8_t v_isRecordingDeps_3248_; lean_object* v_ref_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_toCold_3242_ = lean_ctor_get(v___y_3239_, 0);
v_currRecDepth_3243_ = lean_ctor_get(v___y_3239_, 1);
v_ref_3244_ = lean_ctor_get(v___y_3239_, 2);
v_optionFlags_3245_ = lean_ctor_get_uint16(v___y_3239_, sizeof(void*)*3);
v_suppressElabErrors_3246_ = lean_ctor_get_uint8(v___y_3239_, sizeof(void*)*3 + 2);
v_checkDeprecated_3247_ = lean_ctor_get_uint8(v___y_3239_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3248_ = lean_ctor_get_uint8(v___y_3239_, sizeof(void*)*3 + 4);
v_ref_3249_ = l_Lean_replaceRef(v_ref_3237_, v_ref_3244_);
lean_inc(v_currRecDepth_3243_);
lean_inc_ref(v_toCold_3242_);
v___x_3250_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3250_, 0, v_toCold_3242_);
lean_ctor_set(v___x_3250_, 1, v_currRecDepth_3243_);
lean_ctor_set(v___x_3250_, 2, v_ref_3249_);
lean_ctor_set_uint16(v___x_3250_, sizeof(void*)*3, v_optionFlags_3245_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*3 + 2, v_suppressElabErrors_3246_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*3 + 3, v_checkDeprecated_3247_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*3 + 4, v_isRecordingDeps_3248_);
v___x_3251_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3238_, v___x_3250_, v___y_3240_);
lean_dec_ref_known(v___x_3250_, 3);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_3252_, lean_object* v_msg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3252_, v_msg_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v_ref_3252_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_3258_, lean_object* v_msg_3259_, lean_object* v_declHint_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v___x_3266_; 
v___x_3264_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3259_, v_declHint_3260_, v___y_3261_, v___y_3262_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3258_, v_a_3265_, v___y_3261_, v___y_3262_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_3267_, lean_object* v_msg_3268_, lean_object* v_declHint_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3267_, v_msg_3268_, v_declHint_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v_ref_3267_);
return v_res_3273_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_3276_ = l_Lean_stringToMessageData(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_3279_ = l_Lean_stringToMessageData(v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3280_, lean_object* v_constName_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3285_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3286_ = 0;
lean_inc(v_constName_3281_);
v___x_3287_ = l_Lean_MessageData_ofConstName(v_constName_3281_, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3285_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3280_, v___x_3290_, v_constName_3281_, v___y_3282_, v___y_3283_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3292_, lean_object* v_constName_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3292_, v_constName_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v_ref_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_ref_3302_; lean_object* v___x_3303_; 
v_ref_3302_ = lean_ctor_get(v___y_3299_, 2);
v___x_3303_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3302_, v_constName_3298_, v___y_3299_, v___y_3300_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; lean_object* v_env_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; 
v___x_3313_ = lean_st_ref_get(v___y_3311_);
v_env_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc_ref(v_env_3314_);
lean_dec(v___x_3313_);
v___x_3315_ = 0;
lean_inc(v_constName_3309_);
v___x_3316_ = l_Lean_Environment_find_x3f(v_env_3314_, v_constName_3309_, v___x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3309_, v___y_3310_, v___y_3311_);
return v___x_3317_;
}
else
{
lean_object* v_val_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_constName_3309_);
v_val_3318_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3316_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_val_3318_);
lean_dec(v___x_3316_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 0);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Expr_getAppFn(v_type_3331_);
if (lean_obj_tag(v___x_3335_) == 4)
{
lean_object* v_declName_3336_; lean_object* v___x_3337_; 
v_declName_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_declName_3336_);
lean_dec_ref_known(v___x_3335_, 2);
v___x_3337_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_3336_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3355_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3355_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3355_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 5)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v_val_3342_ = lean_ctor_get(v_a_3338_, 0);
lean_inc_ref(v_val_3342_);
lean_dec_ref_known(v_a_3338_, 1);
v___x_3343_ = l_Lean_InductiveVal_numCtors(v_val_3342_);
lean_dec_ref(v_val_3342_);
v___x_3344_ = lean_unsigned_to_nat(1u);
v___x_3345_ = lean_nat_dec_le(v___x_3343_, v___x_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(v___x_3345_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3346_);
v___x_3348_ = v___x_3340_;
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
else
{
uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_dec(v_a_3338_);
v___x_3350_ = 0;
v___x_3351_ = lean_box(v___x_3350_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3351_);
v___x_3353_ = v___x_3340_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
v_a_3356_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3337_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3337_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v___x_3335_);
v___x_3364_ = 0;
v___x_3365_ = lean_box(v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec_ref(v_type_3367_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_3372_, lean_object* v_constName_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3373_, v___y_3374_, v___y_3375_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3378_, lean_object* v_constName_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_3378_, v_constName_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3384_, lean_object* v_ref_3385_, lean_object* v_constName_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3385_, v_constName_3386_, v___y_3387_, v___y_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3391_, lean_object* v_ref_3392_, lean_object* v_constName_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_3391_, v_ref_3392_, v_constName_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v_ref_3392_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3398_, lean_object* v_ref_3399_, lean_object* v_msg_3400_, lean_object* v_declHint_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3399_, v_msg_3400_, v_declHint_3401_, v___y_3402_, v___y_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_ref_3407_, lean_object* v_msg_3408_, lean_object* v_declHint_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3406_, v_ref_3407_, v_msg_3408_, v_declHint_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_ref_3407_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_3414_, lean_object* v_declHint_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3414_, v_declHint_3415_, v___y_3417_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_3420_, lean_object* v_declHint_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3420_, v_declHint_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3426_, lean_object* v_ref_3427_, lean_object* v_msg_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3427_, v_msg_3428_, v___y_3429_, v___y_3430_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3433_, lean_object* v_ref_3434_, lean_object* v_msg_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3433_, v_ref_3434_, v_msg_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v_ref_3434_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3440_, lean_object* v_msg_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3441_, v___y_3442_, v___y_3443_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3446_, lean_object* v_msg_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3446_, v_msg_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3452_, lean_object* v_fvarId_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_toGoalState_3459_; lean_object* v_mvarId_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3496_; 
v_toGoalState_3459_ = lean_ctor_get(v_goal_3452_, 0);
v_mvarId_3460_ = lean_ctor_get(v_goal_3452_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_goal_3452_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3462_ = v_goal_3452_;
v_isShared_3463_ = v_isSharedCheck_3496_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_mvarId_3460_);
lean_inc(v_toGoalState_3459_);
lean_dec(v_goal_3452_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3496_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3460_, v_fvarId_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3487_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3487_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3487_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
if (lean_obj_tag(v_a_3465_) == 1)
{
lean_object* v_val_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3482_; 
v_val_3469_ = lean_ctor_get(v_a_3465_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3471_ = v_a_3465_;
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_val_3469_);
lean_dec(v_a_3465_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v_val_3469_);
v___x_3474_ = v___x_3462_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_toGoalState_3459_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_val_3469_);
v___x_3474_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3474_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3476_);
v___x_3478_ = v___x_3467_;
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
lean_object* v___x_3483_; lean_object* v___x_3485_; 
lean_dec(v_a_3465_);
lean_del_object(v___x_3462_);
lean_dec_ref(v_toGoalState_3459_);
v___x_3483_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3483_);
v___x_3485_ = v___x_3467_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_del_object(v___x_3462_);
lean_dec_ref(v_toGoalState_3459_);
v_a_3488_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3464_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3464_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3497_, lean_object* v_fvarId_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3497_, v_fvarId_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3505_, lean_object* v_x_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3505_, v_x_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
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
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
v_a_3521_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3512_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3512_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3529_, lean_object* v_x_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3529_, v_x_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3537_, lean_object* v_mvarId_3538_, lean_object* v_x_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3538_, v_x_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_mvarId_3547_, lean_object* v_x_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3546_, v_mvarId_3547_, v_x_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3555_, lean_object* v_toGoalState_3556_, lean_object* v_goal_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
lean_inc(v_mvarId_3555_);
v___x_3563_ = l_Lean_MVarId_getType(v_mvarId_3555_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = l_Lean_Meta_isProp(v_a_3564_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3592_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3568_ = v___x_3565_;
v_isShared_3569_ = v_isSharedCheck_3592_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3565_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3592_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_unbox(v_a_3566_);
lean_dec(v_a_3566_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_del_object(v___x_3568_);
lean_dec_ref(v_goal_3557_);
v___x_3571_ = l_Lean_MVarId_exfalso(v_mvarId_3555_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3580_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3580_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v_toGoalState_3556_);
lean_ctor_set(v___x_3576_, 1, v_a_3572_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3578_ = v___x_3574_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_toGoalState_3556_);
v_a_3581_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3571_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3571_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v___x_3590_; 
lean_dec_ref(v_toGoalState_3556_);
lean_dec(v_mvarId_3555_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 0, v_goal_3557_);
v___x_3590_ = v___x_3568_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_goal_3557_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec_ref(v_goal_3557_);
lean_dec_ref(v_toGoalState_3556_);
lean_dec(v_mvarId_3555_);
v_a_3593_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3565_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3565_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v_goal_3557_);
lean_dec_ref(v_toGoalState_3556_);
lean_dec(v_mvarId_3555_);
v_a_3601_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3563_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3563_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3609_, lean_object* v_toGoalState_3610_, lean_object* v_goal_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3609_, v_toGoalState_3610_, v_goal_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_toGoalState_3624_; lean_object* v_mvarId_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; 
v_toGoalState_3624_ = lean_ctor_get(v_goal_3618_, 0);
lean_inc_ref(v_toGoalState_3624_);
v_mvarId_3625_ = lean_ctor_get(v_goal_3618_, 1);
lean_inc_n(v_mvarId_3625_, 2);
v___f_3626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3626_, 0, v_mvarId_3625_);
lean_closure_set(v___f_3626_, 1, v_toGoalState_3624_);
lean_closure_set(v___f_3626_, 2, v_goal_3618_);
v___x_3627_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3625_, v___f_3626_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object* v_toGoalState_3635_, lean_object* v_mvarId_3636_, lean_object* v_goal_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_mvarId_3649_; lean_object* v___x_3652_; 
lean_inc(v_mvarId_3636_);
v___x_3652_ = l_Lean_MVarId_getType(v_mvarId_3636_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc_n(v_a_3653_, 2);
lean_dec_ref_known(v___x_3652_, 1);
v___x_3654_ = l_Lean_Meta_Grind_simpCore(v_a_3653_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3686_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3686_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3686_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_expr_3659_; lean_object* v_proof_x3f_3660_; uint8_t v___x_3661_; 
v_expr_3659_ = lean_ctor_get(v_a_3655_, 0);
lean_inc_ref(v_expr_3659_);
v_proof_x3f_3660_ = lean_ctor_get(v_a_3655_, 1);
lean_inc(v_proof_x3f_3660_);
lean_dec(v_a_3655_);
v___x_3661_ = lean_expr_eqv(v_expr_3659_, v_a_3653_);
lean_dec(v_a_3653_);
if (v___x_3661_ == 0)
{
lean_del_object(v___x_3657_);
lean_dec_ref(v_goal_3637_);
if (lean_obj_tag(v_proof_x3f_3660_) == 0)
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_3636_, v_expr_3659_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_mvarId_3649_ = v_a_3663_;
goto v___jp_3648_;
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec_ref(v_toGoalState_3635_);
v_a_3664_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3662_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3662_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3673_; 
v_val_3672_ = lean_ctor_get(v_proof_x3f_3660_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_proof_x3f_3660_, 1);
v___x_3673_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_3636_, v_expr_3659_, v_val_3672_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v_mvarId_3649_ = v_a_3674_;
goto v___jp_3648_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v_toGoalState_3635_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3673_);
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
}
else
{
lean_object* v___x_3684_; 
lean_dec(v_proof_x3f_3660_);
lean_dec_ref(v_expr_3659_);
lean_dec(v_mvarId_3636_);
lean_dec_ref(v_toGoalState_3635_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_goal_3637_);
v___x_3684_ = v___x_3657_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_goal_3637_);
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
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3653_);
lean_dec_ref(v_goal_3637_);
lean_dec(v_mvarId_3636_);
lean_dec_ref(v_toGoalState_3635_);
v_a_3687_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3654_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3654_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v_goal_3637_);
lean_dec(v_mvarId_3636_);
lean_dec_ref(v_toGoalState_3635_);
v_a_3695_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3652_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3652_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
v___jp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_toGoalState_3635_);
lean_ctor_set(v___x_3650_, 1, v_mvarId_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object* v_toGoalState_3703_, lean_object* v_mvarId_3704_, lean_object* v_goal_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3703_, v_mvarId_3704_, v_goal_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object* v_goal_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v_toGoalState_3728_; lean_object* v_mvarId_3729_; lean_object* v___f_3730_; lean_object* v___x_3731_; 
v_toGoalState_3728_ = lean_ctor_get(v_goal_3717_, 0);
lean_inc_ref(v_toGoalState_3728_);
v_mvarId_3729_ = lean_ctor_get(v_goal_3717_, 1);
lean_inc_n(v_mvarId_3729_, 2);
v___f_3730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3730_, 0, v_toGoalState_3728_);
lean_closure_set(v___f_3730_, 1, v_mvarId_3729_);
lean_closure_set(v___f_3730_, 2, v_goal_3717_);
v___x_3731_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3729_, v___f_3730_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object* v_goal_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_mvarId_3750_; lean_object* v___x_3751_; 
v_mvarId_3750_ = lean_ctor_get(v_goal_3744_, 1);
lean_inc(v_mvarId_3750_);
lean_dec_ref(v_goal_3744_);
v___x_3751_ = l_Lean_MVarId_getDecl(v_mvarId_3750_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3761_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_lctx_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v_lctx_3756_ = lean_ctor_get(v_a_3752_, 1);
lean_inc_ref(v_lctx_3756_);
lean_dec(v_a_3752_);
v___x_3757_ = l_Lean_LocalContext_lastDecl(v_lctx_3756_);
lean_dec_ref(v_lctx_3756_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3757_);
v___x_3759_ = v___x_3754_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
v_a_3762_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3751_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3751_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_goal_3777_, lean_object* v_fvarId_3778_, lean_object* v_generation_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = lean_st_mk_ref(v_goal_3777_);
lean_inc(v_fvarId_3778_);
v___x_3791_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3778_, v_generation_3779_, v___x_3790_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v___x_3792_; 
lean_dec_ref_known(v___x_3791_, 1);
v___x_3792_ = l_Lean_FVarId_getType___redArg(v_fvarId_3778_, v___y_3785_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_a_3793_, v___x_3790_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3803_; 
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; 
v_unused_3804_ = lean_ctor_get(v___x_3794_, 0);
lean_dec(v_unused_3804_);
v___x_3796_ = v___x_3794_;
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
else
{
lean_dec(v___x_3794_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3798_ = lean_st_ref_get(v___x_3790_);
v___x_3799_ = lean_st_ref_get(v___x_3790_);
lean_dec(v___x_3790_);
lean_dec(v___x_3799_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3801_ = v___x_3796_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3798_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec(v___x_3790_);
v_a_3805_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3794_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3794_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v___x_3790_);
v_a_3813_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3792_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3792_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v___x_3790_);
lean_dec(v_fvarId_3778_);
v_a_3821_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3791_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3791_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_goal_3829_, lean_object* v_fvarId_3830_, lean_object* v_generation_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_goal_3829_, v_fvarId_3830_, v_generation_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3843_, lean_object* v_as_x27_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
if (lean_obj_tag(v_as_x27_3844_) == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref(v_kp_3843_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_b_3845_);
return v___x_3856_;
}
else
{
lean_object* v_head_3857_; lean_object* v_tail_3858_; lean_object* v_fst_3859_; lean_object* v_snd_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3886_; 
v_head_3857_ = lean_ctor_get(v_as_x27_3844_, 0);
v_tail_3858_ = lean_ctor_get(v_as_x27_3844_, 1);
v_fst_3859_ = lean_ctor_get(v_b_3845_, 0);
v_snd_3860_ = lean_ctor_get(v_b_3845_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_b_3845_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3862_ = v_b_3845_;
v_isShared_3863_ = v_isSharedCheck_3886_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_snd_3860_);
lean_inc(v_fst_3859_);
lean_dec(v_b_3845_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3886_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; 
lean_inc_ref(v_kp_3843_);
lean_inc(v___y_3854_);
lean_inc_ref(v___y_3853_);
lean_inc(v___y_3852_);
lean_inc_ref(v___y_3851_);
lean_inc(v___y_3850_);
lean_inc_ref(v___y_3849_);
lean_inc(v___y_3848_);
lean_inc_ref(v___y_3847_);
lean_inc(v___y_3846_);
lean_inc(v_head_3857_);
v___x_3864_ = lean_apply_11(v_kp_3843_, v_head_3857_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, lean_box(0));
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
if (lean_obj_tag(v_a_3865_) == 0)
{
lean_object* v_seq_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v_seq_3866_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_seq_3866_);
lean_dec_ref_known(v_a_3865_, 1);
v___x_3867_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3859_, v_seq_3866_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3867_);
v___x_3869_ = v___x_3862_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_snd_3860_);
v___x_3869_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
v_as_x27_3844_ = v_tail_3858_;
v_b_3845_ = v___x_3869_;
goto _start;
}
}
else
{
lean_object* v_gs_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
v_gs_3872_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_gs_3872_);
lean_dec_ref_known(v_a_3865_, 1);
v___x_3873_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3860_, v_gs_3872_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 1, v___x_3873_);
v___x_3875_ = v___x_3862_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_fst_3859_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
v_as_x27_3844_ = v_tail_3858_;
v_b_3845_ = v___x_3875_;
goto _start;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3862_);
lean_dec(v_snd_3860_);
lean_dec(v_fst_3859_);
lean_dec_ref(v_kp_3843_);
v_a_3878_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3864_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3864_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3887_, lean_object* v_as_x27_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3887_, v_as_x27_3888_, v_b_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_as_x27_3888_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v___x_3901_, uint8_t v___x_3902_, uint64_t v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
if (lean_obj_tag(v_a_3904_) == 0)
{
lean_object* v___x_3906_; 
lean_dec_ref(v___x_3901_);
v___x_3906_ = lean_array_to_list(v_a_3905_);
return v___x_3906_;
}
else
{
lean_object* v_ematch_3907_; lean_object* v_head_3908_; lean_object* v_tail_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3962_; 
v_ematch_3907_ = lean_ctor_get(v___x_3901_, 13);
lean_inc_ref(v_ematch_3907_);
v_head_3908_ = lean_ctor_get(v_a_3904_, 0);
v_tail_3909_ = lean_ctor_get(v_a_3904_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_a_3904_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3911_ = v_a_3904_;
v_isShared_3912_ = v_isSharedCheck_3962_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_tail_3909_);
lean_inc(v_head_3908_);
lean_dec(v_a_3904_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3962_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v_nextDeclIdx_3913_; lean_object* v_enodeMap_3914_; lean_object* v_exprs_3915_; lean_object* v_parents_3916_; lean_object* v_congrTable_3917_; lean_object* v_appMap_3918_; lean_object* v_indicesFound_3919_; lean_object* v_toProcess_3920_; lean_object* v_internalizing_3921_; lean_object* v_nextIdx_3922_; lean_object* v_newRawFacts_3923_; lean_object* v_facts_3924_; lean_object* v_extThms_3925_; lean_object* v_inj_3926_; lean_object* v_split_3927_; lean_object* v_clean_3928_; lean_object* v_sstates_3929_; lean_object* v_goalStack_3930_; uint64_t v_introBase_3931_; lean_object* v_numIntros_3932_; lean_object* v_thmMap_3933_; lean_object* v_gmt_3934_; lean_object* v_thms_3935_; lean_object* v_newThms_3936_; lean_object* v_numInstances_3937_; lean_object* v_numDelayedInstances_3938_; lean_object* v_preInstances_3939_; lean_object* v_nextThmIdx_3940_; lean_object* v_matchEqNames_3941_; lean_object* v_delayedThmInsts_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3960_; 
v_nextDeclIdx_3913_ = lean_ctor_get(v___x_3901_, 0);
v_enodeMap_3914_ = lean_ctor_get(v___x_3901_, 1);
v_exprs_3915_ = lean_ctor_get(v___x_3901_, 2);
v_parents_3916_ = lean_ctor_get(v___x_3901_, 3);
v_congrTable_3917_ = lean_ctor_get(v___x_3901_, 4);
v_appMap_3918_ = lean_ctor_get(v___x_3901_, 5);
v_indicesFound_3919_ = lean_ctor_get(v___x_3901_, 6);
v_toProcess_3920_ = lean_ctor_get(v___x_3901_, 7);
v_internalizing_3921_ = lean_ctor_get(v___x_3901_, 8);
v_nextIdx_3922_ = lean_ctor_get(v___x_3901_, 9);
v_newRawFacts_3923_ = lean_ctor_get(v___x_3901_, 10);
v_facts_3924_ = lean_ctor_get(v___x_3901_, 11);
v_extThms_3925_ = lean_ctor_get(v___x_3901_, 12);
v_inj_3926_ = lean_ctor_get(v___x_3901_, 14);
v_split_3927_ = lean_ctor_get(v___x_3901_, 15);
v_clean_3928_ = lean_ctor_get(v___x_3901_, 16);
v_sstates_3929_ = lean_ctor_get(v___x_3901_, 17);
v_goalStack_3930_ = lean_ctor_get(v___x_3901_, 18);
v_introBase_3931_ = lean_ctor_get_uint64(v___x_3901_, sizeof(void*)*20);
v_numIntros_3932_ = lean_ctor_get(v___x_3901_, 19);
v_thmMap_3933_ = lean_ctor_get(v_ematch_3907_, 0);
v_gmt_3934_ = lean_ctor_get(v_ematch_3907_, 1);
v_thms_3935_ = lean_ctor_get(v_ematch_3907_, 2);
v_newThms_3936_ = lean_ctor_get(v_ematch_3907_, 3);
v_numInstances_3937_ = lean_ctor_get(v_ematch_3907_, 4);
v_numDelayedInstances_3938_ = lean_ctor_get(v_ematch_3907_, 5);
v_preInstances_3939_ = lean_ctor_get(v_ematch_3907_, 7);
v_nextThmIdx_3940_ = lean_ctor_get(v_ematch_3907_, 8);
v_matchEqNames_3941_ = lean_ctor_get(v_ematch_3907_, 9);
v_delayedThmInsts_3942_ = lean_ctor_get(v_ematch_3907_, 10);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_ematch_3907_);
if (v_isSharedCheck_3960_ == 0)
{
lean_object* v_unused_3961_; 
v_unused_3961_ = lean_ctor_get(v_ematch_3907_, 6);
lean_dec(v_unused_3961_);
v___x_3944_ = v_ematch_3907_;
v_isShared_3945_ = v_isSharedCheck_3960_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_delayedThmInsts_3942_);
lean_inc(v_matchEqNames_3941_);
lean_inc(v_nextThmIdx_3940_);
lean_inc(v_preInstances_3939_);
lean_inc(v_numDelayedInstances_3938_);
lean_inc(v_numInstances_3937_);
lean_inc(v_newThms_3936_);
lean_inc(v_thms_3935_);
lean_inc(v_gmt_3934_);
lean_inc(v_thmMap_3933_);
lean_dec(v_ematch_3907_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3960_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3946_ = lean_array_get_size(v_a_3905_);
v___x_3947_ = lean_unsigned_to_nat(0u);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 6, v___x_3947_);
v___x_3949_ = v___x_3944_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_thmMap_3933_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_gmt_3934_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_thms_3935_);
lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_newThms_3936_);
lean_ctor_set(v_reuseFailAlloc_3959_, 4, v_numInstances_3937_);
lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_numDelayedInstances_3938_);
lean_ctor_set(v_reuseFailAlloc_3959_, 6, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3959_, 7, v_preInstances_3939_);
lean_ctor_set(v_reuseFailAlloc_3959_, 8, v_nextThmIdx_3940_);
lean_ctor_set(v_reuseFailAlloc_3959_, 9, v_matchEqNames_3941_);
lean_ctor_set(v_reuseFailAlloc_3959_, 10, v_delayedThmInsts_3942_);
v___x_3949_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_inc(v_numIntros_3932_);
lean_inc_ref(v_goalStack_3930_);
lean_inc_ref(v_sstates_3929_);
lean_inc_ref(v_clean_3928_);
lean_inc_ref(v_split_3927_);
lean_inc_ref(v_inj_3926_);
lean_inc_ref(v_extThms_3925_);
lean_inc_ref(v_facts_3924_);
lean_inc_ref(v_newRawFacts_3923_);
lean_inc(v_nextIdx_3922_);
lean_inc_ref(v_internalizing_3921_);
lean_inc_ref(v_toProcess_3920_);
lean_inc_ref(v_indicesFound_3919_);
lean_inc_ref(v_appMap_3918_);
lean_inc_ref(v_congrTable_3917_);
lean_inc_ref(v_parents_3916_);
lean_inc_ref(v_exprs_3915_);
lean_inc_ref(v_enodeMap_3914_);
lean_inc(v_nextDeclIdx_3913_);
v___x_3950_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_3950_, 0, v_nextDeclIdx_3913_);
lean_ctor_set(v___x_3950_, 1, v_enodeMap_3914_);
lean_ctor_set(v___x_3950_, 2, v_exprs_3915_);
lean_ctor_set(v___x_3950_, 3, v_parents_3916_);
lean_ctor_set(v___x_3950_, 4, v_congrTable_3917_);
lean_ctor_set(v___x_3950_, 5, v_appMap_3918_);
lean_ctor_set(v___x_3950_, 6, v_indicesFound_3919_);
lean_ctor_set(v___x_3950_, 7, v_toProcess_3920_);
lean_ctor_set(v___x_3950_, 8, v_internalizing_3921_);
lean_ctor_set(v___x_3950_, 9, v_nextIdx_3922_);
lean_ctor_set(v___x_3950_, 10, v_newRawFacts_3923_);
lean_ctor_set(v___x_3950_, 11, v_facts_3924_);
lean_ctor_set(v___x_3950_, 12, v_extThms_3925_);
lean_ctor_set(v___x_3950_, 13, v___x_3949_);
lean_ctor_set(v___x_3950_, 14, v_inj_3926_);
lean_ctor_set(v___x_3950_, 15, v_split_3927_);
lean_ctor_set(v___x_3950_, 16, v_clean_3928_);
lean_ctor_set(v___x_3950_, 17, v_sstates_3929_);
lean_ctor_set(v___x_3950_, 18, v_goalStack_3930_);
lean_ctor_set(v___x_3950_, 19, v_numIntros_3932_);
lean_ctor_set_uint8(v___x_3950_, sizeof(void*)*20 + 8, v___x_3902_);
lean_ctor_set_uint64(v___x_3950_, sizeof(void*)*20, v_introBase_3931_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set_tag(v___x_3911_, 0);
lean_ctor_set(v___x_3911_, 1, v_head_3908_);
lean_ctor_set(v___x_3911_, 0, v___x_3950_);
v___x_3952_ = v___x_3911_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_head_3908_);
v___x_3952_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
uint64_t v___x_3953_; uint64_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_uint64_of_nat(v___x_3946_);
v___x_3954_ = lean_uint64_mix_hash(v_a_3903_, v___x_3953_);
v___x_3955_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_3952_, v___x_3954_);
v___x_3956_ = lean_array_push(v_a_3905_, v___x_3955_);
v_a_3904_ = v_tail_3909_;
v_a_3905_ = v___x_3956_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v___x_3963_, lean_object* v___x_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
uint8_t v___x_45632__boxed_3968_; uint64_t v_a_45633__boxed_3969_; lean_object* v_res_3970_; 
v___x_45632__boxed_3968_ = lean_unbox(v___x_3964_);
v_a_45633__boxed_3969_ = lean_unbox_uint64(v_a_3965_);
lean_dec_ref(v_a_3965_);
v_res_3970_ = l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v___x_3963_, v___x_45632__boxed_3968_, v_a_45633__boxed_3969_, v_a_3966_, v_a_3967_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(lean_object* v_fvarId_3975_, lean_object* v_kp_3976_, lean_object* v_goal_3977_, lean_object* v_toGoalState_3978_, lean_object* v_mvarId_3979_, lean_object* v___f_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_goal_3992_; lean_object* v_toGoalState_3993_; lean_object* v_mvarId_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___x_4079_; 
lean_inc(v_fvarId_3975_);
v___x_4079_ = l_Lean_FVarId_getType___redArg(v_fvarId_3975_, v___y_3986_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
lean_inc(v___y_3989_);
lean_inc_ref(v___y_3988_);
lean_inc(v___y_3987_);
lean_inc_ref(v___y_3986_);
v___x_4081_ = lean_whnf(v_a_4080_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4184_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4184_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4184_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___x_4135_; 
v___x_4135_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_4082_, v___y_3982_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4175_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4175_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4175_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
uint8_t v___x_4140_; 
v___x_4140_ = lean_unbox(v_a_4136_);
lean_dec(v_a_4136_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
lean_del_object(v___x_4084_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v___x_4141_ = lean_box(0);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4141_);
v___x_4143_ = v___x_4138_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
else
{
lean_object* v___x_4145_; 
lean_del_object(v___x_4138_);
v___x_4145_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3982_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; uint8_t v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v___x_4147_ = lean_unbox(v_a_4146_);
lean_dec(v_a_4146_);
if (v___x_4147_ == 0)
{
v___y_4087_ = v___y_3981_;
v___y_4088_ = v___y_3982_;
v___y_4089_ = v___y_3983_;
v___y_4090_ = v___y_3984_;
v___y_4091_ = v___y_3985_;
v___y_4092_ = v___y_3986_;
v___y_4093_ = v___y_3987_;
v___y_4094_ = v___y_3988_;
v___y_4095_ = v___y_3989_;
goto v___jp_4086_;
}
else
{
lean_object* v___x_4148_; 
v___x_4148_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_4082_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4158_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4158_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4158_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
uint8_t v___x_4153_; 
v___x_4153_ = lean_unbox(v_a_4149_);
lean_dec(v_a_4149_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4156_; 
lean_del_object(v___x_4084_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v___x_4154_ = lean_box(0);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4154_);
v___x_4156_ = v___x_4151_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
else
{
lean_del_object(v___x_4151_);
v___y_4087_ = v___y_3981_;
v___y_4088_ = v___y_3982_;
v___y_4089_ = v___y_3983_;
v___y_4090_ = v___y_3984_;
v___y_4091_ = v___y_3985_;
v___y_4092_ = v___y_3986_;
v___y_4093_ = v___y_3987_;
v___y_4094_ = v___y_3988_;
v___y_4095_ = v___y_3989_;
goto v___jp_4086_;
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_del_object(v___x_4084_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4159_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4148_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4148_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_del_object(v___x_4084_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4167_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4145_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4145_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_del_object(v___x_4084_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4176_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4135_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4135_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
v___jp_4086_:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Expr_getAppFn(v_a_4082_);
if (lean_obj_tag(v___x_4096_) == 4)
{
lean_object* v_declName_4097_; lean_object* v___x_4098_; 
lean_del_object(v___x_4084_);
v_declName_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc_n(v_declName_4097_, 2);
lean_dec_ref_known(v___x_4096_, 2);
v___x_4098_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_4097_, v___y_4089_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v___x_4099_; 
lean_dec_ref_known(v___x_4098_, 1);
v___x_4099_ = l_Lean_Meta_isProp(v_a_4082_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; uint8_t v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_4097_);
lean_dec(v_declName_4097_);
if (v___x_4101_ == 0)
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_unbox(v_a_4100_);
lean_dec(v_a_4100_);
if (v___x_4102_ == 0)
{
lean_dec_ref(v___f_3980_);
v_goal_3992_ = v_goal_3977_;
v_toGoalState_3993_ = v_toGoalState_3978_;
v_mvarId_3994_ = v_mvarId_3979_;
v___y_3995_ = v___y_4087_;
v___y_3996_ = v___y_4088_;
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4092_;
v___y_4001_ = v___y_4093_;
v___y_4002_ = v___y_4094_;
v___y_4003_ = v___y_4095_;
goto v___jp_3991_;
}
else
{
lean_object* v___x_4103_; 
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
v___x_4103_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3979_, v___f_3980_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v_toGoalState_4105_; lean_object* v_mvarId_4106_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v_toGoalState_4105_ = lean_ctor_get(v_a_4104_, 0);
lean_inc_ref(v_toGoalState_4105_);
v_mvarId_4106_ = lean_ctor_get(v_a_4104_, 1);
lean_inc(v_mvarId_4106_);
v_goal_3992_ = v_a_4104_;
v_toGoalState_3993_ = v_toGoalState_4105_;
v_mvarId_3994_ = v_mvarId_4106_;
v___y_3995_ = v___y_4087_;
v___y_3996_ = v___y_4088_;
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4092_;
v___y_4001_ = v___y_4093_;
v___y_4002_ = v___y_4094_;
v___y_4003_ = v___y_4095_;
goto v___jp_3991_;
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4107_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4103_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4103_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
else
{
lean_dec(v_a_4100_);
lean_dec_ref(v___f_3980_);
v_goal_3992_ = v_goal_3977_;
v_toGoalState_3993_ = v_toGoalState_3978_;
v_mvarId_3994_ = v_mvarId_3979_;
v___y_3995_ = v___y_4087_;
v___y_3996_ = v___y_4088_;
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4092_;
v___y_4001_ = v___y_4093_;
v___y_4002_ = v___y_4094_;
v___y_4003_ = v___y_4095_;
goto v___jp_3991_;
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_declName_4097_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4115_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4099_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4099_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_declName_4097_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4123_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4098_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4098_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
lean_dec_ref(v___x_4096_);
lean_dec(v_a_4082_);
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v___x_4131_ = lean_box(0);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4131_);
v___x_4133_ = v___x_4084_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4185_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4081_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4081_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec_ref(v___f_3980_);
lean_dec(v_mvarId_3979_);
lean_dec_ref(v_toGoalState_3978_);
lean_dec_ref(v_goal_3977_);
lean_dec_ref(v_kp_3976_);
lean_dec(v_fvarId_3975_);
v_a_4193_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4079_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4079_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
v___jp_3991_:
{
uint8_t v_inconsistent_4004_; 
v_inconsistent_4004_ = lean_ctor_get_uint8(v_toGoalState_3993_, sizeof(void*)*20 + 8);
if (v_inconsistent_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
lean_dec_ref(v_goal_3992_);
v___x_4005_ = l_Lean_mkFVar(v_fvarId_3975_);
lean_inc_ref(v___x_4005_);
v___x_4006_ = l_Lean_Meta_Grind_cases(v_mvarId_3994_, v___x_4005_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4008_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = l_Lean_Meta_Grind_getAnchor(v___x_4005_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; uint64_t v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = lean_unsigned_to_nat(0u);
v___x_4011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0));
v___x_4012_ = lean_unbox_uint64(v_a_4009_);
lean_dec(v_a_4009_);
v___x_4013_ = l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_toGoalState_3993_, v_inconsistent_4004_, v___x_4012_, v_a_4007_, v___x_4011_);
v___x_4014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1));
v___x_4015_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3976_, v___x_4013_, v___x_4014_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___x_4013_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4036_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4036_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4036_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_fst_4020_; lean_object* v_snd_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_fst_4020_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_fst_4020_);
v_snd_4021_ = lean_ctor_get(v_a_4016_, 1);
lean_inc(v_snd_4021_);
lean_dec(v_a_4016_);
v___x_4022_ = lean_array_get_size(v_snd_4021_);
v___x_4023_ = lean_nat_dec_eq(v___x_4022_, v___x_4010_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
lean_dec(v_fst_4020_);
v___x_4024_ = lean_array_to_list(v_snd_4021_);
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
v___x_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4026_);
v___x_4028_ = v___x_4018_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
lean_dec(v_snd_4021_);
v___x_4030_ = lean_array_to_list(v_fst_4020_);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4032_);
v___x_4034_ = v___x_4018_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4015_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4015_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_a_4007_);
lean_dec_ref(v_toGoalState_3993_);
lean_dec_ref(v_kp_3976_);
v_a_4045_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4008_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4008_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v___x_4005_);
lean_dec_ref(v_toGoalState_3993_);
lean_dec_ref(v_kp_3976_);
v_a_4053_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4006_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4006_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_object* v___x_4061_; 
lean_dec(v_mvarId_3994_);
lean_dec_ref(v_toGoalState_3993_);
lean_dec(v_fvarId_3975_);
lean_inc(v___y_4003_);
lean_inc_ref(v___y_4002_);
lean_inc(v___y_4001_);
lean_inc_ref(v___y_4000_);
lean_inc(v___y_3999_);
lean_inc_ref(v___y_3998_);
lean_inc(v___y_3997_);
lean_inc_ref(v___y_3996_);
lean_inc(v___y_3995_);
v___x_4061_ = lean_apply_11(v_kp_3976_, v_goal_3992_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, lean_box(0));
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4070_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4070_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_a_4062_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v___x_4066_);
v___x_4068_ = v___x_4064_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
v_a_4071_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4061_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4061_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed(lean_object* v_fvarId_4201_, lean_object* v_kp_4202_, lean_object* v_goal_4203_, lean_object* v_toGoalState_4204_, lean_object* v_mvarId_4205_, lean_object* v___f_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(v_fvarId_4201_, v_kp_4202_, v_goal_4203_, v_toGoalState_4204_, v_mvarId_4205_, v___f_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_4218_, lean_object* v_fvarId_4219_, lean_object* v_generation_4220_, lean_object* v_kp_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_toGoalState_4232_; lean_object* v_mvarId_4233_; lean_object* v___f_4234_; lean_object* v___f_4235_; lean_object* v___x_4236_; 
v_toGoalState_4232_ = lean_ctor_get(v_goal_4218_, 0);
lean_inc_ref(v_toGoalState_4232_);
v_mvarId_4233_ = lean_ctor_get(v_goal_4218_, 1);
lean_inc_n(v_mvarId_4233_, 2);
lean_inc(v_fvarId_4219_);
lean_inc_ref(v_goal_4218_);
v___f_4234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4234_, 0, v_goal_4218_);
lean_closure_set(v___f_4234_, 1, v_fvarId_4219_);
lean_closure_set(v___f_4234_, 2, v_generation_4220_);
v___f_4235_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed), 16, 6);
lean_closure_set(v___f_4235_, 0, v_fvarId_4219_);
lean_closure_set(v___f_4235_, 1, v_kp_4221_);
lean_closure_set(v___f_4235_, 2, v_goal_4218_);
lean_closure_set(v___f_4235_, 3, v_toGoalState_4232_);
lean_closure_set(v___f_4235_, 4, v_mvarId_4233_);
lean_closure_set(v___f_4235_, 5, v___f_4234_);
v___x_4236_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4233_, v___f_4235_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_4237_, lean_object* v_fvarId_4238_, lean_object* v_generation_4239_, lean_object* v_kp_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4237_, v_fvarId_4238_, v_generation_4239_, v_kp_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_4252_, lean_object* v_as_4253_, lean_object* v_as_x27_4254_, lean_object* v_b_4255_, lean_object* v_a_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_4252_, v_as_x27_4254_, v_b_4255_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_4268_, lean_object* v_as_4269_, lean_object* v_as_x27_4270_, lean_object* v_b_4271_, lean_object* v_a_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_4268_, v_as_4269_, v_as_x27_4270_, v_b_4271_, v_a_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec(v_as_x27_4270_);
lean_dec(v_as_4269_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_4284_, lean_object* v_fvarId_4285_, lean_object* v_generation_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_st_mk_ref(v_goal_4284_);
v___x_4298_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_4285_, v_generation_4286_, v___x_4297_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4307_; 
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4307_ == 0)
{
lean_object* v_unused_4308_; 
v_unused_4308_ = lean_ctor_get(v___x_4298_, 0);
lean_dec(v_unused_4308_);
v___x_4300_ = v___x_4298_;
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
else
{
lean_dec(v___x_4298_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4302_ = lean_st_ref_get(v___x_4297_);
v___x_4303_ = lean_st_ref_get(v___x_4297_);
lean_dec(v___x_4297_);
lean_dec(v___x_4303_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4302_);
v___x_4305_ = v___x_4300_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4302_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec(v___x_4297_);
v_a_4309_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4298_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4298_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_4317_, lean_object* v_fvarId_4318_, lean_object* v_generation_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_4317_, v_fvarId_4318_, v_generation_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_4333_, lean_object* v_goal_4334_, lean_object* v_kna_4335_, lean_object* v_kp_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_toGoalState_4347_; uint8_t v_inconsistent_4348_; 
v_toGoalState_4347_ = lean_ctor_get(v_goal_4334_, 0);
v_inconsistent_4348_ = lean_ctor_get_uint8(v_toGoalState_4347_, sizeof(void*)*20 + 8);
if (v_inconsistent_4348_ == 0)
{
lean_object* v_mvarId_4349_; lean_object* v___x_4350_; 
v_mvarId_4349_ = lean_ctor_get(v_goal_4334_, 1);
lean_inc(v_mvarId_4349_);
v___x_4350_ = l_Lean_MVarId_getType(v_mvarId_4349_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; uint8_t v___x_4352_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = l_Lean_Expr_isFalse(v_a_4351_);
lean_dec(v_a_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
lean_dec_ref(v_kna_4335_);
lean_inc(v_generation_4333_);
v___x_4353_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_4334_, v_generation_4333_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
switch(lean_obj_tag(v_a_4354_))
{
case 0:
{
lean_object* v_goal_4355_; lean_object* v___x_4356_; 
lean_dec(v_generation_4333_);
v_goal_4355_ = lean_ctor_get(v_a_4354_, 0);
lean_inc_ref(v_goal_4355_);
lean_dec_ref_known(v_a_4354_, 1);
v___x_4356_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_4355_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v___x_4358_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_a_4357_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v_toGoalState_4360_; lean_object* v_mvarId_4361_; lean_object* v___x_4362_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v_toGoalState_4360_ = lean_ctor_get(v_a_4359_, 0);
v_mvarId_4361_ = lean_ctor_get(v_a_4359_, 1);
lean_inc(v_mvarId_4361_);
v___x_4362_ = l_Lean_MVarId_getType(v_mvarId_4361_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; uint8_t v___x_4364_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v___x_4364_ = l_Lean_Expr_isForall(v_a_4363_);
if (v___x_4364_ == 0)
{
uint8_t v___x_4365_; 
v___x_4365_ = l_Lean_Expr_isLet(v_a_4363_);
lean_dec(v_a_4363_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_inc(v_mvarId_4361_);
v___x_4366_ = l_Lean_MVarId_byContra_x3f(v_mvarId_4361_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4367_);
lean_dec_ref_known(v___x_4366_, 1);
if (lean_obj_tag(v_a_4367_) == 1)
{
lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4376_; 
lean_inc_ref(v_toGoalState_4360_);
v_isSharedCheck_4376_ = !lean_is_exclusive(v_a_4359_);
if (v_isSharedCheck_4376_ == 0)
{
lean_object* v_unused_4377_; lean_object* v_unused_4378_; 
v_unused_4377_ = lean_ctor_get(v_a_4359_, 1);
lean_dec(v_unused_4377_);
v_unused_4378_ = lean_ctor_get(v_a_4359_, 0);
lean_dec(v_unused_4378_);
v___x_4369_ = v_a_4359_;
v_isShared_4370_ = v_isSharedCheck_4376_;
goto v_resetjp_4368_;
}
else
{
lean_dec(v_a_4359_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4376_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_val_4371_; lean_object* v___x_4373_; 
v_val_4371_ = lean_ctor_get(v_a_4367_, 0);
lean_inc(v_val_4371_);
lean_dec_ref_known(v_a_4367_, 1);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v_val_4371_);
v___x_4373_ = v___x_4369_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_toGoalState_4360_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_val_4371_);
v___x_4373_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4374_; 
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4374_ = lean_apply_11(v_kp_4336_, v___x_4373_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4374_;
}
}
}
else
{
lean_object* v___x_4379_; 
lean_dec(v_a_4367_);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4379_ = lean_apply_11(v_kp_4336_, v_a_4359_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4379_;
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4359_);
lean_dec_ref(v_kp_4336_);
v_a_4380_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4366_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4366_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v___x_4388_; 
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4388_ = lean_apply_11(v_kp_4336_, v_a_4359_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4388_;
}
}
else
{
lean_object* v___x_4389_; 
lean_dec(v_a_4363_);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4389_ = lean_apply_11(v_kp_4336_, v_a_4359_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4389_;
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_a_4359_);
lean_dec_ref(v_kp_4336_);
v_a_4390_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4362_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4362_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
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
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec_ref(v_kp_4336_);
v_a_4398_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4358_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4358_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec_ref(v_kp_4336_);
v_a_4406_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4356_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4356_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4414_; lean_object* v_goal_4415_; lean_object* v___f_4416_; lean_object* v___x_4417_; 
v_fvarId_4414_ = lean_ctor_get(v_a_4354_, 0);
lean_inc_n(v_fvarId_4414_, 3);
v_goal_4415_ = lean_ctor_get(v_a_4354_, 1);
lean_inc_ref_n(v_goal_4415_, 3);
lean_dec_ref_known(v_a_4354_, 2);
lean_inc(v_generation_4333_);
v___f_4416_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4416_, 0, v_goal_4415_);
lean_closure_set(v___f_4416_, 1, v_fvarId_4414_);
lean_closure_set(v___f_4416_, 2, v_generation_4333_);
v___x_4417_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_4415_, v_fvarId_4414_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
if (lean_obj_tag(v_a_4418_) == 1)
{
lean_object* v_val_4419_; lean_object* v___x_4420_; 
lean_dec_ref(v___f_4416_);
lean_dec_ref(v_goal_4415_);
lean_dec(v_fvarId_4414_);
lean_dec(v_generation_4333_);
v_val_4419_ = lean_ctor_get(v_a_4418_, 0);
lean_inc(v_val_4419_);
lean_dec_ref_known(v_a_4418_, 1);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4420_ = lean_apply_11(v_kp_4336_, v_val_4419_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4420_;
}
else
{
lean_object* v___x_4421_; 
lean_dec(v_a_4418_);
lean_inc_ref(v_kp_4336_);
lean_inc_ref(v_goal_4415_);
v___x_4421_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4415_, v_fvarId_4414_, v_generation_4333_, v_kp_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4442_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4442_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4442_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
if (lean_obj_tag(v_a_4422_) == 1)
{
lean_object* v_val_4426_; lean_object* v___x_4428_; 
lean_dec_ref(v___f_4416_);
lean_dec_ref(v_goal_4415_);
lean_dec_ref(v_kp_4336_);
v_val_4426_ = lean_ctor_get(v_a_4422_, 0);
lean_inc(v_val_4426_);
lean_dec_ref_known(v_a_4422_, 1);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v_val_4426_);
v___x_4428_ = v___x_4424_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_val_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
else
{
lean_object* v_mvarId_4430_; lean_object* v___x_4431_; 
lean_del_object(v___x_4424_);
lean_dec(v_a_4422_);
v_mvarId_4430_ = lean_ctor_get(v_goal_4415_, 1);
lean_inc(v_mvarId_4430_);
lean_dec_ref(v_goal_4415_);
v___x_4431_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4430_, v___f_4416_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4433_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref_known(v___x_4431_, 1);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4433_ = lean_apply_11(v_kp_4336_, v_a_4432_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4433_;
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v_kp_4336_);
v_a_4434_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4431_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4431_);
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
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec_ref(v___f_4416_);
lean_dec_ref(v_goal_4415_);
lean_dec_ref(v_kp_4336_);
v_a_4443_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4421_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4421_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec_ref(v___f_4416_);
lean_dec_ref(v_goal_4415_);
lean_dec(v_fvarId_4414_);
lean_dec_ref(v_kp_4336_);
lean_dec(v_generation_4333_);
v_a_4451_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4417_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4417_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
case 2:
{
lean_object* v_goal_4459_; lean_object* v___x_4460_; 
lean_dec(v_generation_4333_);
v_goal_4459_ = lean_ctor_get(v_a_4354_, 0);
lean_inc_ref(v_goal_4459_);
lean_dec_ref_known(v_a_4354_, 1);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4460_ = lean_apply_11(v_kp_4336_, v_goal_4459_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4460_;
}
default: 
{
lean_object* v_fvarId_4461_; lean_object* v_goal_4462_; lean_object* v___x_4463_; 
v_fvarId_4461_ = lean_ctor_get(v_a_4354_, 0);
lean_inc(v_fvarId_4461_);
v_goal_4462_ = lean_ctor_get(v_a_4354_, 1);
lean_inc_ref_n(v_goal_4462_, 2);
lean_dec_ref_known(v_a_4354_, 2);
lean_inc_ref(v_kp_4336_);
v___x_4463_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4462_, v_fvarId_4461_, v_generation_4333_, v_kp_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4473_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4466_ = v___x_4463_;
v_isShared_4467_ = v_isSharedCheck_4473_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4463_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4473_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
if (lean_obj_tag(v_a_4464_) == 1)
{
lean_object* v_val_4468_; lean_object* v___x_4470_; 
lean_dec_ref(v_goal_4462_);
lean_dec_ref(v_kp_4336_);
v_val_4468_ = lean_ctor_get(v_a_4464_, 0);
lean_inc(v_val_4468_);
lean_dec_ref_known(v_a_4464_, 1);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 0, v_val_4468_);
v___x_4470_ = v___x_4466_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_val_4468_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
else
{
lean_object* v___x_4472_; 
lean_del_object(v___x_4466_);
lean_dec(v_a_4464_);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4472_ = lean_apply_11(v_kp_4336_, v_goal_4462_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4472_;
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref(v_goal_4462_);
lean_dec_ref(v_kp_4336_);
v_a_4474_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4463_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4463_);
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
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v_kp_4336_);
lean_dec(v_generation_4333_);
v_a_4482_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4353_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4353_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v___x_4490_; 
lean_dec_ref(v_kp_4336_);
lean_dec(v_generation_4333_);
lean_inc(v_a_4345_);
lean_inc_ref(v_a_4344_);
lean_inc(v_a_4343_);
lean_inc_ref(v_a_4342_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
v___x_4490_ = lean_apply_11(v_kna_4335_, v_goal_4334_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, lean_box(0));
return v___x_4490_;
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec_ref(v_kp_4336_);
lean_dec_ref(v_kna_4335_);
lean_dec_ref(v_goal_4334_);
lean_dec(v_generation_4333_);
v_a_4491_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4350_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4350_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
lean_dec_ref(v_kp_4336_);
lean_dec_ref(v_kna_4335_);
lean_dec_ref(v_goal_4334_);
lean_dec(v_generation_4333_);
v___x_4499_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_4501_, lean_object* v_goal_4502_, lean_object* v_kna_4503_, lean_object* v_kp_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Lean_Meta_Grind_Action_intro(v_generation_4501_, v_goal_4502_, v_kna_4503_, v_kp_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
return v_res_4515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = lean_unsigned_to_nat(1000000u);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_4517_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4532_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_4545_, lean_object* v___f_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4560_ = lean_unsigned_to_nat(1000000u);
v___x_4561_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_4561_, 0, v_generation_4545_);
v___x_4562_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_4562_, 0, v___x_4560_);
lean_closure_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l_Lean_Meta_Grind_Action_andThen(v___x_4562_, v___f_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_4564_, lean_object* v___f_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_4564_, v___f_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_4582_, lean_object* v_a_4583_, lean_object* v_kna_4584_, lean_object* v_kp_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v___f_4596_; lean_object* v___f_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___f_4596_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_4597_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4597_, 0, v_generation_4582_);
lean_closure_set(v___f_4597_, 1, v___f_4596_);
v___x_4598_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_4599_ = l_Lean_Meta_Grind_Action_andThen(v___x_4598_, v___f_4597_, v_a_4583_, v_kna_4584_, v_kp_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_4600_, lean_object* v_a_4601_, lean_object* v_kna_4602_, lean_object* v_kp_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Meta_Grind_Action_intros(v_generation_4600_, v_a_4601_, v_kna_4602_, v_kp_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
return v_res_4614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_4623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_4624_ = l_Lean_mkConst(v___x_4623_, v___x_4622_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_4625_, lean_object* v_prop_4626_, lean_object* v_proof_4627_, lean_object* v_generation_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_st_mk_ref(v_goal_4625_);
lean_inc(v___y_4637_);
lean_inc_ref(v___y_4636_);
lean_inc(v___y_4635_);
lean_inc_ref(v___y_4634_);
lean_inc(v___y_4633_);
lean_inc_ref(v___y_4632_);
lean_inc(v___y_4631_);
lean_inc_ref(v___y_4630_);
lean_inc(v___y_4629_);
lean_inc(v___x_4639_);
lean_inc_ref(v_prop_4626_);
v___x_4640_ = lean_grind_preprocess(v_prop_4626_, v___x_4639_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_expr_4642_; lean_object* v___x_4643_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v___x_4640_, 1);
v_expr_4642_ = lean_ctor_get(v_a_4641_, 0);
lean_inc_ref(v_expr_4642_);
v___x_4643_ = l_Lean_Meta_Simp_Result_getProof(v_a_4641_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
v___x_4645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4642_);
v___x_4646_ = l_Lean_mkApp4(v___x_4645_, v_prop_4626_, v_expr_4642_, v_a_4644_, v_proof_4627_);
v___x_4647_ = l_Lean_Meta_Grind_add(v_expr_4642_, v___x_4646_, v_generation_4628_, v___x_4639_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4656_; 
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4656_ == 0)
{
lean_object* v_unused_4657_; 
v_unused_4657_ = lean_ctor_get(v___x_4647_, 0);
lean_dec(v_unused_4657_);
v___x_4649_ = v___x_4647_;
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
else
{
lean_dec(v___x_4647_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4656_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4654_; 
v___x_4651_ = lean_st_ref_get(v___x_4639_);
v___x_4652_ = lean_st_ref_get(v___x_4639_);
lean_dec(v___x_4639_);
lean_dec(v___x_4652_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 0, v___x_4651_);
v___x_4654_ = v___x_4649_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4651_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec(v___x_4639_);
v_a_4658_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4647_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4647_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec_ref(v_expr_4642_);
lean_dec(v___x_4639_);
lean_dec(v_generation_4628_);
lean_dec_ref(v_proof_4627_);
lean_dec_ref(v_prop_4626_);
v_a_4666_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4643_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4643_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v___x_4639_);
lean_dec(v_generation_4628_);
lean_dec_ref(v_proof_4627_);
lean_dec_ref(v_prop_4626_);
v_a_4674_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4640_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4640_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4682_, lean_object* v_prop_4683_, lean_object* v_proof_4684_, lean_object* v_generation_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4682_, v_prop_4683_, v_proof_4684_, v_generation_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_goal_4697_, lean_object* v___f_4698_, lean_object* v_kp_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_mvarId_4710_; lean_object* v___x_4711_; 
v_mvarId_4710_ = lean_ctor_get(v_goal_4697_, 1);
lean_inc(v_mvarId_4710_);
lean_dec_ref(v_goal_4697_);
v___x_4711_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4710_, v___f_4698_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4713_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4711_, 1);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
lean_inc(v___y_4706_);
lean_inc_ref(v___y_4705_);
lean_inc(v___y_4704_);
lean_inc_ref(v___y_4703_);
lean_inc(v___y_4702_);
lean_inc_ref(v___y_4701_);
lean_inc(v___y_4700_);
v___x_4713_ = lean_apply_11(v_kp_4699_, v_a_4712_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, lean_box(0));
return v___x_4713_;
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec_ref(v_kp_4699_);
v_a_4714_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4711_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4711_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_goal_4722_, lean_object* v___f_4723_, lean_object* v_kp_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4722_, v___f_4723_, v_kp_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4736_, lean_object* v_prop_4737_, lean_object* v_generation_4738_, lean_object* v_goal_4739_, lean_object* v_kna_4740_, lean_object* v_kp_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v___f_4752_; lean_object* v___f_4753_; lean_object* v___x_4754_; 
lean_inc(v_generation_4738_);
lean_inc_ref(v_proof_4736_);
lean_inc_ref(v_prop_4737_);
lean_inc_ref_n(v_goal_4739_, 2);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4752_, 0, v_goal_4739_);
lean_closure_set(v___f_4752_, 1, v_prop_4737_);
lean_closure_set(v___f_4752_, 2, v_proof_4736_);
lean_closure_set(v___f_4752_, 3, v_generation_4738_);
lean_inc_ref(v_kp_4741_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4753_, 0, v_goal_4739_);
lean_closure_set(v___f_4753_, 1, v___f_4752_);
lean_closure_set(v___f_4753_, 2, v_kp_4741_);
v___x_4754_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4737_, v_a_4743_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; uint8_t v___x_4756_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v___x_4756_ = lean_unbox(v_a_4755_);
lean_dec(v_a_4755_);
if (v___x_4756_ == 0)
{
lean_object* v_mvarId_4757_; lean_object* v___x_4758_; 
lean_dec_ref(v_kp_4741_);
lean_dec_ref(v_kna_4740_);
lean_dec(v_generation_4738_);
lean_dec_ref(v_prop_4737_);
lean_dec_ref(v_proof_4736_);
v_mvarId_4757_ = lean_ctor_get(v_goal_4739_, 1);
lean_inc(v_mvarId_4757_);
lean_dec_ref(v_goal_4739_);
v___x_4758_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4757_, v___f_4753_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4758_;
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec_ref(v___f_4753_);
v___x_4759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4760_ = l_Lean_Core_mkFreshUserName(v___x_4759_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v_toGoalState_4762_; lean_object* v_mvarId_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4794_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v_toGoalState_4762_ = lean_ctor_get(v_goal_4739_, 0);
v_mvarId_4763_ = lean_ctor_get(v_goal_4739_, 1);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_goal_4739_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4765_ = v_goal_4739_;
v_isShared_4766_ = v_isSharedCheck_4794_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_mvarId_4763_);
lean_inc(v_toGoalState_4762_);
lean_dec(v_goal_4739_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4794_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4767_; 
lean_inc_ref(v_prop_4737_);
lean_inc(v_mvarId_4763_);
v___x_4767_ = l_Lean_MVarId_assert(v_mvarId_4763_, v_a_4761_, v_prop_4737_, v_proof_4736_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_object* v_a_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v___x_4767_, 1);
v___x_4769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_4769_, 0, v_prop_4737_);
v___x_4770_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4763_, v___x_4769_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4770_, 1);
if (v_isShared_4766_ == 0)
{
lean_ctor_set(v___x_4765_, 1, v_a_4768_);
v___x_4773_ = v___x_4765_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_toGoalState_4762_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
uint64_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4774_ = lean_unbox_uint64(v_a_4771_);
lean_dec(v_a_4771_);
v___x_4775_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_4773_, v___x_4774_);
v___x_4776_ = l_Lean_Meta_Grind_Action_intros(v_generation_4738_, v___x_4775_, v_kna_4740_, v_kp_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4776_;
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec(v_a_4768_);
lean_del_object(v___x_4765_);
lean_dec_ref(v_toGoalState_4762_);
lean_dec_ref(v_kp_4741_);
lean_dec_ref(v_kna_4740_);
lean_dec(v_generation_4738_);
v_a_4778_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4770_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4770_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_del_object(v___x_4765_);
lean_dec(v_mvarId_4763_);
lean_dec_ref(v_toGoalState_4762_);
lean_dec_ref(v_kp_4741_);
lean_dec_ref(v_kna_4740_);
lean_dec(v_generation_4738_);
lean_dec_ref(v_prop_4737_);
v_a_4786_ = lean_ctor_get(v___x_4767_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4767_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4767_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_kp_4741_);
lean_dec_ref(v_kna_4740_);
lean_dec_ref(v_goal_4739_);
lean_dec(v_generation_4738_);
lean_dec_ref(v_prop_4737_);
lean_dec_ref(v_proof_4736_);
v_a_4795_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4760_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4760_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v___f_4753_);
lean_dec_ref(v_kp_4741_);
lean_dec_ref(v_kna_4740_);
lean_dec_ref(v_goal_4739_);
lean_dec(v_generation_4738_);
lean_dec_ref(v_prop_4737_);
lean_dec_ref(v_proof_4736_);
v_a_4803_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4754_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4754_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4811_, lean_object* v_prop_4812_, lean_object* v_generation_4813_, lean_object* v_goal_4814_, lean_object* v_kna_4815_, lean_object* v_kp_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4811_, v_prop_4812_, v_generation_4813_, v_goal_4814_, v_kna_4815_, v_kp_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4828_, lean_object* v_kna_4829_, lean_object* v_kp_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_toGoalState_4841_; uint8_t v_inconsistent_4842_; 
v_toGoalState_4841_ = lean_ctor_get(v_goal_4828_, 0);
lean_inc_ref(v_toGoalState_4841_);
v_inconsistent_4842_ = lean_ctor_get_uint8(v_toGoalState_4841_, sizeof(void*)*20 + 8);
if (v_inconsistent_4842_ == 0)
{
lean_object* v_mvarId_4843_; lean_object* v_nextDeclIdx_4844_; lean_object* v_enodeMap_4845_; lean_object* v_exprs_4846_; lean_object* v_parents_4847_; lean_object* v_congrTable_4848_; lean_object* v_appMap_4849_; lean_object* v_indicesFound_4850_; lean_object* v_toProcess_4851_; lean_object* v_internalizing_4852_; lean_object* v_nextIdx_4853_; lean_object* v_newRawFacts_4854_; lean_object* v_facts_4855_; lean_object* v_extThms_4856_; lean_object* v_ematch_4857_; lean_object* v_inj_4858_; lean_object* v_split_4859_; lean_object* v_clean_4860_; lean_object* v_sstates_4861_; lean_object* v_goalStack_4862_; uint64_t v_introBase_4863_; lean_object* v_numIntros_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4907_; 
v_mvarId_4843_ = lean_ctor_get(v_goal_4828_, 1);
v_nextDeclIdx_4844_ = lean_ctor_get(v_toGoalState_4841_, 0);
v_enodeMap_4845_ = lean_ctor_get(v_toGoalState_4841_, 1);
v_exprs_4846_ = lean_ctor_get(v_toGoalState_4841_, 2);
v_parents_4847_ = lean_ctor_get(v_toGoalState_4841_, 3);
v_congrTable_4848_ = lean_ctor_get(v_toGoalState_4841_, 4);
v_appMap_4849_ = lean_ctor_get(v_toGoalState_4841_, 5);
v_indicesFound_4850_ = lean_ctor_get(v_toGoalState_4841_, 6);
v_toProcess_4851_ = lean_ctor_get(v_toGoalState_4841_, 7);
v_internalizing_4852_ = lean_ctor_get(v_toGoalState_4841_, 8);
v_nextIdx_4853_ = lean_ctor_get(v_toGoalState_4841_, 9);
v_newRawFacts_4854_ = lean_ctor_get(v_toGoalState_4841_, 10);
v_facts_4855_ = lean_ctor_get(v_toGoalState_4841_, 11);
v_extThms_4856_ = lean_ctor_get(v_toGoalState_4841_, 12);
v_ematch_4857_ = lean_ctor_get(v_toGoalState_4841_, 13);
v_inj_4858_ = lean_ctor_get(v_toGoalState_4841_, 14);
v_split_4859_ = lean_ctor_get(v_toGoalState_4841_, 15);
v_clean_4860_ = lean_ctor_get(v_toGoalState_4841_, 16);
v_sstates_4861_ = lean_ctor_get(v_toGoalState_4841_, 17);
v_goalStack_4862_ = lean_ctor_get(v_toGoalState_4841_, 18);
v_introBase_4863_ = lean_ctor_get_uint64(v_toGoalState_4841_, sizeof(void*)*20);
v_numIntros_4864_ = lean_ctor_get(v_toGoalState_4841_, 19);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_toGoalState_4841_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4866_ = v_toGoalState_4841_;
v_isShared_4867_ = v_isSharedCheck_4907_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_numIntros_4864_);
lean_inc(v_goalStack_4862_);
lean_inc(v_sstates_4861_);
lean_inc(v_clean_4860_);
lean_inc(v_split_4859_);
lean_inc(v_inj_4858_);
lean_inc(v_ematch_4857_);
lean_inc(v_extThms_4856_);
lean_inc(v_facts_4855_);
lean_inc(v_newRawFacts_4854_);
lean_inc(v_nextIdx_4853_);
lean_inc(v_internalizing_4852_);
lean_inc(v_toProcess_4851_);
lean_inc(v_indicesFound_4850_);
lean_inc(v_appMap_4849_);
lean_inc(v_congrTable_4848_);
lean_inc(v_parents_4847_);
lean_inc(v_exprs_4846_);
lean_inc(v_enodeMap_4845_);
lean_inc(v_nextDeclIdx_4844_);
lean_dec(v_toGoalState_4841_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4907_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4854_);
if (lean_obj_tag(v___x_4868_) == 1)
{
lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4903_; 
lean_inc(v_mvarId_4843_);
v_isSharedCheck_4903_ = !lean_is_exclusive(v_goal_4828_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; lean_object* v_unused_4905_; 
v_unused_4904_ = lean_ctor_get(v_goal_4828_, 1);
lean_dec(v_unused_4904_);
v_unused_4905_ = lean_ctor_get(v_goal_4828_, 0);
lean_dec(v_unused_4905_);
v___x_4870_ = v_goal_4828_;
v_isShared_4871_ = v_isSharedCheck_4903_;
goto v_resetjp_4869_;
}
else
{
lean_dec(v_goal_4828_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4903_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v_val_4872_; lean_object* v_fst_4873_; lean_object* v_snd_4874_; lean_object* v_proof_4875_; lean_object* v_prop_4876_; lean_object* v_generation_4877_; lean_object* v_splitSource_4878_; lean_object* v_ematchDiagSource_4879_; lean_object* v_simp_4880_; lean_object* v_simpMethods_4881_; lean_object* v_symSimpMethods_4882_; lean_object* v_symDSimpMethods_4883_; lean_object* v_config_4884_; lean_object* v_identity_4885_; lean_object* v_activeSolvers_4886_; lean_object* v_anchorRefs_x3f_4887_; uint8_t v_anchors_4888_; uint8_t v_cheapCases_4889_; uint8_t v_reportMVarIssue_4890_; lean_object* v_symPrios_4891_; lean_object* v_extensions_4892_; uint8_t v_debug_4893_; uint8_t v_ematchDiag_4894_; lean_object* v___x_4896_; 
v_val_4872_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_val_4872_);
lean_dec_ref_known(v___x_4868_, 1);
v_fst_4873_ = lean_ctor_get(v_val_4872_, 0);
lean_inc(v_fst_4873_);
v_snd_4874_ = lean_ctor_get(v_val_4872_, 1);
lean_inc(v_snd_4874_);
lean_dec(v_val_4872_);
v_proof_4875_ = lean_ctor_get(v_fst_4873_, 0);
lean_inc_ref(v_proof_4875_);
v_prop_4876_ = lean_ctor_get(v_fst_4873_, 1);
lean_inc_ref(v_prop_4876_);
v_generation_4877_ = lean_ctor_get(v_fst_4873_, 2);
lean_inc(v_generation_4877_);
v_splitSource_4878_ = lean_ctor_get(v_fst_4873_, 3);
lean_inc(v_splitSource_4878_);
v_ematchDiagSource_4879_ = lean_ctor_get(v_fst_4873_, 4);
lean_inc(v_ematchDiagSource_4879_);
lean_dec(v_fst_4873_);
v_simp_4880_ = lean_ctor_get(v_a_4832_, 0);
v_simpMethods_4881_ = lean_ctor_get(v_a_4832_, 1);
v_symSimpMethods_4882_ = lean_ctor_get(v_a_4832_, 2);
v_symDSimpMethods_4883_ = lean_ctor_get(v_a_4832_, 3);
v_config_4884_ = lean_ctor_get(v_a_4832_, 4);
v_identity_4885_ = lean_ctor_get(v_a_4832_, 5);
v_activeSolvers_4886_ = lean_ctor_get(v_a_4832_, 6);
v_anchorRefs_x3f_4887_ = lean_ctor_get(v_a_4832_, 7);
v_anchors_4888_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*12);
v_cheapCases_4889_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*12 + 1);
v_reportMVarIssue_4890_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*12 + 2);
v_symPrios_4891_ = lean_ctor_get(v_a_4832_, 10);
v_extensions_4892_ = lean_ctor_get(v_a_4832_, 11);
v_debug_4893_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*12 + 3);
v_ematchDiag_4894_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*12 + 4);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 10, v_snd_4874_);
v___x_4896_ = v___x_4866_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_nextDeclIdx_4844_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_enodeMap_4845_);
lean_ctor_set(v_reuseFailAlloc_4902_, 2, v_exprs_4846_);
lean_ctor_set(v_reuseFailAlloc_4902_, 3, v_parents_4847_);
lean_ctor_set(v_reuseFailAlloc_4902_, 4, v_congrTable_4848_);
lean_ctor_set(v_reuseFailAlloc_4902_, 5, v_appMap_4849_);
lean_ctor_set(v_reuseFailAlloc_4902_, 6, v_indicesFound_4850_);
lean_ctor_set(v_reuseFailAlloc_4902_, 7, v_toProcess_4851_);
lean_ctor_set(v_reuseFailAlloc_4902_, 8, v_internalizing_4852_);
lean_ctor_set(v_reuseFailAlloc_4902_, 9, v_nextIdx_4853_);
lean_ctor_set(v_reuseFailAlloc_4902_, 10, v_snd_4874_);
lean_ctor_set(v_reuseFailAlloc_4902_, 11, v_facts_4855_);
lean_ctor_set(v_reuseFailAlloc_4902_, 12, v_extThms_4856_);
lean_ctor_set(v_reuseFailAlloc_4902_, 13, v_ematch_4857_);
lean_ctor_set(v_reuseFailAlloc_4902_, 14, v_inj_4858_);
lean_ctor_set(v_reuseFailAlloc_4902_, 15, v_split_4859_);
lean_ctor_set(v_reuseFailAlloc_4902_, 16, v_clean_4860_);
lean_ctor_set(v_reuseFailAlloc_4902_, 17, v_sstates_4861_);
lean_ctor_set(v_reuseFailAlloc_4902_, 18, v_goalStack_4862_);
lean_ctor_set(v_reuseFailAlloc_4902_, 19, v_numIntros_4864_);
lean_ctor_set_uint8(v_reuseFailAlloc_4902_, sizeof(void*)*20 + 8, v_inconsistent_4842_);
lean_ctor_set_uint64(v_reuseFailAlloc_4902_, sizeof(void*)*20, v_introBase_4863_);
v___x_4896_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v_goal_4898_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4896_);
v_goal_4898_ = v___x_4870_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4896_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_mvarId_4843_);
v_goal_4898_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
lean_inc_ref(v_extensions_4892_);
lean_inc_ref(v_symPrios_4891_);
lean_inc(v_anchorRefs_x3f_4887_);
lean_inc_ref(v_activeSolvers_4886_);
lean_inc(v_identity_4885_);
lean_inc_ref(v_config_4884_);
lean_inc_ref(v_symDSimpMethods_4883_);
lean_inc_ref(v_symSimpMethods_4882_);
lean_inc_ref(v_simpMethods_4881_);
lean_inc_ref(v_simp_4880_);
v___x_4899_ = lean_alloc_ctor(0, 12, 5);
lean_ctor_set(v___x_4899_, 0, v_simp_4880_);
lean_ctor_set(v___x_4899_, 1, v_simpMethods_4881_);
lean_ctor_set(v___x_4899_, 2, v_symSimpMethods_4882_);
lean_ctor_set(v___x_4899_, 3, v_symDSimpMethods_4883_);
lean_ctor_set(v___x_4899_, 4, v_config_4884_);
lean_ctor_set(v___x_4899_, 5, v_identity_4885_);
lean_ctor_set(v___x_4899_, 6, v_activeSolvers_4886_);
lean_ctor_set(v___x_4899_, 7, v_anchorRefs_x3f_4887_);
lean_ctor_set(v___x_4899_, 8, v_splitSource_4878_);
lean_ctor_set(v___x_4899_, 9, v_ematchDiagSource_4879_);
lean_ctor_set(v___x_4899_, 10, v_symPrios_4891_);
lean_ctor_set(v___x_4899_, 11, v_extensions_4892_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*12, v_anchors_4888_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*12 + 1, v_cheapCases_4889_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*12 + 2, v_reportMVarIssue_4890_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*12 + 3, v_debug_4893_);
lean_ctor_set_uint8(v___x_4899_, sizeof(void*)*12 + 4, v_ematchDiag_4894_);
v___x_4900_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4875_, v_prop_4876_, v_generation_4877_, v_goal_4898_, v_kna_4829_, v_kp_4830_, v_a_4831_, v___x_4899_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec_ref_known(v___x_4899_, 12);
return v___x_4900_;
}
}
}
}
else
{
lean_object* v___x_4906_; 
lean_dec(v___x_4868_);
lean_del_object(v___x_4866_);
lean_dec(v_numIntros_4864_);
lean_dec_ref(v_goalStack_4862_);
lean_dec_ref(v_sstates_4861_);
lean_dec_ref(v_clean_4860_);
lean_dec_ref(v_split_4859_);
lean_dec_ref(v_inj_4858_);
lean_dec_ref(v_ematch_4857_);
lean_dec_ref(v_extThms_4856_);
lean_dec_ref(v_facts_4855_);
lean_dec(v_nextIdx_4853_);
lean_dec_ref(v_internalizing_4852_);
lean_dec_ref(v_toProcess_4851_);
lean_dec_ref(v_indicesFound_4850_);
lean_dec_ref(v_appMap_4849_);
lean_dec_ref(v_congrTable_4848_);
lean_dec_ref(v_parents_4847_);
lean_dec_ref(v_exprs_4846_);
lean_dec_ref(v_enodeMap_4845_);
lean_dec(v_nextDeclIdx_4844_);
lean_dec_ref(v_kp_4830_);
lean_inc(v_a_4839_);
lean_inc_ref(v_a_4838_);
lean_inc(v_a_4837_);
lean_inc_ref(v_a_4836_);
lean_inc(v_a_4835_);
lean_inc_ref(v_a_4834_);
lean_inc(v_a_4833_);
lean_inc_ref(v_a_4832_);
lean_inc(v_a_4831_);
v___x_4906_ = lean_apply_11(v_kna_4829_, v_goal_4828_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, lean_box(0));
return v___x_4906_;
}
}
}
else
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec_ref(v_toGoalState_4841_);
lean_dec_ref(v_kp_4830_);
lean_dec_ref(v_kna_4829_);
lean_dec_ref(v_goal_4828_);
v___x_4908_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4908_);
return v___x_4909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4910_, lean_object* v_kna_4911_, lean_object* v_kp_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4910_, v_kna_4911_, v_kp_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
lean_dec(v_a_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
lean_dec(v_a_4915_);
lean_dec_ref(v_a_4914_);
lean_dec(v_a_4913_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4924_, lean_object* v_kp_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(1000000u);
v___x_4937_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4938_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4936_, v___x_4937_, v_a_4924_, v_kp_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4939_, lean_object* v_kp_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4939_, v_kp_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4952_, lean_object* v_kna_4953_, lean_object* v_kp_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4952_, v_kp_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4966_, lean_object* v_kna_4967_, lean_object* v_kp_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4966_, v_kna_4967_, v_kp_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec(v_a_4971_);
lean_dec_ref(v_a_4970_);
lean_dec(v_a_4969_);
lean_dec_ref(v_kna_4967_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4980_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4995_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_5008_, lean_object* v___f_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_Meta_Grind_Action_andThen(v_a_5008_, v___f_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_5024_, lean_object* v___f_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_5024_, v___f_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
lean_dec(v___y_5037_);
lean_dec_ref(v___y_5036_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v___y_5029_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___f_5042_; lean_object* v___x_5043_; 
v___f_5042_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___x_5043_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5052_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5046_ = v___x_5043_;
v_isShared_5047_ = v_isSharedCheck_5052_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5052_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___f_5048_; lean_object* v___x_5050_; 
v___f_5048_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_5048_, 0, v_a_5044_);
lean_closure_set(v___f_5048_, 1, v___f_5042_);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v___f_5048_);
v___x_5050_ = v___x_5046_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___f_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
else
{
return v___x_5043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_5054_;
}
}
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedIntroResult_default = _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult_default);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
}
#ifdef __cplusplus
}
#endif
