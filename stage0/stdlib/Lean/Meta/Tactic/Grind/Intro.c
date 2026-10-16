// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Injection import Lean.Meta.Tactic.Grind.Core import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.MarkAccessible import Init.Grind.Util
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
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
uint8_t l_Lean_Meta_Grind_isMatchCondCandidate(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
lean_object* v_arg_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_arg_74_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_74_);
v___x_75_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3));
v___x_77_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_76_);
lean_dec_ref(v___x_75_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v_arg_74_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_arg_74_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object* v_e_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
uint8_t v___x_92_; 
lean_inc_ref(v_e_80_);
v___x_92_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_80_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_inc_ref(v_e_80_);
v___x_93_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_80_);
if (lean_obj_tag(v___x_93_) == 1)
{
lean_object* v_val_94_; uint8_t v___x_95_; lean_object* v___x_96_; 
lean_dec_ref(v_e_80_);
v_val_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = 1;
v___x_96_ = l_Lean_Meta_Sym_canon(v_val_94_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = l_Lean_Meta_Sym_shareCommon(v_a_97_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_104_, 0, v_a_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*2, v___x_95_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_98_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_98_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_96_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_96_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
else
{
lean_object* v___x_125_; 
lean_dec(v___x_93_);
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc(v_a_82_);
lean_inc(v_a_81_);
v___x_125_ = lean_grind_preprocess(v_e_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
return v___x_125_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_80_);
lean_inc(v_a_90_);
lean_inc_ref(v_a_89_);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc(v_a_84_);
lean_inc_ref(v_a_83_);
lean_inc(v_a_82_);
lean_inc(v_a_81_);
v___x_127_ = lean_grind_preprocess(v___x_126_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object* v_e_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_129_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_141_, lean_object* v_str_142_, lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
uint8_t v_decide_145_; 
v_decide_145_ = lean_nat_dec_eq(v_a_143_, v___x_141_);
if (v_decide_145_ == 0)
{
uint32_t v___x_146_; uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_string_utf8_get_fast(v_str_142_, v_a_143_);
v___x_147_ = 95;
v___x_148_ = lean_uint32_dec_eq(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_string_utf8_next_fast(v_str_142_, v_a_143_);
lean_dec(v_a_143_);
v_a_143_ = v___x_150_;
v_b_144_ = v___x_149_;
goto _start;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_a_143_);
return v___x_152_;
}
}
else
{
lean_dec(v_a_143_);
lean_inc(v_b_144_);
return v_b_144_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_153_, lean_object* v_str_154_, lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_153_, v_str_154_, v_a_155_, v_b_156_);
lean_dec(v_b_156_);
lean_dec_ref(v_str_154_);
lean_dec(v___x_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_164_, lean_object* v_type_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; 
if (lean_obj_tag(v_name_164_) == 1)
{
lean_object* v_str_199_; lean_object* v___y_201_; lean_object* v_searcher_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_str_199_ = lean_ctor_get(v_name_164_, 1);
lean_inc_ref(v_str_199_);
lean_dec_ref_known(v_name_164_, 2);
v_searcher_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_string_utf8_byte_size(v_str_199_);
v___x_221_ = lean_box(0);
v___x_222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_220_, v_str_199_, v_searcher_219_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
v___y_201_ = v___x_220_;
goto v___jp_200_;
}
else
{
lean_object* v_val_223_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_201_ = v_val_223_;
goto v___jp_200_;
}
v___jp_200_:
{
lean_object* v___x_202_; uint8_t v_decide_203_; 
v___x_202_ = lean_string_utf8_byte_size(v_str_199_);
v_decide_203_ = lean_nat_dec_eq(v___y_201_, v___x_202_);
if (v_decide_203_ == 0)
{
lean_object* v___x_204_; lean_object* v_suffix_205_; uint8_t v___x_206_; 
v___x_204_ = lean_string_utf8_next_fast(v_str_199_, v___y_201_);
lean_inc_ref(v_str_199_);
v_suffix_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_205_, 0, v_str_199_);
lean_ctor_set(v_suffix_205_, 1, v___x_204_);
lean_ctor_set(v_suffix_205_, 2, v___x_202_);
v___x_206_ = l_String_Slice_isNat(v_suffix_205_);
lean_dec_ref_known(v_suffix_205_, 3);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v___y_201_);
lean_dec_ref(v_type_165_);
v___x_207_ = lean_box(0);
v___x_208_ = l_Lean_Name_str___override(v___x_207_, v_str_199_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_nat_dec_eq(v___y_201_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_type_165_);
v___x_212_ = lean_string_utf8_extract_fast(v_str_199_, v___x_210_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v_str_199_);
v___x_213_ = lean_box(0);
v___x_214_ = l_Lean_Name_str___override(v___x_213_, v___x_212_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_dec(v___y_201_);
lean_dec_ref(v_str_199_);
v___y_172_ = v_a_166_;
v___y_173_ = v_a_167_;
v___y_174_ = v_a_168_;
v___y_175_ = v_a_169_;
goto v___jp_171_;
}
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v___y_201_);
lean_dec_ref(v_type_165_);
v___x_216_ = lean_box(0);
v___x_217_ = l_Lean_Name_str___override(v___x_216_, v_str_199_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
else
{
lean_dec(v_name_164_);
v___y_172_ = v_a_166_;
v___y_173_ = v_a_167_;
v___y_174_ = v_a_168_;
v___y_175_ = v_a_169_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_isProp(v_type_165_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_190_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_190_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
uint8_t v___x_181_; 
v___x_181_ = lean_unbox(v_a_177_);
lean_dec(v_a_177_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_186_);
v___x_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_a_191_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_176_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_224_, lean_object* v_type_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_224_, v_type_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v_str_234_, lean_object* v_inst_235_, lean_object* v_R_236_, lean_object* v_a_237_, lean_object* v_b_238_, lean_object* v_c_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_232_, v_str_234_, v_a_237_, v_b_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_241_, lean_object* v___x_242_, lean_object* v_str_243_, lean_object* v_inst_244_, lean_object* v_R_245_, lean_object* v_a_246_, lean_object* v_b_247_, lean_object* v_c_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_241_, v___x_242_, v_str_243_, v_inst_244_, v_R_245_, v_a_246_, v_b_247_, v_c_248_);
lean_dec(v_b_247_);
lean_dec_ref(v_str_243_);
lean_dec_ref(v___x_242_);
lean_dec(v___x_241_);
return v_res_249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_250_, lean_object* v_i_251_, lean_object* v_k_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_get_size(v_keys_250_);
v___x_254_ = lean_nat_dec_lt(v_i_251_, v___x_253_);
if (v___x_254_ == 0)
{
lean_dec(v_i_251_);
return v___x_254_;
}
else
{
lean_object* v_k_x27_255_; uint8_t v___x_256_; 
v_k_x27_255_ = lean_array_fget_borrowed(v_keys_250_, v_i_251_);
v___x_256_ = lean_name_eq(v_k_252_, v_k_x27_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_251_, v___x_257_);
lean_dec(v_i_251_);
v_i_251_ = v___x_258_;
goto _start;
}
else
{
lean_dec(v_i_251_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_260_, lean_object* v_i_261_, lean_object* v_k_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_260_, v_i_261_, v_k_262_);
lean_dec(v_k_262_);
lean_dec_ref(v_keys_260_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_265_, size_t v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v_es_268_; lean_object* v___x_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v_j_272_; lean_object* v___x_273_; 
v_es_268_ = lean_ctor_get(v_x_265_, 0);
v___x_269_ = lean_box(2);
v___x_270_ = ((size_t)31ULL);
v___x_271_ = lean_usize_land(v_x_266_, v___x_270_);
v_j_272_ = lean_usize_to_nat(v___x_271_);
v___x_273_ = lean_array_get_borrowed(v___x_269_, v_es_268_, v_j_272_);
lean_dec(v_j_272_);
switch(lean_obj_tag(v___x_273_))
{
case 0:
{
lean_object* v_key_274_; uint8_t v___x_275_; 
v_key_274_ = lean_ctor_get(v___x_273_, 0);
v___x_275_ = lean_name_eq(v_x_267_, v_key_274_);
return v___x_275_;
}
case 1:
{
lean_object* v_node_276_; size_t v___x_277_; size_t v___x_278_; 
v_node_276_ = lean_ctor_get(v___x_273_, 0);
v___x_277_ = ((size_t)5ULL);
v___x_278_ = lean_usize_shift_right(v_x_266_, v___x_277_);
v_x_265_ = v_node_276_;
v_x_266_ = v___x_278_;
goto _start;
}
default: 
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
}
}
else
{
lean_object* v_ks_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_ks_281_ = lean_ctor_get(v_x_265_, 0);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_281_, v___x_282_, v_x_267_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
size_t v_x_33094__boxed_287_; uint8_t v_res_288_; lean_object* v_r_289_; 
v_x_33094__boxed_287_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_res_288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_284_, v_x_33094__boxed_287_, v_x_286_);
lean_dec(v_x_286_);
lean_dec_ref(v_x_284_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint64_t v___y_293_; 
if (lean_obj_tag(v_x_291_) == 0)
{
uint64_t v___x_296_; 
v___x_296_ = 1723ULL;
v___y_293_ = v___x_296_;
goto v___jp_292_;
}
else
{
uint64_t v_hash_297_; 
v_hash_297_ = lean_ctor_get_uint64(v_x_291_, sizeof(void*)*2);
v___y_293_ = v_hash_297_;
goto v___jp_292_;
}
v___jp_292_:
{
size_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_uint64_to_usize(v___y_293_);
v___x_295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_290_, v___x_294_, v_x_291_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec_ref(v_x_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_326_; 
v_snd_306_ = lean_ctor_get(v_a_303_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v_a_303_, 0);
lean_dec(v_unused_327_);
v___x_308_ = v_a_303_;
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_dec(v_a_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_326_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_toGoalState_314_; lean_object* v_clean_315_; lean_object* v_used_316_; uint8_t v___x_317_; 
lean_inc(v_snd_306_);
lean_inc(v_a_302_);
v___x_310_ = lean_name_append_index_after(v_a_302_, v_snd_306_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v_snd_306_, v___x_311_);
lean_dec(v_snd_306_);
v___x_313_ = lean_st_ref_get(v___y_304_);
v_toGoalState_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_toGoalState_314_);
lean_dec(v___x_313_);
v_clean_315_ = lean_ctor_get(v_toGoalState_314_, 16);
lean_inc_ref(v_clean_315_);
lean_dec_ref(v_toGoalState_314_);
v_used_316_ = lean_ctor_get(v_clean_315_, 0);
lean_inc_ref(v_used_316_);
lean_dec_ref(v_clean_315_);
v___x_317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_316_, v___x_310_);
lean_dec_ref(v_used_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_319_; 
lean_dec(v_a_302_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_312_);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_319_ = v___x_308_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_312_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_312_);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_323_ = v___x_308_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_312_);
v___x_323_ = v_reuseFailAlloc_325_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v_a_303_ = v___x_323_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_328_, v_a_329_, v___y_330_);
lean_dec(v___y_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_ks_337_; lean_object* v_vs_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_362_; 
v_ks_337_ = lean_ctor_get(v_x_333_, 0);
v_vs_338_ = lean_ctor_get(v_x_333_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_362_ == 0)
{
v___x_340_ = v_x_333_;
v_isShared_341_ = v_isSharedCheck_362_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_vs_338_);
lean_inc(v_ks_337_);
lean_dec(v_x_333_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_362_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_array_get_size(v_ks_337_);
v___x_343_ = lean_nat_dec_lt(v_x_334_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_dec(v_x_334_);
v___x_344_ = lean_array_push(v_ks_337_, v_x_335_);
v___x_345_ = lean_array_push(v_vs_338_, v_x_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_345_);
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v_k_x27_349_; uint8_t v___x_350_; 
v_k_x27_349_ = lean_array_fget_borrowed(v_ks_337_, v_x_334_);
v___x_350_ = lean_name_eq(v_x_335_, v_k_x27_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_352_; 
if (v_isShared_341_ == 0)
{
v___x_352_ = v___x_340_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_ks_337_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_vs_338_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_x_334_, v___x_353_);
lean_dec(v_x_334_);
v_x_333_ = v___x_352_;
v_x_334_ = v___x_354_;
goto _start;
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_array_fset(v_ks_337_, v_x_334_, v_x_335_);
v___x_358_ = lean_array_fset(v_vs_338_, v_x_334_, v_x_336_);
lean_dec(v_x_334_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_358_);
lean_ctor_set(v___x_340_, 0, v___x_357_);
v___x_360_ = v___x_340_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_363_, lean_object* v_k_364_, lean_object* v_v_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_363_, v___x_366_, v_k_364_, v_v_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_369_, size_t v_x_370_, size_t v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v_es_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v_j_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_es_374_ = lean_ctor_get(v_x_369_, 0);
v___x_375_ = ((size_t)31ULL);
v___x_376_ = lean_usize_land(v_x_370_, v___x_375_);
v_j_377_ = lean_usize_to_nat(v___x_376_);
v___x_378_ = lean_array_get_size(v_es_374_);
v___x_379_ = lean_nat_dec_lt(v_j_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec(v_j_377_);
lean_dec(v_x_373_);
lean_dec(v_x_372_);
return v_x_369_;
}
else
{
lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_418_; 
lean_inc_ref(v_es_374_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_x_369_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v_x_369_, 0);
lean_dec(v_unused_419_);
v___x_381_ = v_x_369_;
v_isShared_382_ = v_isSharedCheck_418_;
goto v_resetjp_380_;
}
else
{
lean_dec(v_x_369_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_418_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_v_383_; lean_object* v___x_384_; lean_object* v_xs_x27_385_; lean_object* v___y_387_; 
v_v_383_ = lean_array_fget(v_es_374_, v_j_377_);
v___x_384_ = lean_box(0);
v_xs_x27_385_ = lean_array_fset(v_es_374_, v_j_377_, v___x_384_);
switch(lean_obj_tag(v_v_383_))
{
case 0:
{
lean_object* v_key_392_; lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_403_; 
v_key_392_ = lean_ctor_get(v_v_383_, 0);
v_val_393_ = lean_ctor_get(v_v_383_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_v_383_);
if (v_isSharedCheck_403_ == 0)
{
v___x_395_ = v_v_383_;
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_inc(v_key_392_);
lean_dec(v_v_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; 
v___x_397_ = lean_name_eq(v_x_372_, v_key_392_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_del_object(v___x_395_);
v___x_398_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_392_, v_val_393_, v_x_372_, v_x_373_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___y_387_ = v___x_399_;
goto v___jp_386_;
}
else
{
lean_object* v___x_401_; 
lean_dec(v_val_393_);
lean_dec(v_key_392_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v_x_373_);
lean_ctor_set(v___x_395_, 0, v_x_372_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_x_372_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_x_373_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
v___y_387_ = v___x_401_;
goto v___jp_386_;
}
}
}
}
case 1:
{
lean_object* v_node_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_node_404_ = lean_ctor_get(v_v_383_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_v_383_);
if (v_isSharedCheck_416_ == 0)
{
v___x_406_ = v_v_383_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_node_404_);
lean_dec(v_v_383_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_408_ = ((size_t)5ULL);
v___x_409_ = lean_usize_shift_right(v_x_370_, v___x_408_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_x_371_, v___x_410_);
v___x_412_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_404_, v___x_409_, v___x_411_, v_x_372_, v_x_373_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_412_);
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v___y_387_ = v___x_414_;
goto v___jp_386_;
}
}
}
default: 
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_x_372_);
lean_ctor_set(v___x_417_, 1, v_x_373_);
v___y_387_ = v___x_417_;
goto v___jp_386_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_array_fset(v_xs_x27_385_, v_j_377_, v___y_387_);
lean_dec(v_j_377_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_388_);
v___x_390_ = v___x_381_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v_ks_420_; lean_object* v_vs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_439_; 
v_ks_420_ = lean_ctor_get(v_x_369_, 0);
v_vs_421_ = lean_ctor_get(v_x_369_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_369_);
if (v_isSharedCheck_439_ == 0)
{
v___x_423_ = v_x_369_;
v_isShared_424_ = v_isSharedCheck_439_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_vs_421_);
lean_inc(v_ks_420_);
lean_dec(v_x_369_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_439_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_ks_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_vs_421_);
v___x_426_ = v_reuseFailAlloc_438_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v_newNode_427_; size_t v___x_428_; uint8_t v___x_429_; 
v_newNode_427_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_426_, v_x_372_, v_x_373_);
v___x_428_ = ((size_t)7ULL);
v___x_429_ = lean_usize_dec_le(v___x_428_, v_x_371_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_430_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_427_);
v___x_431_ = lean_unsigned_to_nat(4u);
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
lean_dec(v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v_ks_433_; lean_object* v_vs_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_ks_433_ = lean_ctor_get(v_newNode_427_, 0);
lean_inc_ref(v_ks_433_);
v_vs_434_ = lean_ctor_get(v_newNode_427_, 1);
lean_inc_ref(v_vs_434_);
lean_dec_ref(v_newNode_427_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_371_, v_ks_433_, v_vs_434_, v___x_435_, v___x_436_);
lean_dec_ref(v_vs_434_);
lean_dec_ref(v_ks_433_);
return v___x_437_;
}
else
{
return v_newNode_427_;
}
}
else
{
return v_newNode_427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_440_, lean_object* v_keys_441_, lean_object* v_vals_442_, lean_object* v_i_443_, lean_object* v_entries_444_){
_start:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_array_get_size(v_keys_441_);
v___x_446_ = lean_nat_dec_lt(v_i_443_, v___x_445_);
if (v___x_446_ == 0)
{
lean_dec(v_i_443_);
return v_entries_444_;
}
else
{
lean_object* v_k_447_; lean_object* v_v_448_; uint64_t v___y_450_; 
v_k_447_ = lean_array_fget_borrowed(v_keys_441_, v_i_443_);
v_v_448_ = lean_array_fget_borrowed(v_vals_442_, v_i_443_);
if (lean_obj_tag(v_k_447_) == 0)
{
uint64_t v___x_461_; 
v___x_461_ = 1723ULL;
v___y_450_ = v___x_461_;
goto v___jp_449_;
}
else
{
uint64_t v_hash_462_; 
v_hash_462_ = lean_ctor_get_uint64(v_k_447_, sizeof(void*)*2);
v___y_450_ = v_hash_462_;
goto v___jp_449_;
}
v___jp_449_:
{
size_t v_h_451_; size_t v___x_452_; lean_object* v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v_h_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_h_451_ = lean_uint64_to_usize(v___y_450_);
v___x_452_ = ((size_t)5ULL);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v_depth_440_, v___x_454_);
v___x_456_ = lean_usize_mul(v___x_452_, v___x_455_);
v_h_457_ = lean_usize_shift_right(v_h_451_, v___x_456_);
v___x_458_ = lean_nat_add(v_i_443_, v___x_453_);
lean_dec(v_i_443_);
lean_inc(v_v_448_);
lean_inc(v_k_447_);
v___x_459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_444_, v_h_457_, v_depth_440_, v_k_447_, v_v_448_);
v_i_443_ = v___x_458_;
v_entries_444_ = v___x_459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_463_, lean_object* v_keys_464_, lean_object* v_vals_465_, lean_object* v_i_466_, lean_object* v_entries_467_){
_start:
{
size_t v_depth_boxed_468_; lean_object* v_res_469_; 
v_depth_boxed_468_ = lean_unbox_usize(v_depth_463_);
lean_dec(v_depth_463_);
v_res_469_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_468_, v_keys_464_, v_vals_465_, v_i_466_, v_entries_467_);
lean_dec_ref(v_vals_465_);
lean_dec_ref(v_keys_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
size_t v_x_33274__boxed_475_; size_t v_x_33275__boxed_476_; lean_object* v_res_477_; 
v_x_33274__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_x_33275__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_res_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_470_, v_x_33274__boxed_475_, v_x_33275__boxed_476_, v_x_473_, v_x_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
uint64_t v___y_482_; 
if (lean_obj_tag(v_x_479_) == 0)
{
uint64_t v___x_486_; 
v___x_486_ = 1723ULL;
v___y_482_ = v___x_486_;
goto v___jp_481_;
}
else
{
uint64_t v_hash_487_; 
v_hash_487_ = lean_ctor_get_uint64(v_x_479_, sizeof(void*)*2);
v___y_482_ = v_hash_487_;
goto v___jp_481_;
}
v___jp_481_:
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_uint64_to_usize(v___y_482_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_478_, v___x_483_, v___x_484_, v_x_479_, v_x_480_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_488_, lean_object* v_vals_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_array_get_size(v_keys_488_);
v___x_493_ = lean_nat_dec_lt(v_i_490_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_i_490_);
v___x_494_ = lean_box(0);
return v___x_494_;
}
else
{
lean_object* v_k_x27_495_; uint8_t v___x_496_; 
v_k_x27_495_ = lean_array_fget_borrowed(v_keys_488_, v_i_490_);
v___x_496_ = lean_name_eq(v_k_491_, v_k_x27_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_i_490_, v___x_497_);
lean_dec(v_i_490_);
v_i_490_ = v___x_498_;
goto _start;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_array_fget_borrowed(v_vals_489_, v_i_490_);
lean_dec(v_i_490_);
lean_inc(v___x_500_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_502_, lean_object* v_vals_503_, lean_object* v_i_504_, lean_object* v_k_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_502_, v_vals_503_, v_i_504_, v_k_505_);
lean_dec(v_k_505_);
lean_dec_ref(v_vals_503_);
lean_dec_ref(v_keys_502_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_507_, size_t v_x_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_es_510_; lean_object* v___x_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v_j_514_; lean_object* v___x_515_; 
v_es_510_ = lean_ctor_get(v_x_507_, 0);
v___x_511_ = lean_box(2);
v___x_512_ = ((size_t)31ULL);
v___x_513_ = lean_usize_land(v_x_508_, v___x_512_);
v_j_514_ = lean_usize_to_nat(v___x_513_);
v___x_515_ = lean_array_get_borrowed(v___x_511_, v_es_510_, v_j_514_);
lean_dec(v_j_514_);
switch(lean_obj_tag(v___x_515_))
{
case 0:
{
lean_object* v_key_516_; lean_object* v_val_517_; uint8_t v___x_518_; 
v_key_516_ = lean_ctor_get(v___x_515_, 0);
v_val_517_ = lean_ctor_get(v___x_515_, 1);
v___x_518_ = lean_name_eq(v_x_509_, v_key_516_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_box(0);
return v___x_519_;
}
else
{
lean_object* v___x_520_; 
lean_inc(v_val_517_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_val_517_);
return v___x_520_;
}
}
case 1:
{
lean_object* v_node_521_; size_t v___x_522_; size_t v___x_523_; 
v_node_521_ = lean_ctor_get(v___x_515_, 0);
v___x_522_ = ((size_t)5ULL);
v___x_523_ = lean_usize_shift_right(v_x_508_, v___x_522_);
v_x_507_ = v_node_521_;
v_x_508_ = v___x_523_;
goto _start;
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = lean_box(0);
return v___x_525_;
}
}
}
else
{
lean_object* v_ks_526_; lean_object* v_vs_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_ks_526_ = lean_ctor_get(v_x_507_, 0);
v_vs_527_ = lean_ctor_get(v_x_507_, 1);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_526_, v_vs_527_, v___x_528_, v_x_509_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_33464__boxed_533_; lean_object* v_res_534_; 
v_x_33464__boxed_533_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_530_, v_x_33464__boxed_533_, v_x_532_);
lean_dec(v_x_532_);
lean_dec_ref(v_x_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint64_t v___y_538_; 
if (lean_obj_tag(v_x_536_) == 0)
{
uint64_t v___x_541_; 
v___x_541_ = 1723ULL;
v___y_538_ = v___x_541_;
goto v___jp_537_;
}
else
{
uint64_t v_hash_542_; 
v_hash_542_ = lean_ctor_get_uint64(v_x_536_, sizeof(void*)*2);
v___y_538_ = v_hash_542_;
goto v___jp_537_;
}
v___jp_537_:
{
size_t v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_uint64_to_usize(v___y_538_);
v___x_540_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_535_, v___x_539_, v_x_536_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec_ref(v_x_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_549_, lean_object* v_type_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_name_563_; lean_object* v___y_564_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_name_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_553_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_779_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_779_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_779_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_779_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v_clean_744_; 
v_clean_744_ = lean_ctor_get_uint8(v_a_719_, sizeof(void*)*14 + 16);
lean_dec(v_a_719_);
if (v_clean_744_ == 0)
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_549_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_val_746_; lean_object* v___x_748_; 
lean_dec_ref(v_type_550_);
lean_dec(v_name_549_);
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_val_746_);
v___x_748_ = v___x_721_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_val_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
uint8_t v___x_750_; 
lean_dec(v___x_745_);
v___x_750_ = l_Lean_Name_hasMacroScopes(v_name_549_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_del_object(v___x_721_);
lean_dec_ref(v_type_550_);
v___x_751_ = l_Lean_Core_mkFreshUserName(v_name_549_, v_a_559_, v_a_560_);
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = l_Lean_Name_eraseMacroScopes(v_name_549_);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_754_ = lean_name_eq(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_756_ = lean_name_eq(v___x_752_, v___x_755_);
lean_dec(v___x_752_);
if (v___x_756_ == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v_type_550_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_name_549_);
v___x_758_ = v___x_721_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_name_549_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_del_object(v___x_721_);
goto v___jp_723_;
}
}
else
{
lean_dec(v___x_752_);
lean_del_object(v___x_721_);
goto v___jp_723_;
}
}
}
}
else
{
uint8_t v___x_760_; 
lean_del_object(v___x_721_);
v___x_760_ = l_Lean_Name_hasMacroScopes(v_name_549_);
if (v___x_760_ == 0)
{
v_name_693_ = v_name_549_;
v___y_694_ = v_a_551_;
v___y_695_ = v_a_552_;
v___y_696_ = v_a_553_;
v___y_697_ = v_a_554_;
v___y_698_ = v_a_555_;
v___y_699_ = v_a_556_;
v___y_700_ = v_a_557_;
v___y_701_ = v_a_558_;
v___y_702_ = v_a_559_;
v___y_703_ = v_a_560_;
goto v___jp_692_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_761_ = l_Lean_Name_eraseMacroScopes(v_name_549_);
lean_dec(v_name_549_);
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_776_ = lean_name_eq(v___x_761_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_778_ = lean_name_eq(v___x_761_, v___x_777_);
if (v___x_778_ == 0)
{
v_name_693_ = v___x_761_;
v___y_694_ = v_a_551_;
v___y_695_ = v_a_552_;
v___y_696_ = v_a_553_;
v___y_697_ = v_a_554_;
v___y_698_ = v_a_555_;
v___y_699_ = v_a_556_;
v___y_700_ = v_a_557_;
v___y_701_ = v_a_558_;
v___y_702_ = v_a_559_;
v___y_703_ = v_a_560_;
goto v___jp_692_;
}
else
{
goto v___jp_762_;
}
}
else
{
goto v___jp_762_;
}
v___jp_762_:
{
lean_object* v___x_763_; 
lean_inc_ref(v_type_550_);
v___x_763_ = l_Lean_Meta_isProp(v_type_550_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_unbox(v_a_764_);
lean_dec(v_a_764_);
if (v___x_765_ == 0)
{
v_name_693_ = v___x_761_;
v___y_694_ = v_a_551_;
v___y_695_ = v_a_552_;
v___y_696_ = v_a_553_;
v___y_697_ = v_a_554_;
v___y_698_ = v_a_555_;
v___y_699_ = v_a_556_;
v___y_700_ = v_a_557_;
v___y_701_ = v_a_558_;
v___y_702_ = v_a_559_;
v___y_703_ = v_a_560_;
goto v___jp_692_;
}
else
{
lean_object* v___x_766_; 
lean_dec(v___x_761_);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_693_ = v___x_766_;
v___y_694_ = v_a_551_;
v___y_695_ = v_a_552_;
v___y_696_ = v_a_553_;
v___y_697_ = v_a_554_;
v___y_698_ = v_a_555_;
v___y_699_ = v_a_556_;
v___y_700_ = v_a_557_;
v___y_701_ = v_a_558_;
v___y_702_ = v_a_559_;
v___y_703_ = v_a_560_;
goto v___jp_692_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v___x_761_);
lean_dec_ref(v_type_550_);
v_a_767_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_763_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
v___jp_723_:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_isProp(v_type_550_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_735_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint8_t v___x_729_; 
v___x_729_ = lean_unbox(v_a_725_);
lean_dec(v_a_725_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_name_549_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_name_549_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_del_object(v___x_727_);
lean_dec(v_name_549_);
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_734_ = l_Lean_Core_mkFreshUserName(v___x_733_, v_a_559_, v_a_560_);
return v___x_734_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_name_549_);
v_a_736_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_724_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_724_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_type_550_);
lean_dec(v_name_549_);
v_a_780_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_718_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_718_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
v___jp_562_:
{
lean_object* v___x_565_; lean_object* v_toGoalState_566_; lean_object* v_clean_567_; lean_object* v_mvarId_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_614_; 
v___x_565_ = lean_st_ref_take(v___y_564_);
v_toGoalState_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_toGoalState_566_);
v_clean_567_ = lean_ctor_get(v_toGoalState_566_, 16);
lean_inc_ref(v_clean_567_);
v_mvarId_568_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_565_, 0);
lean_dec(v_unused_615_);
v___x_570_ = v___x_565_;
v_isShared_571_ = v_isSharedCheck_614_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_mvarId_568_);
lean_dec(v___x_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_614_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_nextDeclIdx_572_; lean_object* v_enodeMap_573_; lean_object* v_exprs_574_; lean_object* v_parents_575_; lean_object* v_congrTable_576_; lean_object* v_appMap_577_; lean_object* v_indicesFound_578_; lean_object* v_toProcess_579_; lean_object* v_internalizing_580_; uint8_t v_inconsistent_581_; lean_object* v_nextIdx_582_; lean_object* v_newRawFacts_583_; lean_object* v_facts_584_; lean_object* v_extThms_585_; lean_object* v_ematch_586_; lean_object* v_inj_587_; lean_object* v_split_588_; lean_object* v_sstates_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_612_; 
v_nextDeclIdx_572_ = lean_ctor_get(v_toGoalState_566_, 0);
v_enodeMap_573_ = lean_ctor_get(v_toGoalState_566_, 1);
v_exprs_574_ = lean_ctor_get(v_toGoalState_566_, 2);
v_parents_575_ = lean_ctor_get(v_toGoalState_566_, 3);
v_congrTable_576_ = lean_ctor_get(v_toGoalState_566_, 4);
v_appMap_577_ = lean_ctor_get(v_toGoalState_566_, 5);
v_indicesFound_578_ = lean_ctor_get(v_toGoalState_566_, 6);
v_toProcess_579_ = lean_ctor_get(v_toGoalState_566_, 7);
v_internalizing_580_ = lean_ctor_get(v_toGoalState_566_, 8);
v_inconsistent_581_ = lean_ctor_get_uint8(v_toGoalState_566_, sizeof(void*)*18);
v_nextIdx_582_ = lean_ctor_get(v_toGoalState_566_, 9);
v_newRawFacts_583_ = lean_ctor_get(v_toGoalState_566_, 10);
v_facts_584_ = lean_ctor_get(v_toGoalState_566_, 11);
v_extThms_585_ = lean_ctor_get(v_toGoalState_566_, 12);
v_ematch_586_ = lean_ctor_get(v_toGoalState_566_, 13);
v_inj_587_ = lean_ctor_get(v_toGoalState_566_, 14);
v_split_588_ = lean_ctor_get(v_toGoalState_566_, 15);
v_sstates_589_ = lean_ctor_get(v_toGoalState_566_, 17);
v_isSharedCheck_612_ = !lean_is_exclusive(v_toGoalState_566_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_toGoalState_566_, 16);
lean_dec(v_unused_613_);
v___x_591_ = v_toGoalState_566_;
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_sstates_589_);
lean_inc(v_split_588_);
lean_inc(v_inj_587_);
lean_inc(v_ematch_586_);
lean_inc(v_extThms_585_);
lean_inc(v_facts_584_);
lean_inc(v_newRawFacts_583_);
lean_inc(v_nextIdx_582_);
lean_inc(v_internalizing_580_);
lean_inc(v_toProcess_579_);
lean_inc(v_indicesFound_578_);
lean_inc(v_appMap_577_);
lean_inc(v_congrTable_576_);
lean_inc(v_parents_575_);
lean_inc(v_exprs_574_);
lean_inc(v_enodeMap_573_);
lean_inc(v_nextDeclIdx_572_);
lean_dec(v_toGoalState_566_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_used_593_; lean_object* v_next_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_611_; 
v_used_593_ = lean_ctor_get(v_clean_567_, 0);
v_next_594_ = lean_ctor_get(v_clean_567_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_clean_567_);
if (v_isSharedCheck_611_ == 0)
{
v___x_596_ = v_clean_567_;
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_next_594_);
lean_inc(v_used_593_);
lean_dec(v_clean_567_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = lean_box(0);
lean_inc(v_name_563_);
v___x_599_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_593_, v_name_563_, v___x_598_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_next_594_);
v___x_601_ = v_reuseFailAlloc_610_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 16, v___x_601_);
v___x_603_ = v___x_591_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_nextDeclIdx_572_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_enodeMap_573_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_exprs_574_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_parents_575_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_congrTable_576_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_appMap_577_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_indicesFound_578_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_toProcess_579_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_internalizing_580_);
lean_ctor_set(v_reuseFailAlloc_609_, 9, v_nextIdx_582_);
lean_ctor_set(v_reuseFailAlloc_609_, 10, v_newRawFacts_583_);
lean_ctor_set(v_reuseFailAlloc_609_, 11, v_facts_584_);
lean_ctor_set(v_reuseFailAlloc_609_, 12, v_extThms_585_);
lean_ctor_set(v_reuseFailAlloc_609_, 13, v_ematch_586_);
lean_ctor_set(v_reuseFailAlloc_609_, 14, v_inj_587_);
lean_ctor_set(v_reuseFailAlloc_609_, 15, v_split_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 16, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 17, v_sstates_589_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*18, v_inconsistent_581_);
v___x_603_ = v_reuseFailAlloc_609_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_603_);
v___x_605_ = v___x_570_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_mvarId_568_);
v___x_605_ = v_reuseFailAlloc_608_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_st_ref_put(v___y_564_, v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_name_563_);
return v___x_607_;
}
}
}
}
}
}
}
v___jp_616_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___y_623_);
lean_ctor_set(v___x_630_, 1, v___y_629_);
lean_inc(v___y_624_);
v___x_631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_624_, v___x_630_, v___y_620_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_635_; lean_object* v_toGoalState_636_; lean_object* v_clean_637_; lean_object* v_mvarId_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_682_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v_fst_633_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_fst_633_);
v_snd_634_ = lean_ctor_get(v_a_632_, 1);
lean_inc(v_snd_634_);
lean_dec(v_a_632_);
v___x_635_ = lean_st_ref_take(v___y_620_);
v_toGoalState_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_toGoalState_636_);
v_clean_637_ = lean_ctor_get(v_toGoalState_636_, 16);
lean_inc_ref(v_clean_637_);
v_mvarId_638_ = lean_ctor_get(v___x_635_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_683_);
v___x_640_ = v___x_635_;
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_mvarId_638_);
lean_dec(v___x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_nextDeclIdx_642_; lean_object* v_enodeMap_643_; lean_object* v_exprs_644_; lean_object* v_parents_645_; lean_object* v_congrTable_646_; lean_object* v_appMap_647_; lean_object* v_indicesFound_648_; lean_object* v_toProcess_649_; lean_object* v_internalizing_650_; uint8_t v_inconsistent_651_; lean_object* v_nextIdx_652_; lean_object* v_newRawFacts_653_; lean_object* v_facts_654_; lean_object* v_extThms_655_; lean_object* v_ematch_656_; lean_object* v_inj_657_; lean_object* v_split_658_; lean_object* v_sstates_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_680_; 
v_nextDeclIdx_642_ = lean_ctor_get(v_toGoalState_636_, 0);
v_enodeMap_643_ = lean_ctor_get(v_toGoalState_636_, 1);
v_exprs_644_ = lean_ctor_get(v_toGoalState_636_, 2);
v_parents_645_ = lean_ctor_get(v_toGoalState_636_, 3);
v_congrTable_646_ = lean_ctor_get(v_toGoalState_636_, 4);
v_appMap_647_ = lean_ctor_get(v_toGoalState_636_, 5);
v_indicesFound_648_ = lean_ctor_get(v_toGoalState_636_, 6);
v_toProcess_649_ = lean_ctor_get(v_toGoalState_636_, 7);
v_internalizing_650_ = lean_ctor_get(v_toGoalState_636_, 8);
v_inconsistent_651_ = lean_ctor_get_uint8(v_toGoalState_636_, sizeof(void*)*18);
v_nextIdx_652_ = lean_ctor_get(v_toGoalState_636_, 9);
v_newRawFacts_653_ = lean_ctor_get(v_toGoalState_636_, 10);
v_facts_654_ = lean_ctor_get(v_toGoalState_636_, 11);
v_extThms_655_ = lean_ctor_get(v_toGoalState_636_, 12);
v_ematch_656_ = lean_ctor_get(v_toGoalState_636_, 13);
v_inj_657_ = lean_ctor_get(v_toGoalState_636_, 14);
v_split_658_ = lean_ctor_get(v_toGoalState_636_, 15);
v_sstates_659_ = lean_ctor_get(v_toGoalState_636_, 17);
v_isSharedCheck_680_ = !lean_is_exclusive(v_toGoalState_636_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_toGoalState_636_, 16);
lean_dec(v_unused_681_);
v___x_661_ = v_toGoalState_636_;
v_isShared_662_ = v_isSharedCheck_680_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_sstates_659_);
lean_inc(v_split_658_);
lean_inc(v_inj_657_);
lean_inc(v_ematch_656_);
lean_inc(v_extThms_655_);
lean_inc(v_facts_654_);
lean_inc(v_newRawFacts_653_);
lean_inc(v_nextIdx_652_);
lean_inc(v_internalizing_650_);
lean_inc(v_toProcess_649_);
lean_inc(v_indicesFound_648_);
lean_inc(v_appMap_647_);
lean_inc(v_congrTable_646_);
lean_inc(v_parents_645_);
lean_inc(v_exprs_644_);
lean_inc(v_enodeMap_643_);
lean_inc(v_nextDeclIdx_642_);
lean_dec(v_toGoalState_636_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_680_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_used_663_; lean_object* v_next_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_679_; 
v_used_663_ = lean_ctor_get(v_clean_637_, 0);
v_next_664_ = lean_ctor_get(v_clean_637_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_clean_637_);
if (v_isSharedCheck_679_ == 0)
{
v___x_666_ = v_clean_637_;
v_isShared_667_ = v_isSharedCheck_679_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_next_664_);
lean_inc(v_used_663_);
lean_dec(v_clean_637_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_679_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_664_, v___y_624_, v_snd_634_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_used_663_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_678_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 16, v___x_670_);
v___x_672_ = v___x_661_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_nextDeclIdx_642_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_enodeMap_643_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_exprs_644_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_parents_645_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_congrTable_646_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_appMap_647_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_indicesFound_648_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v_toProcess_649_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_internalizing_650_);
lean_ctor_set(v_reuseFailAlloc_677_, 9, v_nextIdx_652_);
lean_ctor_set(v_reuseFailAlloc_677_, 10, v_newRawFacts_653_);
lean_ctor_set(v_reuseFailAlloc_677_, 11, v_facts_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 12, v_extThms_655_);
lean_ctor_set(v_reuseFailAlloc_677_, 13, v_ematch_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 14, v_inj_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 15, v_split_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 16, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_677_, 17, v_sstates_659_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*18, v_inconsistent_651_);
v___x_672_ = v_reuseFailAlloc_677_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_672_);
v___x_674_ = v___x_640_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_mvarId_638_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_st_ref_put(v___y_620_, v___x_674_);
v_name_563_ = v_fst_633_;
v___y_564_ = v___y_620_;
goto v___jp_562_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v___y_624_);
v_a_684_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_631_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_631_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
v___jp_692_:
{
lean_object* v___x_704_; lean_object* v_toGoalState_705_; lean_object* v_clean_706_; lean_object* v_used_707_; uint8_t v___x_708_; 
v___x_704_ = lean_st_ref_get(v___y_694_);
v_toGoalState_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_toGoalState_705_);
lean_dec(v___x_704_);
v_clean_706_ = lean_ctor_get(v_toGoalState_705_, 16);
lean_inc_ref(v_clean_706_);
lean_dec_ref(v_toGoalState_705_);
v_used_707_ = lean_ctor_get(v_clean_706_, 0);
lean_inc_ref(v_used_707_);
lean_dec_ref(v_clean_706_);
v___x_708_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_707_, v_name_693_);
lean_dec_ref(v_used_707_);
if (v___x_708_ == 0)
{
lean_dec_ref(v_type_550_);
v_name_563_ = v_name_693_;
v___y_564_ = v___y_694_;
goto v___jp_562_;
}
else
{
lean_object* v___x_709_; 
lean_inc(v_name_693_);
v___x_709_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_693_, v_type_550_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v_toGoalState_712_; lean_object* v_clean_713_; lean_object* v_next_714_; lean_object* v___x_715_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_st_ref_get(v___y_694_);
v_toGoalState_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_toGoalState_712_);
lean_dec(v___x_711_);
v_clean_713_ = lean_ctor_get(v_toGoalState_712_, 16);
lean_inc_ref(v_clean_713_);
lean_dec_ref(v_toGoalState_712_);
v_next_714_ = lean_ctor_get(v_clean_713_, 1);
lean_inc_ref(v_next_714_);
lean_dec_ref(v_clean_713_);
v___x_715_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_714_, v_a_710_);
lean_dec_ref(v_next_714_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v_val_716_; 
v_val_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_val_716_);
lean_dec_ref_known(v___x_715_, 1);
v___y_617_ = v___y_703_;
v___y_618_ = v___y_695_;
v___y_619_ = v___y_696_;
v___y_620_ = v___y_694_;
v___y_621_ = v___y_701_;
v___y_622_ = v___y_698_;
v___y_623_ = v_name_693_;
v___y_624_ = v_a_710_;
v___y_625_ = v___y_702_;
v___y_626_ = v___y_697_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_700_;
v___y_629_ = v_val_716_;
goto v___jp_616_;
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_715_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___y_617_ = v___y_703_;
v___y_618_ = v___y_695_;
v___y_619_ = v___y_696_;
v___y_620_ = v___y_694_;
v___y_621_ = v___y_701_;
v___y_622_ = v___y_698_;
v___y_623_ = v_name_693_;
v___y_624_ = v_a_710_;
v___y_625_ = v___y_702_;
v___y_626_ = v___y_697_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_700_;
v___y_629_ = v___x_717_;
goto v___jp_616_;
}
}
else
{
lean_dec(v_name_693_);
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_788_, lean_object* v_type_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_788_, v_type_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec(v_a_790_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_811_, v_x_812_, v_x_813_);
lean_dec(v_x_813_);
lean_dec_ref(v_x_812_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_816_, lean_object* v_inst_817_, lean_object* v_a_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_816_, v_a_818_, v___y_819_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_831_, lean_object* v_inst_832_, lean_object* v_a_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_831_, v_inst_832_, v_a_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec(v___y_834_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_850_, v_x_851_, v_x_852_);
lean_dec(v_x_852_);
lean_dec_ref(v_x_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, size_t v_x_856_, size_t v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_855_, v_x_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
size_t v_x_33958__boxed_867_; size_t v_x_33959__boxed_868_; lean_object* v_res_869_; 
v_x_33958__boxed_867_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_x_33959__boxed_868_ = lean_unbox_usize(v_x_864_);
lean_dec(v_x_864_);
v_res_869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_861_, v_x_862_, v_x_33958__boxed_867_, v_x_33959__boxed_868_, v_x_865_, v_x_866_);
return v_res_869_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, size_t v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_871_, v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
size_t v_x_33975__boxed_879_; uint8_t v_res_880_; lean_object* v_r_881_; 
v_x_33975__boxed_879_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_880_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_875_, v_x_876_, v_x_33975__boxed_879_, v_x_878_);
lean_dec(v_x_878_);
lean_dec_ref(v_x_876_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, size_t v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_883_, v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
size_t v_x_33986__boxed_891_; lean_object* v_res_892_; 
v_x_33986__boxed_891_ = lean_unbox_usize(v_x_889_);
lean_dec(v_x_889_);
v_res_892_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_887_, v_x_888_, v_x_33986__boxed_891_, v_x_890_);
lean_dec(v_x_890_);
lean_dec_ref(v_x_888_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_893_, lean_object* v_n_894_, lean_object* v_k_895_, lean_object* v_v_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_894_, v_k_895_, v_v_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_898_, size_t v_depth_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_entries_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_899_, v_keys_900_, v_vals_901_, v_i_903_, v_entries_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_906_, lean_object* v_depth_907_, lean_object* v_keys_908_, lean_object* v_vals_909_, lean_object* v_heq_910_, lean_object* v_i_911_, lean_object* v_entries_912_){
_start:
{
size_t v_depth_boxed_913_; lean_object* v_res_914_; 
v_depth_boxed_913_ = lean_unbox_usize(v_depth_907_);
lean_dec(v_depth_907_);
v_res_914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_906_, v_depth_boxed_913_, v_keys_908_, v_vals_909_, v_heq_910_, v_i_911_, v_entries_912_);
lean_dec_ref(v_vals_909_);
lean_dec_ref(v_keys_908_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_heq_918_, lean_object* v_i_919_, lean_object* v_k_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_916_, v_i_919_, v_k_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_k_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_922_, v_keys_923_, v_vals_924_, v_heq_925_, v_i_926_, v_k_927_);
lean_dec(v_k_927_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_k_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_931_, v_vals_932_, v_i_934_, v_k_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_k_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_937_, v_keys_938_, v_vals_939_, v_heq_940_, v_i_941_, v_k_942_);
lean_dec(v_k_942_);
lean_dec_ref(v_vals_939_);
lean_dec_ref(v_keys_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_945_, v_x_946_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_env_957_; uint8_t v___x_958_; lean_object* v_env_959_; lean_object* v___x_960_; lean_object* v_toCold_961_; lean_object* v_mctx_962_; lean_object* v_lctx_963_; lean_object* v_options_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_956_ = lean_st_ref_get(v___y_954_);
v_env_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_env_957_);
lean_dec(v___x_956_);
v___x_958_ = 0;
v_env_959_ = l_Lean_Environment_setRecordingDeps(v_env_957_, v___x_958_);
v___x_960_ = lean_st_ref_get(v___y_952_);
v_toCold_961_ = lean_ctor_get(v___y_953_, 0);
v_mctx_962_ = lean_ctor_get(v___x_960_, 0);
lean_inc_ref(v_mctx_962_);
lean_dec(v___x_960_);
v_lctx_963_ = lean_ctor_get(v___y_951_, 2);
v_options_964_ = lean_ctor_get(v_toCold_961_, 2);
lean_inc_ref(v_options_964_);
lean_inc_ref(v_lctx_963_);
v___x_965_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_965_, 0, v_env_959_);
lean_ctor_set(v___x_965_, 1, v_mctx_962_);
lean_ctor_set(v___x_965_, 2, v_lctx_963_);
lean_ctor_set(v___x_965_, 3, v_options_964_);
v___x_966_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v_msgData_950_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_ref_981_; lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_ref_981_ = lean_ctor_get(v___y_978_, 2);
v___x_982_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_991_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_inc(v_ref_981_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_ref_981_);
lean_ctor_set(v___x_987_, 1, v_a_983_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 1);
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_fst_1014_; lean_object* v_snd_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___x_1068_; lean_object* v_mvarId_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_st_ref_get(v_a_1002_);
v_mvarId_1069_ = lean_ctor_get(v___x_1068_, 1);
lean_inc(v_mvarId_1069_);
lean_dec(v___x_1068_);
v___x_1070_ = l_Lean_MVarId_getType(v_mvarId_1069_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
switch(lean_obj_tag(v_a_1071_))
{
case 7:
{
lean_object* v_binderName_1072_; lean_object* v_binderType_1073_; 
v_binderName_1072_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_binderName_1072_);
v_binderType_1073_ = lean_ctor_get(v_a_1071_, 1);
lean_inc_ref(v_binderType_1073_);
lean_dec_ref_known(v_a_1071_, 3);
v_fst_1014_ = v_binderName_1072_;
v_snd_1015_ = v_binderType_1073_;
v___y_1016_ = v_a_1002_;
v___y_1017_ = v_a_1003_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
goto v___jp_1013_;
}
case 8:
{
lean_object* v_declName_1074_; lean_object* v_type_1075_; 
v_declName_1074_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_declName_1074_);
v_type_1075_ = lean_ctor_get(v_a_1071_, 1);
lean_inc_ref(v_type_1075_);
lean_dec_ref_known(v_a_1071_, 4);
v_fst_1014_ = v_declName_1074_;
v_snd_1015_ = v_type_1075_;
v___y_1016_ = v_a_1002_;
v___y_1017_ = v_a_1003_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
goto v___jp_1013_;
}
default: 
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_a_1071_);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1077_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1076_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1070_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1070_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1014_, v_snd_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v_mvarId_1029_; lean_object* v___x_1030_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = lean_st_ref_get(v___y_1016_);
v_mvarId_1029_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_mvarId_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = l_Lean_MVarId_intro(v_mvarId_1029_, v_a_1027_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1051_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1037_; lean_object* v_toGoalState_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_fst_1035_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_fst_1035_);
v_snd_1036_ = lean_ctor_get(v_a_1031_, 1);
lean_inc(v_snd_1036_);
lean_dec(v_a_1031_);
v___x_1037_ = lean_st_ref_take(v___y_1016_);
v_toGoalState_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v___x_1037_, 1);
lean_dec(v_unused_1050_);
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_toGoalState_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v_snd_1036_);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_toGoalState_1038_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_snd_1036_);
v___x_1043_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_st_ref_put(v___y_1016_, v___x_1043_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_fst_1035_);
v___x_1046_ = v___x_1033_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1035_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1030_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1030_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1026_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1026_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec(v_a_1094_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1107_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1120_, v_msg_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc(v___y_1135_);
v___x_1146_ = lean_apply_11(v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec(v___y_1148_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___f_1173_; lean_object* v___x_1174_; 
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc(v___y_1162_);
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1173_, 0, v_x_1161_);
lean_closure_set(v___f_1173_, 1, v___y_1162_);
lean_closure_set(v___f_1173_, 2, v___y_1163_);
lean_closure_set(v___f_1173_, 3, v___y_1164_);
lean_closure_set(v___f_1173_, 4, v___y_1165_);
lean_closure_set(v___f_1173_, 5, v___y_1166_);
lean_closure_set(v___f_1173_, 6, v___y_1167_);
v___x_1174_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1160_, v___f_1173_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1174_) == 0)
{
return v___x_1174_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1183_, lean_object* v_x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1183_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1197_, lean_object* v_mvarId_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1198_, v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_mvarId_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1212_, v_mvarId_1213_, v_x_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec(v___y_1215_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1228_);
v___x_1238_ = lean_apply_10(v_x_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, lean_box(0));
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___f_1263_; lean_object* v___x_1264_; 
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1263_, 0, v_x_1252_);
lean_closure_set(v___f_1263_, 1, v___y_1253_);
lean_closure_set(v___f_1263_, 2, v___y_1254_);
lean_closure_set(v___f_1263_, 3, v___y_1255_);
lean_closure_set(v___f_1263_, 4, v___y_1256_);
lean_closure_set(v___f_1263_, 5, v___y_1257_);
v___x_1264_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1251_, v___f_1263_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
return v___x_1264_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1273_, v_x_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1286_, lean_object* v_mvarId_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1287_, v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_mvarId_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1300_, v_mvarId_1301_, v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1314_, lean_object* v_generation_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
lean_inc(v_a_1314_);
v___x_1327_ = l_Lean_FVarId_getDecl___redArg(v_a_1314_, v___y_1322_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = l_Lean_LocalDecl_type(v_a_1328_);
lean_dec(v_a_1328_);
lean_inc_ref(v___x_1329_);
v___x_1330_ = l_Lean_Meta_isProp(v___x_1329_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; uint8_t v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = lean_unbox(v_a_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref(v___x_1329_);
lean_inc(v_a_1314_);
v___x_1333_ = l_Lean_FVarId_getDecl___redArg(v_a_1314_, v___y_1322_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
v___x_1336_ = l_Lean_LocalDecl_value(v_a_1334_, v___x_1335_);
lean_dec(v_a_1334_);
v___x_1337_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1336_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
lean_inc(v_a_1314_);
v___x_1339_ = l_Lean_mkFVar(v_a_1314_);
v___x_1340_ = l_Lean_Meta_Sym_shareCommon(v___x_1339_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
lean_inc(v_a_1338_);
v___x_1342_ = l_Lean_Meta_Simp_Result_getProof(v_a_1338_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_expr_1344_; lean_object* v___x_1345_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_expr_1344_ = lean_ctor_get(v_a_1338_, 0);
lean_inc_ref(v_expr_1344_);
lean_dec(v_a_1338_);
v___x_1345_ = l_Lean_Meta_Grind_addNewEq(v_a_1341_, v_expr_1344_, v_a_1343_, v_generation_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1354_; 
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v___x_1345_, 0);
lean_dec(v_unused_1355_);
v___x_1347_ = v___x_1345_;
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v___x_1345_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_st_ref_get(v___y_1316_);
v___x_1350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1314_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_a_1314_);
v_a_1356_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1345_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1345_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1341_);
lean_dec(v_a_1338_);
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1364_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1342_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1342_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_a_1338_);
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1372_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1340_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1340_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1380_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1337_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1337_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1331_);
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1388_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1333_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1333_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec(v_a_1331_);
lean_dec(v_generation_1315_);
v___x_1396_ = lean_st_ref_get(v___y_1316_);
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1329_);
v___x_1398_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1397_, v___x_1329_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_mvarId_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_mvarId_1400_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_mvarId_1400_);
lean_dec(v___x_1396_);
v___x_1401_ = l_Lean_mkFVar(v_a_1314_);
v___x_1402_ = l_Lean_MVarId_assert(v_mvarId_1400_, v_a_1399_, v___x_1329_, v___x_1401_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1421_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1421_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1421_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v_toGoalState_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1419_; 
v___x_1407_ = lean_st_ref_get(v___y_1316_);
v_toGoalState_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1407_, 1);
lean_dec(v_unused_1420_);
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1419_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_toGoalState_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1419_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_a_1403_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_toGoalState_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1403_);
v___x_1413_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1414_);
v___x_1416_ = v___x_1405_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1402_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1402_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v___x_1396_);
lean_dec_ref(v___x_1329_);
lean_dec(v_a_1314_);
v_a_1430_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1398_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1398_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___x_1329_);
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1438_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1330_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1330_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_generation_1315_);
lean_dec(v_a_1314_);
v_a_1446_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1327_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1327_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1454_, lean_object* v_generation_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1454_, v_generation_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v_ks_1472_; lean_object* v_vs_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1497_; 
v_ks_1472_ = lean_ctor_get(v_x_1468_, 0);
v_vs_1473_ = lean_ctor_get(v_x_1468_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1475_ = v_x_1468_;
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_vs_1473_);
lean_inc(v_ks_1472_);
lean_dec(v_x_1468_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_array_get_size(v_ks_1472_);
v___x_1478_ = lean_nat_dec_lt(v_x_1469_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_x_1469_);
v___x_1479_ = lean_array_push(v_ks_1472_, v_x_1470_);
v___x_1480_ = lean_array_push(v_vs_1473_, v_x_1471_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1480_);
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1482_ = v___x_1475_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
else
{
lean_object* v_k_x27_1484_; uint8_t v___x_1485_; 
v_k_x27_1484_ = lean_array_fget_borrowed(v_ks_1472_, v_x_1469_);
v___x_1485_ = l_Lean_instBEqMVarId_beq(v_x_1470_, v_k_x27_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1487_; 
if (v_isShared_1476_ == 0)
{
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_ks_1472_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_vs_1473_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_x_1469_, v___x_1488_);
lean_dec(v_x_1469_);
v_x_1468_ = v___x_1487_;
v_x_1469_ = v___x_1489_;
goto _start;
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_array_fset(v_ks_1472_, v_x_1469_, v_x_1470_);
v___x_1493_ = lean_array_fset(v_vs_1473_, v_x_1469_, v_x_1471_);
lean_dec(v_x_1469_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1493_);
lean_ctor_set(v___x_1475_, 0, v___x_1492_);
v___x_1495_ = v___x_1475_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1498_, lean_object* v_k_1499_, lean_object* v_v_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1498_, v___x_1501_, v_k_1499_, v_v_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1503_, size_t v_x_1504_, size_t v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v_es_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v_j_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_es_1508_ = lean_ctor_get(v_x_1503_, 0);
v___x_1509_ = ((size_t)31ULL);
v___x_1510_ = lean_usize_land(v_x_1504_, v___x_1509_);
v_j_1511_ = lean_usize_to_nat(v___x_1510_);
v___x_1512_ = lean_array_get_size(v_es_1508_);
v___x_1513_ = lean_nat_dec_lt(v_j_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_dec(v_j_1511_);
lean_dec(v_x_1507_);
lean_dec(v_x_1506_);
return v_x_1503_;
}
else
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1552_; 
lean_inc_ref(v_es_1508_);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v_x_1503_, 0);
lean_dec(v_unused_1553_);
v___x_1515_ = v_x_1503_;
v_isShared_1516_ = v_isSharedCheck_1552_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_x_1503_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1552_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_v_1517_; lean_object* v___x_1518_; lean_object* v_xs_x27_1519_; lean_object* v___y_1521_; 
v_v_1517_ = lean_array_fget(v_es_1508_, v_j_1511_);
v___x_1518_ = lean_box(0);
v_xs_x27_1519_ = lean_array_fset(v_es_1508_, v_j_1511_, v___x_1518_);
switch(lean_obj_tag(v_v_1517_))
{
case 0:
{
lean_object* v_key_1526_; lean_object* v_val_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1537_; 
v_key_1526_ = lean_ctor_get(v_v_1517_, 0);
v_val_1527_ = lean_ctor_get(v_v_1517_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_v_1517_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1529_ = v_v_1517_;
v_isShared_1530_ = v_isSharedCheck_1537_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_val_1527_);
lean_inc(v_key_1526_);
lean_dec(v_v_1517_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1537_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Lean_instBEqMVarId_beq(v_x_1506_, v_key_1526_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_del_object(v___x_1529_);
v___x_1532_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1526_, v_val_1527_, v_x_1506_, v_x_1507_);
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
v___y_1521_ = v___x_1533_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1535_; 
lean_dec(v_val_1527_);
lean_dec(v_key_1526_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v_x_1507_);
lean_ctor_set(v___x_1529_, 0, v_x_1506_);
v___x_1535_ = v___x_1529_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_x_1506_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_x_1507_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v___y_1521_ = v___x_1535_;
goto v___jp_1520_;
}
}
}
}
case 1:
{
lean_object* v_node_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1550_; 
v_node_1538_ = lean_ctor_get(v_v_1517_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_v_1517_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1540_ = v_v_1517_;
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_node_1538_);
lean_dec(v_v_1517_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
size_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1542_ = ((size_t)5ULL);
v___x_1543_ = lean_usize_shift_right(v_x_1504_, v___x_1542_);
v___x_1544_ = ((size_t)1ULL);
v___x_1545_ = lean_usize_add(v_x_1505_, v___x_1544_);
v___x_1546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1538_, v___x_1543_, v___x_1545_, v_x_1506_, v_x_1507_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1546_);
v___x_1548_ = v___x_1540_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
v___y_1521_ = v___x_1548_;
goto v___jp_1520_;
}
}
}
default: 
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_x_1506_);
lean_ctor_set(v___x_1551_, 1, v_x_1507_);
v___y_1521_ = v___x_1551_;
goto v___jp_1520_;
}
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_array_fset(v_xs_x27_1519_, v_j_1511_, v___y_1521_);
lean_dec(v_j_1511_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1522_);
v___x_1524_ = v___x_1515_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_ks_1554_; lean_object* v_vs_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1573_; 
v_ks_1554_ = lean_ctor_get(v_x_1503_, 0);
v_vs_1555_ = lean_ctor_get(v_x_1503_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1503_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1557_ = v_x_1503_;
v_isShared_1558_ = v_isSharedCheck_1573_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_vs_1555_);
lean_inc(v_ks_1554_);
lean_dec(v_x_1503_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1573_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_ks_1554_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_vs_1555_);
v___x_1560_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v_newNode_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v_newNode_1561_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1560_, v_x_1506_, v_x_1507_);
v___x_1562_ = ((size_t)7ULL);
v___x_1563_ = lean_usize_dec_le(v___x_1562_, v_x_1505_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1561_);
v___x_1565_ = lean_unsigned_to_nat(4u);
v___x_1566_ = lean_nat_dec_lt(v___x_1564_, v___x_1565_);
lean_dec(v___x_1564_);
if (v___x_1566_ == 0)
{
lean_object* v_ks_1567_; lean_object* v_vs_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_ks_1567_ = lean_ctor_get(v_newNode_1561_, 0);
lean_inc_ref(v_ks_1567_);
v_vs_1568_ = lean_ctor_get(v_newNode_1561_, 1);
lean_inc_ref(v_vs_1568_);
lean_dec_ref(v_newNode_1561_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1505_, v_ks_1567_, v_vs_1568_, v___x_1569_, v___x_1570_);
lean_dec_ref(v_vs_1568_);
lean_dec_ref(v_ks_1567_);
return v___x_1571_;
}
else
{
return v_newNode_1561_;
}
}
else
{
return v_newNode_1561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1574_, lean_object* v_keys_1575_, lean_object* v_vals_1576_, lean_object* v_i_1577_, lean_object* v_entries_1578_){
_start:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_array_get_size(v_keys_1575_);
v___x_1580_ = lean_nat_dec_lt(v_i_1577_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v_i_1577_);
return v_entries_1578_;
}
else
{
lean_object* v_k_1581_; lean_object* v_v_1582_; uint64_t v___x_1583_; size_t v_h_1584_; size_t v___x_1585_; lean_object* v___x_1586_; size_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v_h_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_k_1581_ = lean_array_fget_borrowed(v_keys_1575_, v_i_1577_);
v_v_1582_ = lean_array_fget_borrowed(v_vals_1576_, v_i_1577_);
v___x_1583_ = l_Lean_instHashableMVarId_hash(v_k_1581_);
v_h_1584_ = lean_uint64_to_usize(v___x_1583_);
v___x_1585_ = ((size_t)5ULL);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_sub(v_depth_1574_, v___x_1587_);
v___x_1589_ = lean_usize_mul(v___x_1585_, v___x_1588_);
v_h_1590_ = lean_usize_shift_right(v_h_1584_, v___x_1589_);
v___x_1591_ = lean_nat_add(v_i_1577_, v___x_1586_);
lean_dec(v_i_1577_);
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
v___x_1592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1578_, v_h_1590_, v_depth_1574_, v_k_1581_, v_v_1582_);
v_i_1577_ = v___x_1591_;
v_entries_1578_ = v___x_1592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1594_, lean_object* v_keys_1595_, lean_object* v_vals_1596_, lean_object* v_i_1597_, lean_object* v_entries_1598_){
_start:
{
size_t v_depth_boxed_1599_; lean_object* v_res_1600_; 
v_depth_boxed_1599_ = lean_unbox_usize(v_depth_1594_);
lean_dec(v_depth_1594_);
v_res_1600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1599_, v_keys_1595_, v_vals_1596_, v_i_1597_, v_entries_1598_);
lean_dec_ref(v_vals_1596_);
lean_dec_ref(v_keys_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
size_t v_x_152422__boxed_1606_; size_t v_x_152423__boxed_1607_; lean_object* v_res_1608_; 
v_x_152422__boxed_1606_ = lean_unbox_usize(v_x_1602_);
lean_dec(v_x_1602_);
v_x_152423__boxed_1607_ = lean_unbox_usize(v_x_1603_);
lean_dec(v_x_1603_);
v_res_1608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1601_, v_x_152422__boxed_1606_, v_x_152423__boxed_1607_, v_x_1604_, v_x_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
uint64_t v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = l_Lean_instHashableMVarId_hash(v_x_1610_);
v___x_1613_ = lean_uint64_to_usize(v___x_1612_);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1609_, v___x_1613_, v___x_1614_, v_x_1610_, v_x_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1616_, lean_object* v_val_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v_mctx_1621_; lean_object* v_cache_1622_; lean_object* v_zetaDeltaFVarIds_1623_; lean_object* v_postponed_1624_; lean_object* v_diag_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1655_; 
v___x_1620_ = lean_st_ref_take(v___y_1618_);
v_mctx_1621_ = lean_ctor_get(v___x_1620_, 0);
v_cache_1622_ = lean_ctor_get(v___x_1620_, 1);
v_zetaDeltaFVarIds_1623_ = lean_ctor_get(v___x_1620_, 2);
v_postponed_1624_ = lean_ctor_get(v___x_1620_, 3);
v_diag_1625_ = lean_ctor_get(v___x_1620_, 4);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1627_ = v___x_1620_;
v_isShared_1628_ = v_isSharedCheck_1655_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_diag_1625_);
lean_inc(v_postponed_1624_);
lean_inc(v_zetaDeltaFVarIds_1623_);
lean_inc(v_cache_1622_);
lean_inc(v_mctx_1621_);
lean_dec(v___x_1620_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1655_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_depth_1629_; lean_object* v_levelAssignDepth_1630_; lean_object* v_lmvarCounter_1631_; lean_object* v_mvarCounter_1632_; lean_object* v_lDecls_1633_; lean_object* v_decls_1634_; lean_object* v_userNames_1635_; lean_object* v_lAssignment_1636_; lean_object* v_eAssignment_1637_; lean_object* v_dAssignment_1638_; lean_object* v_instanceTypedMVars_1639_; lean_object* v_synthNormMemo_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1654_; 
v_depth_1629_ = lean_ctor_get(v_mctx_1621_, 0);
v_levelAssignDepth_1630_ = lean_ctor_get(v_mctx_1621_, 1);
v_lmvarCounter_1631_ = lean_ctor_get(v_mctx_1621_, 2);
v_mvarCounter_1632_ = lean_ctor_get(v_mctx_1621_, 3);
v_lDecls_1633_ = lean_ctor_get(v_mctx_1621_, 4);
v_decls_1634_ = lean_ctor_get(v_mctx_1621_, 5);
v_userNames_1635_ = lean_ctor_get(v_mctx_1621_, 6);
v_lAssignment_1636_ = lean_ctor_get(v_mctx_1621_, 7);
v_eAssignment_1637_ = lean_ctor_get(v_mctx_1621_, 8);
v_dAssignment_1638_ = lean_ctor_get(v_mctx_1621_, 9);
v_instanceTypedMVars_1639_ = lean_ctor_get(v_mctx_1621_, 10);
v_synthNormMemo_1640_ = lean_ctor_get(v_mctx_1621_, 11);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_mctx_1621_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1642_ = v_mctx_1621_;
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_synthNormMemo_1640_);
lean_inc(v_instanceTypedMVars_1639_);
lean_inc(v_dAssignment_1638_);
lean_inc(v_eAssignment_1637_);
lean_inc(v_lAssignment_1636_);
lean_inc(v_userNames_1635_);
lean_inc(v_decls_1634_);
lean_inc(v_lDecls_1633_);
lean_inc(v_mvarCounter_1632_);
lean_inc(v_lmvarCounter_1631_);
lean_inc(v_levelAssignDepth_1630_);
lean_inc(v_depth_1629_);
lean_dec(v_mctx_1621_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1654_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1637_, v_mvarId_1616_, v_val_1617_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 8, v___x_1645_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_depth_1629_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_levelAssignDepth_1630_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_lmvarCounter_1631_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_mvarCounter_1632_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_lDecls_1633_);
lean_ctor_set(v_reuseFailAlloc_1653_, 5, v_decls_1634_);
lean_ctor_set(v_reuseFailAlloc_1653_, 6, v_userNames_1635_);
lean_ctor_set(v_reuseFailAlloc_1653_, 7, v_lAssignment_1636_);
lean_ctor_set(v_reuseFailAlloc_1653_, 8, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1653_, 9, v_dAssignment_1638_);
lean_ctor_set(v_reuseFailAlloc_1653_, 10, v_instanceTypedMVars_1639_);
lean_ctor_set(v_reuseFailAlloc_1653_, 11, v_synthNormMemo_1640_);
v___x_1647_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1647_);
v___x_1649_ = v___x_1627_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_cache_1622_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_zetaDeltaFVarIds_1623_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_postponed_1624_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_diag_1625_);
v___x_1649_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_st_ref_put(v___y_1618_, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1644_);
return v___x_1651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1656_, lean_object* v_val_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1656_, v_val_1657_, v___y_1658_);
lean_dec(v___y_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v_ngen_1664_; lean_object* v_namePrefix_1665_; lean_object* v_idx_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1696_; 
v___x_1663_ = lean_st_ref_get(v___y_1661_);
v_ngen_1664_ = lean_ctor_get(v___x_1663_, 2);
lean_inc_ref(v_ngen_1664_);
lean_dec(v___x_1663_);
v_namePrefix_1665_ = lean_ctor_get(v_ngen_1664_, 0);
v_idx_1666_ = lean_ctor_get(v_ngen_1664_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_ngen_1664_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1668_ = v_ngen_1664_;
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_idx_1666_);
lean_inc(v_namePrefix_1665_);
lean_dec(v_ngen_1664_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_r_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_inc(v_idx_1666_);
lean_inc(v_namePrefix_1665_);
v_r_1670_ = l_Lean_Name_num___override(v_namePrefix_1665_, v_idx_1666_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_idx_1666_, v___x_1671_);
lean_dec(v_idx_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v___x_1672_);
v___x_1674_ = v___x_1668_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_namePrefix_1665_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v_env_1676_; lean_object* v_nextMacroScope_1677_; lean_object* v_auxDeclNGen_1678_; lean_object* v_traceState_1679_; lean_object* v_cache_1680_; lean_object* v_recordedDeps_1681_; lean_object* v_messages_1682_; lean_object* v_infoState_1683_; lean_object* v_snapshotTasks_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1693_; 
v___x_1675_ = lean_st_ref_take(v___y_1661_);
v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
v_nextMacroScope_1677_ = lean_ctor_get(v___x_1675_, 1);
v_auxDeclNGen_1678_ = lean_ctor_get(v___x_1675_, 3);
v_traceState_1679_ = lean_ctor_get(v___x_1675_, 4);
v_cache_1680_ = lean_ctor_get(v___x_1675_, 5);
v_recordedDeps_1681_ = lean_ctor_get(v___x_1675_, 6);
v_messages_1682_ = lean_ctor_get(v___x_1675_, 7);
v_infoState_1683_ = lean_ctor_get(v___x_1675_, 8);
v_snapshotTasks_1684_ = lean_ctor_get(v___x_1675_, 9);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1675_, 2);
lean_dec(v_unused_1694_);
v___x_1686_ = v___x_1675_;
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snapshotTasks_1684_);
lean_inc(v_infoState_1683_);
lean_inc(v_messages_1682_);
lean_inc(v_recordedDeps_1681_);
lean_inc(v_cache_1680_);
lean_inc(v_traceState_1679_);
lean_inc(v_auxDeclNGen_1678_);
lean_inc(v_nextMacroScope_1677_);
lean_inc(v_env_1676_);
lean_dec(v___x_1675_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 2, v___x_1674_);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_env_1676_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_nextMacroScope_1677_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_auxDeclNGen_1678_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v_traceState_1679_);
lean_ctor_set(v_reuseFailAlloc_1692_, 5, v_cache_1680_);
lean_ctor_set(v_reuseFailAlloc_1692_, 6, v_recordedDeps_1681_);
lean_ctor_set(v_reuseFailAlloc_1692_, 7, v_messages_1682_);
lean_ctor_set(v_reuseFailAlloc_1692_, 8, v_infoState_1683_);
lean_ctor_set(v_reuseFailAlloc_1692_, 9, v_snapshotTasks_1684_);
v___x_1689_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_st_ref_put(v___y_1661_, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_r_1670_);
return v___x_1691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1697_);
lean_dec(v___y_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v___x_1711_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1709_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec(v___y_1720_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1737_, lean_object* v_a_1738_, uint8_t v___x_1739_, uint8_t v___x_1740_, uint8_t v___x_1741_, lean_object* v_a_1742_, lean_object* v___x_1743_, lean_object* v_expr_1744_, lean_object* v___x_1745_, lean_object* v_val_1746_, lean_object* v_mvarId_1747_, lean_object* v___x_1748_, lean_object* v_a_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Meta_mkLambdaFVars(v___x_1737_, v_a_1738_, v___x_1739_, v___x_1740_, v___x_1739_, v___x_1740_, v___x_1741_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1742_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_mkConst(v___x_1763_, v___x_1765_);
v___x_1767_ = lean_unsigned_to_nat(5u);
v___x_1768_ = lean_mk_empty_array_with_capacity(v___x_1767_);
v___x_1769_ = lean_array_push(v___x_1768_, v___x_1743_);
v___x_1770_ = lean_array_push(v___x_1769_, v_expr_1744_);
v___x_1771_ = lean_array_push(v___x_1770_, v___x_1745_);
v___x_1772_ = lean_array_push(v___x_1771_, v_val_1746_);
v___x_1773_ = lean_array_push(v___x_1772_, v_a_1762_);
v___x_1774_ = l_Lean_mkAppN(v___x_1766_, v___x_1773_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1747_, v___x_1774_, v___y_1757_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1793_; 
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v___x_1775_, 0);
lean_dec(v_unused_1794_);
v___x_1777_ = v___x_1775_;
v_isShared_1778_ = v_isSharedCheck_1793_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v___x_1775_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1793_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v_toGoalState_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1791_; 
v___x_1779_ = lean_st_ref_get(v___y_1750_);
v_toGoalState_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v___x_1779_, 1);
lean_dec(v_unused_1792_);
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1791_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_toGoalState_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1791_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v___x_1748_);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_toGoalState_1780_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1748_);
v___x_1785_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_a_1749_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1786_);
v___x_1788_ = v___x_1777_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1749_);
lean_dec(v___x_1748_);
v_a_1795_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1775_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1775_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1749_);
lean_dec(v___x_1748_);
lean_dec(v_mvarId_1747_);
lean_dec_ref(v_val_1746_);
lean_dec_ref(v___x_1745_);
lean_dec_ref(v_expr_1744_);
lean_dec_ref(v___x_1743_);
lean_dec(v_a_1742_);
v_a_1803_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1761_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1761_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1811_ = _args[0];
lean_object* v_a_1812_ = _args[1];
lean_object* v___x_1813_ = _args[2];
lean_object* v___x_1814_ = _args[3];
lean_object* v___x_1815_ = _args[4];
lean_object* v_a_1816_ = _args[5];
lean_object* v___x_1817_ = _args[6];
lean_object* v_expr_1818_ = _args[7];
lean_object* v___x_1819_ = _args[8];
lean_object* v_val_1820_ = _args[9];
lean_object* v_mvarId_1821_ = _args[10];
lean_object* v___x_1822_ = _args[11];
lean_object* v_a_1823_ = _args[12];
lean_object* v___y_1824_ = _args[13];
lean_object* v___y_1825_ = _args[14];
lean_object* v___y_1826_ = _args[15];
lean_object* v___y_1827_ = _args[16];
lean_object* v___y_1828_ = _args[17];
lean_object* v___y_1829_ = _args[18];
lean_object* v___y_1830_ = _args[19];
lean_object* v___y_1831_ = _args[20];
lean_object* v___y_1832_ = _args[21];
lean_object* v___y_1833_ = _args[22];
lean_object* v___y_1834_ = _args[23];
_start:
{
uint8_t v___x_152744__boxed_1835_; uint8_t v___x_152745__boxed_1836_; uint8_t v___x_152746__boxed_1837_; lean_object* v_res_1838_; 
v___x_152744__boxed_1835_ = lean_unbox(v___x_1813_);
v___x_152745__boxed_1836_ = lean_unbox(v___x_1814_);
v___x_152746__boxed_1837_ = lean_unbox(v___x_1815_);
v_res_1838_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1811_, v_a_1812_, v___x_152744__boxed_1835_, v___x_152745__boxed_1836_, v___x_152746__boxed_1837_, v_a_1816_, v___x_1817_, v_expr_1818_, v___x_1819_, v_val_1820_, v_mvarId_1821_, v___x_1822_, v_a_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___x_1811_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1844_, lean_object* v_a_1845_, uint8_t v___x_1846_, uint8_t v___x_1847_, uint8_t v___x_1848_, lean_object* v_a_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v_expr_1852_, lean_object* v___x_1853_, lean_object* v_val_1854_, lean_object* v_mvarId_1855_, lean_object* v___x_1856_, lean_object* v_a_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_Meta_mkLambdaFVars(v___x_1844_, v_a_1845_, v___x_1846_, v___x_1847_, v___x_1846_, v___x_1847_, v___x_1848_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1849_);
lean_ctor_set(v___x_1872_, 1, v___x_1850_);
v___x_1873_ = l_Lean_mkConst(v___x_1871_, v___x_1872_);
v___x_1874_ = lean_unsigned_to_nat(5u);
v___x_1875_ = lean_mk_empty_array_with_capacity(v___x_1874_);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1851_);
v___x_1877_ = lean_array_push(v___x_1876_, v_expr_1852_);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1853_);
v___x_1879_ = lean_array_push(v___x_1878_, v_val_1854_);
v___x_1880_ = lean_array_push(v___x_1879_, v_a_1870_);
v___x_1881_ = l_Lean_mkAppN(v___x_1873_, v___x_1880_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1855_, v___x_1881_, v___y_1865_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1900_; 
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v___x_1882_, 0);
lean_dec(v_unused_1901_);
v___x_1884_ = v___x_1882_;
v_isShared_1885_ = v_isSharedCheck_1900_;
goto v_resetjp_1883_;
}
else
{
lean_dec(v___x_1882_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1900_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v_toGoalState_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1898_; 
v___x_1886_ = lean_st_ref_get(v___y_1858_);
v_toGoalState_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1886_, 1);
lean_dec(v_unused_1899_);
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_toGoalState_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1856_);
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_toGoalState_1887_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1856_);
v___x_1892_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_a_1857_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1893_);
v___x_1895_ = v___x_1884_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1857_);
lean_dec(v___x_1856_);
v_a_1902_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1882_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1882_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_a_1857_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1855_);
lean_dec_ref(v_val_1854_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_expr_1852_);
lean_dec_ref(v___x_1851_);
lean_dec(v___x_1850_);
lean_dec(v_a_1849_);
v_a_1910_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1869_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1869_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1918_ = _args[0];
lean_object* v_a_1919_ = _args[1];
lean_object* v___x_1920_ = _args[2];
lean_object* v___x_1921_ = _args[3];
lean_object* v___x_1922_ = _args[4];
lean_object* v_a_1923_ = _args[5];
lean_object* v___x_1924_ = _args[6];
lean_object* v___x_1925_ = _args[7];
lean_object* v_expr_1926_ = _args[8];
lean_object* v___x_1927_ = _args[9];
lean_object* v_val_1928_ = _args[10];
lean_object* v_mvarId_1929_ = _args[11];
lean_object* v___x_1930_ = _args[12];
lean_object* v_a_1931_ = _args[13];
lean_object* v___y_1932_ = _args[14];
lean_object* v___y_1933_ = _args[15];
lean_object* v___y_1934_ = _args[16];
lean_object* v___y_1935_ = _args[17];
lean_object* v___y_1936_ = _args[18];
lean_object* v___y_1937_ = _args[19];
lean_object* v___y_1938_ = _args[20];
lean_object* v___y_1939_ = _args[21];
lean_object* v___y_1940_ = _args[22];
lean_object* v___y_1941_ = _args[23];
lean_object* v___y_1942_ = _args[24];
_start:
{
uint8_t v___x_152926__boxed_1943_; uint8_t v___x_152927__boxed_1944_; uint8_t v___x_152928__boxed_1945_; lean_object* v_res_1946_; 
v___x_152926__boxed_1943_ = lean_unbox(v___x_1920_);
v___x_152927__boxed_1944_ = lean_unbox(v___x_1921_);
v___x_152928__boxed_1945_ = lean_unbox(v___x_1922_);
v_res_1946_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1918_, v_a_1919_, v___x_152926__boxed_1943_, v___x_152927__boxed_1944_, v___x_152928__boxed_1945_, v_a_1923_, v___x_1924_, v___x_1925_, v_expr_1926_, v___x_1927_, v_val_1928_, v_mvarId_1929_, v___x_1930_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___x_1918_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1947_, lean_object* v_a_1948_, uint8_t v___x_1949_, uint8_t v___x_1950_, uint8_t v___x_1951_, lean_object* v_mvarId_1952_, lean_object* v___x_1953_, lean_object* v_a_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Meta_mkLambdaFVars(v___x_1947_, v_a_1948_, v___x_1949_, v___x_1950_, v___x_1949_, v___x_1950_, v___x_1951_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1952_, v_a_1967_, v___y_1962_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1986_; 
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1987_);
v___x_1970_ = v___x_1968_;
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v___x_1968_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v_toGoalState_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1984_; 
v___x_1972_ = lean_st_ref_get(v___y_1955_);
v_toGoalState_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1972_, 1);
lean_dec(v_unused_1985_);
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_toGoalState_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_1953_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_toGoalState_1973_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1953_);
v___x_1978_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1954_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1979_);
v___x_1981_ = v___x_1970_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_a_1954_);
lean_dec(v___x_1953_);
v_a_1988_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1968_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1968_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_a_1954_);
lean_dec(v___x_1953_);
lean_dec(v_mvarId_1952_);
v_a_1996_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1966_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1966_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2004_ = _args[0];
lean_object* v_a_2005_ = _args[1];
lean_object* v___x_2006_ = _args[2];
lean_object* v___x_2007_ = _args[3];
lean_object* v___x_2008_ = _args[4];
lean_object* v_mvarId_2009_ = _args[5];
lean_object* v___x_2010_ = _args[6];
lean_object* v_a_2011_ = _args[7];
lean_object* v___y_2012_ = _args[8];
lean_object* v___y_2013_ = _args[9];
lean_object* v___y_2014_ = _args[10];
lean_object* v___y_2015_ = _args[11];
lean_object* v___y_2016_ = _args[12];
lean_object* v___y_2017_ = _args[13];
lean_object* v___y_2018_ = _args[14];
lean_object* v___y_2019_ = _args[15];
lean_object* v___y_2020_ = _args[16];
lean_object* v___y_2021_ = _args[17];
lean_object* v___y_2022_ = _args[18];
_start:
{
uint8_t v___x_153097__boxed_2023_; uint8_t v___x_153098__boxed_2024_; uint8_t v___x_153099__boxed_2025_; lean_object* v_res_2026_; 
v___x_153097__boxed_2023_ = lean_unbox(v___x_2006_);
v___x_153098__boxed_2024_ = lean_unbox(v___x_2007_);
v___x_153099__boxed_2025_ = lean_unbox(v___x_2008_);
v_res_2026_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2004_, v_a_2005_, v___x_153097__boxed_2023_, v___x_153098__boxed_2024_, v___x_153099__boxed_2025_, v_mvarId_2009_, v___x_2010_, v_a_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___x_2004_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2029_, lean_object* v___x_2030_, lean_object* v_generation_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
lean_inc(v_mvarId_2029_);
v___x_2043_ = l_Lean_MVarId_getTag(v_mvarId_2029_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2030_, v_a_2044_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_n(v_a_2046_, 2);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2029_, v_a_2046_, v___y_2039_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; lean_object* v_toGoalState_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = lean_st_ref_get(v___y_2032_);
v_toGoalState_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v___x_2048_, 1);
lean_dec(v_unused_2059_);
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_toGoalState_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_Expr_mvarId_x21(v_a_2046_);
lean_dec(v_a_2046_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_toGoalState_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; 
v___x_2056_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2055_, v_generation_2031_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2046_);
lean_dec(v_generation_2031_);
v_a_2060_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2047_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2047_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_generation_2031_);
lean_dec(v_mvarId_2029_);
v_a_2068_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2045_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2045_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_generation_2031_);
lean_dec_ref(v___x_2030_);
lean_dec(v_mvarId_2029_);
v_a_2076_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2043_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2043_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2084_, lean_object* v___x_2085_, lean_object* v_generation_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2084_, v___x_2085_, v_generation_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec(v___y_2087_);
return v_res_2098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_box(0);
v___x_2105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2106_ = l_Lean_mkConst(v___x_2105_, v___x_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2107_, lean_object* v_generation_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v_a_2121_; lean_object* v___y_2126_; lean_object* v___x_2136_; lean_object* v_mvarId_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2405_; 
lean_inc_ref(v_goal_2107_);
v___x_2119_ = lean_st_mk_ref(v_goal_2107_);
v___x_2136_ = lean_st_ref_get(v___x_2119_);
v_mvarId_2137_ = lean_ctor_get(v___x_2136_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2136_, 0);
lean_dec(v_unused_2406_);
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2405_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_mvarId_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2405_;
goto v_resetjp_2138_;
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_st_ref_get(v___x_2119_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
v___jp_2125_:
{
if (lean_obj_tag(v___y_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___y_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___y_2126_, 1);
v_a_2121_ = v_a_2127_;
goto v___jp_2120_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v___x_2119_);
v_a_2128_ = lean_ctor_get(v___y_2126_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___y_2126_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___y_2126_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___y_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_MVarId_getType(v_mvarId_2137_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_Expr_isForall(v_a_2142_);
v___x_2144_ = 1;
if (v___x_2143_ == 0)
{
uint8_t v___x_2145_; 
lean_del_object(v___x_2139_);
v___x_2145_ = l_Lean_Expr_isLet(v_a_2142_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_dec(v_a_2142_);
lean_dec_ref(v___y_2114_);
lean_dec(v_generation_2108_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_goal_2107_);
v_a_2121_ = v___x_2146_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2147_; 
lean_dec_ref(v_goal_2107_);
v___x_2147_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2110_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; uint8_t v_zetaDelta_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v_zetaDelta_2149_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*14 + 19);
lean_dec(v_a_2148_);
if (v_zetaDelta_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_a_2142_);
v___x_2150_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v_mvarId_2154_; lean_object* v___x_2155_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___f_2152_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2152_, 0, v_a_2151_);
lean_closure_set(v___f_2152_, 1, v_generation_2108_);
v___x_2153_ = lean_st_ref_get(v___x_2119_);
v_mvarId_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_mvarId_2154_);
lean_dec(v___x_2153_);
v___x_2155_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2154_, v___f_2152_, v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec_ref(v___y_2114_);
v___y_2126_ = v___x_2155_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
lean_dec(v_generation_2108_);
v_a_2156_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2150_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2150_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_mvarId_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; 
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2165_ = l_Lean_Meta_expandLet(v_a_2142_, v___x_2164_, v___x_2144_);
lean_dec(v_a_2142_);
v___x_2166_ = lean_st_ref_get(v___x_2119_);
v_mvarId_2167_ = lean_ctor_get(v___x_2166_, 1);
lean_inc_n(v_mvarId_2167_, 2);
lean_dec(v___x_2166_);
v___f_2168_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2168_, 0, v_mvarId_2167_);
lean_closure_set(v___f_2168_, 1, v___x_2165_);
lean_closure_set(v___f_2168_, 2, v_generation_2108_);
v___x_2169_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2167_, v___f_2168_, v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec_ref(v___y_2114_);
v___y_2126_ = v___x_2169_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
lean_dec(v_generation_2108_);
v_a_2170_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2147_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2147_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec(v_generation_2108_);
lean_dec_ref(v_goal_2107_);
v___x_2178_ = l_Lean_Expr_bindingDomain_x21(v_a_2142_);
lean_inc_ref(v___x_2178_);
v___x_2179_ = l_Lean_Meta_isProp(v___x_2178_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; uint8_t v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = lean_unbox(v_a_2180_);
lean_dec(v_a_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
v___x_2182_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec_ref(v___y_2114_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_st_ref_get(v___x_2119_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 3);
lean_ctor_set(v___x_2139_, 1, v___x_2184_);
lean_ctor_set(v___x_2139_, 0, v_a_2183_);
v___x_2186_ = v___x_2139_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2183_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
v_a_2121_ = v___x_2186_;
goto v___jp_2120_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_del_object(v___x_2139_);
lean_dec(v___x_2119_);
v_a_2188_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2182_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2182_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v_mvarId_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2387_; 
lean_del_object(v___x_2139_);
v___x_2196_ = 0;
v___x_2197_ = lean_st_ref_get(v___x_2119_);
v_mvarId_2198_ = lean_ctor_get(v___x_2197_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2388_);
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2387_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_mvarId_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2387_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; 
lean_inc(v_mvarId_2198_);
v___x_2202_ = l_Lean_MVarId_getTag(v_mvarId_2198_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l_Lean_Expr_bindingBody_x21(v_a_2142_);
v___x_2205_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc_n(v_a_2206_, 2);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = l_Lean_mkFVar(v_a_2206_);
lean_inc_ref(v___x_2178_);
v___x_2208_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2178_, v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_lctx_2210_; lean_object* v_localInstances_2211_; lean_object* v_expr_2212_; lean_object* v_proof_x3f_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v_lctx_2210_ = lean_ctor_get(v___y_2114_, 2);
v_localInstances_2211_ = lean_ctor_get(v___y_2114_, 3);
v_expr_2212_ = lean_ctor_get(v_a_2209_, 0);
lean_inc_ref_n(v_expr_2212_, 2);
v_proof_x3f_2213_ = lean_ctor_get(v_a_2209_, 1);
lean_inc(v_proof_x3f_2213_);
lean_dec(v_a_2209_);
v___x_2214_ = l_Lean_Expr_bindingName_x21(v_a_2142_);
lean_inc(v___x_2214_);
v___x_2215_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2214_, v_expr_2212_, v___x_2119_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; uint8_t v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v_localInsts_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___x_2340_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_Expr_bindingInfo_x21(v_a_2142_);
v___x_2218_ = 0;
lean_inc_ref_n(v_expr_2212_, 2);
lean_inc(v_a_2206_);
lean_inc_ref(v_lctx_2210_);
v___x_2219_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2210_, v_a_2206_, v_a_2216_, v_expr_2212_, v___x_2217_, v___x_2218_);
v___x_2340_ = l_Lean_Meta_isClass_x3f(v_expr_2212_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
if (lean_obj_tag(v_a_2341_) == 1)
{
lean_object* v_val_2342_; lean_object* v___x_2344_; 
v_val_2342_ = lean_ctor_get(v_a_2341_, 0);
lean_inc(v_val_2342_);
lean_dec_ref_known(v_a_2341_, 1);
lean_inc_ref(v___x_2207_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v___x_2207_);
lean_ctor_set(v___x_2200_, 0, v_val_2342_);
v___x_2344_ = v___x_2200_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_val_2342_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2207_);
v___x_2344_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
lean_inc_ref(v_localInstances_2211_);
v___x_2345_ = lean_array_push(v_localInstances_2211_, v___x_2344_);
lean_inc(v___x_2119_);
v_localInsts_2256_ = v___x_2345_;
v___y_2257_ = v___x_2119_;
v___y_2258_ = v___y_2109_;
v___y_2259_ = v___y_2110_;
v___y_2260_ = v___y_2111_;
v___y_2261_ = v___y_2112_;
v___y_2262_ = v___y_2113_;
v___y_2263_ = v___y_2114_;
v___y_2264_ = v___y_2115_;
v___y_2265_ = v___y_2116_;
v___y_2266_ = v___y_2117_;
goto v___jp_2255_;
}
}
else
{
lean_inc_ref(v_localInstances_2211_);
lean_dec(v_a_2341_);
lean_del_object(v___x_2200_);
lean_inc(v___x_2119_);
v_localInsts_2256_ = v_localInstances_2211_;
v___y_2257_ = v___x_2119_;
v___y_2258_ = v___y_2109_;
v___y_2259_ = v___y_2110_;
v___y_2260_ = v___y_2111_;
v___y_2261_ = v___y_2112_;
v___y_2262_ = v___y_2113_;
v___y_2263_ = v___y_2114_;
v___y_2264_ = v___y_2115_;
v___y_2265_ = v___y_2116_;
v___y_2266_ = v___y_2117_;
goto v___jp_2255_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v___x_2219_);
lean_dec(v___x_2214_);
lean_dec(v_proof_x3f_2213_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2203_);
lean_del_object(v___x_2200_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2347_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2340_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2340_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
v___jp_2220_:
{
uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = 2;
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2219_, v___y_2224_, v___y_2232_, v___x_2233_, v_a_2203_, v___x_2234_, v___y_2229_, v___y_2231_, v___y_2228_, v___y_2221_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = l_Lean_Expr_mvarId_x21(v_a_2236_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_mk_empty_array_with_capacity(v___x_2238_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2207_);
v___x_2241_ = 1;
v___x_2242_ = lean_box(v___x_2196_);
v___x_2243_ = lean_box(v___x_2144_);
v___x_2244_ = lean_box(v___x_2241_);
lean_inc(v___x_2237_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2245_, 0, v___x_2240_);
lean_closure_set(v___f_2245_, 1, v_a_2236_);
lean_closure_set(v___f_2245_, 2, v___x_2242_);
lean_closure_set(v___f_2245_, 3, v___x_2243_);
lean_closure_set(v___f_2245_, 4, v___x_2244_);
lean_closure_set(v___f_2245_, 5, v_mvarId_2198_);
lean_closure_set(v___f_2245_, 6, v___x_2237_);
lean_closure_set(v___f_2245_, 7, v_a_2206_);
v___x_2246_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2237_, v___f_2245_, v___y_2227_, v___y_2226_, v___y_2223_, v___y_2222_, v___y_2225_, v___y_2230_, v___y_2229_, v___y_2231_, v___y_2228_, v___y_2221_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2227_);
v___y_2126_ = v___x_2246_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2227_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec(v_mvarId_2198_);
lean_dec(v___x_2119_);
v_a_2247_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2235_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2235_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
v___jp_2255_:
{
if (lean_obj_tag(v_proof_x3f_2213_) == 0)
{
uint8_t v___x_2267_; 
lean_dec(v___x_2214_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2178_);
v___x_2267_ = l_Lean_Expr_isArrow(v_a_2142_);
lean_dec(v_a_2142_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_expr_instantiate1(v___x_2204_, v___x_2207_);
lean_dec_ref(v___x_2204_);
v___y_2221_ = v___y_2266_;
v___y_2222_ = v___y_2260_;
v___y_2223_ = v___y_2259_;
v___y_2224_ = v_localInsts_2256_;
v___y_2225_ = v___y_2261_;
v___y_2226_ = v___y_2258_;
v___y_2227_ = v___y_2257_;
v___y_2228_ = v___y_2265_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___x_2268_;
goto v___jp_2220_;
}
else
{
v___y_2221_ = v___y_2266_;
v___y_2222_ = v___y_2260_;
v___y_2223_ = v___y_2259_;
v___y_2224_ = v_localInsts_2256_;
v___y_2225_ = v___y_2261_;
v___y_2226_ = v___y_2258_;
v___y_2227_ = v___y_2257_;
v___y_2228_ = v___y_2265_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___x_2204_;
goto v___jp_2220_;
}
}
else
{
lean_object* v_val_2269_; uint8_t v___x_2270_; 
v_val_2269_ = lean_ctor_get(v_proof_x3f_2213_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v_proof_x3f_2213_, 1);
v___x_2270_ = l_Lean_Expr_isArrow(v_a_2142_);
lean_dec(v_a_2142_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_inc_ref(v___x_2204_);
lean_inc_ref_n(v___x_2178_, 2);
v___x_2271_ = l_Lean_mkLambda(v___x_2214_, v___x_2217_, v___x_2178_, v___x_2204_);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___x_2207_);
lean_inc(v_val_2269_);
lean_inc_ref(v_expr_2212_);
v___x_2274_ = l_Lean_mkApp4(v___x_2273_, v___x_2178_, v_expr_2212_, v_val_2269_, v___x_2207_);
v___x_2275_ = lean_expr_instantiate1(v___x_2204_, v___x_2274_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2204_);
lean_inc_ref(v___x_2275_);
v___x_2276_ = l_Lean_Meta_getLevel(v___x_2275_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = 2;
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2219_, v_localInsts_2256_, v___x_2275_, v___x_2278_, v_a_2203_, v___x_2279_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_Expr_mvarId_x21(v_a_2281_);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
v___x_2285_ = lean_array_push(v___x_2284_, v___x_2207_);
v___x_2286_ = 1;
v___x_2287_ = lean_box(v___x_2270_);
v___x_2288_ = lean_box(v___x_2144_);
v___x_2289_ = lean_box(v___x_2286_);
lean_inc(v___x_2282_);
v___f_2290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2290_, 0, v___x_2285_);
lean_closure_set(v___f_2290_, 1, v_a_2281_);
lean_closure_set(v___f_2290_, 2, v___x_2287_);
lean_closure_set(v___f_2290_, 3, v___x_2288_);
lean_closure_set(v___f_2290_, 4, v___x_2289_);
lean_closure_set(v___f_2290_, 5, v_a_2277_);
lean_closure_set(v___f_2290_, 6, v___x_2272_);
lean_closure_set(v___f_2290_, 7, v___x_2178_);
lean_closure_set(v___f_2290_, 8, v_expr_2212_);
lean_closure_set(v___f_2290_, 9, v___x_2271_);
lean_closure_set(v___f_2290_, 10, v_val_2269_);
lean_closure_set(v___f_2290_, 11, v_mvarId_2198_);
lean_closure_set(v___f_2290_, 12, v___x_2282_);
lean_closure_set(v___f_2290_, 13, v_a_2206_);
v___x_2291_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2282_, v___f_2290_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
v___y_2126_ = v___x_2291_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_a_2277_);
lean_dec_ref(v___x_2271_);
lean_dec(v_val_2269_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v___x_2119_);
v_a_2292_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2280_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2280_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec_ref(v___x_2275_);
lean_dec_ref(v___x_2271_);
lean_dec(v_val_2269_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v_localInsts_2256_);
lean_dec_ref(v___x_2219_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec(v_a_2203_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v___x_2119_);
v_a_2300_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2276_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2276_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v___x_2308_; 
lean_dec(v___x_2214_);
lean_inc_ref(v___x_2204_);
v___x_2308_ = l_Lean_Meta_getLevel(v___x_2204_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = 2;
v___x_2311_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_2204_);
v___x_2312_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2219_, v_localInsts_2256_, v___x_2204_, v___x_2310_, v_a_2203_, v___x_2311_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = l_Lean_Expr_mvarId_x21(v_a_2313_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_array_push(v___x_2316_, v___x_2207_);
v___x_2318_ = 1;
v___x_2319_ = lean_box(v___x_2196_);
v___x_2320_ = lean_box(v___x_2144_);
v___x_2321_ = lean_box(v___x_2318_);
lean_inc(v___x_2314_);
v___f_2322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2322_, 0, v___x_2317_);
lean_closure_set(v___f_2322_, 1, v_a_2313_);
lean_closure_set(v___f_2322_, 2, v___x_2319_);
lean_closure_set(v___f_2322_, 3, v___x_2320_);
lean_closure_set(v___f_2322_, 4, v___x_2321_);
lean_closure_set(v___f_2322_, 5, v_a_2309_);
lean_closure_set(v___f_2322_, 6, v___x_2178_);
lean_closure_set(v___f_2322_, 7, v_expr_2212_);
lean_closure_set(v___f_2322_, 8, v___x_2204_);
lean_closure_set(v___f_2322_, 9, v_val_2269_);
lean_closure_set(v___f_2322_, 10, v_mvarId_2198_);
lean_closure_set(v___f_2322_, 11, v___x_2314_);
lean_closure_set(v___f_2322_, 12, v_a_2206_);
v___x_2323_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2314_, v___f_2322_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
v___y_2126_ = v___x_2323_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2309_);
lean_dec(v_val_2269_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v___x_2204_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v___x_2119_);
v_a_2324_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2312_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2312_);
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
lean_dec(v_val_2269_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2257_);
lean_dec_ref(v_localInsts_2256_);
lean_dec_ref(v___x_2219_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2203_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v___x_2119_);
v_a_2332_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2308_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2308_);
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
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___x_2214_);
lean_dec(v_proof_x3f_2213_);
lean_dec_ref(v_expr_2212_);
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2203_);
lean_del_object(v___x_2200_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2355_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2215_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2215_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2203_);
lean_del_object(v___x_2200_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2363_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2208_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2208_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2203_);
lean_del_object(v___x_2200_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2371_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2205_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2205_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_del_object(v___x_2200_);
lean_dec(v_mvarId_2198_);
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2379_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2202_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2202_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2142_);
lean_del_object(v___x_2139_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
v_a_2389_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2179_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2179_);
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
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_del_object(v___x_2139_);
lean_dec(v___x_2119_);
lean_dec_ref(v___y_2114_);
lean_dec(v_generation_2108_);
lean_dec_ref(v_goal_2107_);
v_a_2397_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2141_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2141_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2407_, lean_object* v_generation_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2407_, v_generation_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2420_, lean_object* v_generation_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_mvarId_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v_mvarId_2432_ = lean_ctor_get(v_goal_2420_, 1);
lean_inc(v_mvarId_2432_);
v___f_2433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2433_, 0, v_goal_2420_);
lean_closure_set(v___f_2433_, 1, v_generation_2421_);
v___x_2434_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2432_, v___f_2433_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2443_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_fst_2439_; lean_object* v___x_2441_; 
v_fst_2439_ = lean_ctor_get(v_a_2435_, 0);
lean_inc(v_fst_2439_);
lean_dec(v_a_2435_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_fst_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_fst_2439_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2434_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2434_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2452_, lean_object* v_generation_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2452_, v_generation_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2465_, lean_object* v_val_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2465_, v_val_2466_, v___y_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2479_, lean_object* v_val_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2479_, v_val_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2502_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2518_, v_x_2519_, v_x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2522_, lean_object* v_x_2523_, size_t v_x_2524_, size_t v_x_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2523_, v_x_2524_, v_x_2525_, v_x_2526_, v_x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_){
_start:
{
size_t v_x_154075__boxed_2535_; size_t v_x_154076__boxed_2536_; lean_object* v_res_2537_; 
v_x_154075__boxed_2535_ = lean_unbox_usize(v_x_2531_);
lean_dec(v_x_2531_);
v_x_154076__boxed_2536_ = lean_unbox_usize(v_x_2532_);
lean_dec(v_x_2532_);
v_res_2537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2529_, v_x_2530_, v_x_154075__boxed_2535_, v_x_154076__boxed_2536_, v_x_2533_, v_x_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2538_, lean_object* v_n_2539_, lean_object* v_k_2540_, lean_object* v_v_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2539_, v_k_2540_, v_v_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2543_, size_t v_depth_2544_, lean_object* v_keys_2545_, lean_object* v_vals_2546_, lean_object* v_heq_2547_, lean_object* v_i_2548_, lean_object* v_entries_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2544_, v_keys_2545_, v_vals_2546_, v_i_2548_, v_entries_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2551_, lean_object* v_depth_2552_, lean_object* v_keys_2553_, lean_object* v_vals_2554_, lean_object* v_heq_2555_, lean_object* v_i_2556_, lean_object* v_entries_2557_){
_start:
{
size_t v_depth_boxed_2558_; lean_object* v_res_2559_; 
v_depth_boxed_2558_ = lean_unbox_usize(v_depth_2552_);
lean_dec(v_depth_2552_);
v_res_2559_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2551_, v_depth_boxed_2558_, v_keys_2553_, v_vals_2554_, v_heq_2555_, v_i_2556_, v_entries_2557_);
lean_dec_ref(v_vals_2554_);
lean_dec_ref(v_keys_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2560_, lean_object* v_x_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2561_, v_x_2562_, v_x_2563_, v_x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Expr_getAppFn(v_type_2566_);
if (lean_obj_tag(v___x_2569_) == 4)
{
lean_object* v_declName_2570_; lean_object* v___x_2571_; 
v_declName_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_declName_2570_);
lean_dec_ref_known(v___x_2569_, 2);
v___x_2571_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2570_, v_a_2567_);
lean_dec(v_declName_2570_);
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref(v___x_2569_);
v___x_2572_ = 0;
v___x_2573_ = lean_box(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2575_, v_a_2576_);
lean_dec_ref(v_a_2576_);
lean_dec_ref(v_type_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2579_, v_a_2581_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_type_2591_);
return v_res_2602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
lean_ctor_set(v___x_2609_, 3, v___x_2608_);
lean_ctor_set(v___x_2609_, 4, v___x_2607_);
lean_ctor_set(v___x_2609_, 5, v___x_2607_);
lean_ctor_set(v___x_2609_, 6, v___x_2607_);
lean_ctor_set(v___x_2609_, 7, v___x_2607_);
lean_ctor_set(v___x_2609_, 8, v___x_2607_);
lean_ctor_set(v___x_2609_, 9, v___x_2607_);
lean_ctor_set(v___x_2609_, 10, v___x_2607_);
lean_ctor_set(v___x_2609_, 11, v___x_2606_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_unsigned_to_nat(32u);
v___x_2611_ = lean_mk_empty_array_with_capacity(v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2613_ = ((size_t)5ULL);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_unsigned_to_nat(32u);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___x_2615_);
v___x_2617_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2618_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___x_2616_);
lean_ctor_set(v___x_2618_, 2, v___x_2614_);
lean_ctor_set(v___x_2618_, 3, v___x_2614_);
lean_ctor_set_usize(v___x_2618_, 4, v___x_2613_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2619_ = lean_box(1);
v___x_2620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2620_);
lean_ctor_set(v___x_2622_, 2, v___x_2619_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2637_ = l_Lean_stringToMessageData(v___x_2636_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2644_, lean_object* v_declHint_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_env_2650_; uint8_t v___x_2651_; 
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_st_ref_get(v___y_2646_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2651_ = l_Lean_Name_isAnonymous(v_declHint_2645_);
if (v___x_2651_ == 0)
{
uint8_t v_isExporting_2652_; 
v_isExporting_2652_ = lean_ctor_get_uint8(v_env_2650_, sizeof(void*)*13);
if (v_isExporting_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2645_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_msg_2644_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
lean_inc_ref(v_env_2650_);
v___x_2654_ = l_Lean_Environment_setExporting(v_env_2650_, v___x_2651_);
lean_inc(v_declHint_2645_);
lean_inc_ref(v___x_2654_);
v___x_2655_ = l_Lean_Environment_contains(v___x_2654_, v_declHint_2645_, v_isExporting_2652_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2645_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_msg_2644_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v_c_2662_; lean_object* v___x_2663_; 
v___x_2657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2659_ = l_Lean_Options_empty;
v___x_2660_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2654_);
lean_ctor_set(v___x_2660_, 1, v___x_2657_);
lean_ctor_set(v___x_2660_, 2, v___x_2658_);
lean_ctor_set(v___x_2660_, 3, v___x_2659_);
lean_inc(v_declHint_2645_);
v___x_2661_ = l_Lean_MessageData_ofConstName(v_declHint_2645_, v___x_2651_);
v_c_2662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2662_, 0, v___x_2660_);
lean_ctor_set(v_c_2662_, 1, v___x_2661_);
v___x_2663_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2650_, v_declHint_2645_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2645_);
v___x_2664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v_c_2662_);
v___x_2666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = l_Lean_MessageData_note(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_msg_2644_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
else
{
lean_object* v_val_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2705_; 
v_val_2671_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2673_ = v___x_2663_;
v_isShared_2674_ = v_isSharedCheck_2705_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_val_2671_);
lean_dec(v___x_2663_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2705_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v_moduleNames_2676_; lean_object* v_mod_2677_; uint8_t v___x_2678_; 
v___x_2675_ = l_Lean_Environment_header(v_env_2650_);
lean_dec_ref(v_env_2650_);
v_moduleNames_2676_ = lean_ctor_get(v___x_2675_, 4);
lean_inc_ref(v_moduleNames_2676_);
lean_dec_ref(v___x_2675_);
v_mod_2677_ = lean_array_get(v___x_2648_, v_moduleNames_2676_, v_val_2671_);
lean_dec(v_val_2671_);
lean_dec_ref(v_moduleNames_2676_);
v___x_2678_ = l_Lean_isPrivateName(v_declHint_2645_);
lean_dec(v_declHint_2645_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v_c_2662_);
v___x_2681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_MessageData_ofName(v_mod_2677_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_note(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_msg_2644_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2688_);
v___x_2690_ = v___x_2673_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
lean_ctor_set(v___x_2693_, 1, v_c_2662_);
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_MessageData_ofName(v_mod_2677_);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = l_Lean_MessageData_note(v___x_2699_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_msg_2644_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2701_);
v___x_2703_ = v___x_2673_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2706_; 
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2645_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v_msg_2644_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2707_, lean_object* v_declHint_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2707_, v_declHint_2708_, v___y_2709_);
lean_dec(v___y_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2712_, lean_object* v_declHint_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2727_; 
v___x_2717_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2712_, v_declHint_2713_, v___y_2715_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = l_Lean_unknownIdentifierMessageTag;
v___x_2723_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_a_2718_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2723_);
v___x_2725_ = v___x_2720_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2728_, lean_object* v_declHint_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2728_, v_declHint_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v_toCold_2739_; lean_object* v_env_2740_; lean_object* v_options_2741_; uint8_t v___x_2742_; lean_object* v_env_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2738_ = lean_st_ref_get(v___y_2736_);
v_toCold_2739_ = lean_ctor_get(v___y_2735_, 0);
v_env_2740_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_ref(v_env_2740_);
lean_dec(v___x_2738_);
v_options_2741_ = lean_ctor_get(v_toCold_2739_, 2);
v___x_2742_ = 0;
v_env_2743_ = l_Lean_Environment_setRecordingDeps(v_env_2740_, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2745_ = lean_unsigned_to_nat(32u);
v___x_2746_ = lean_mk_empty_array_with_capacity(v___x_2745_);
lean_dec_ref(v___x_2746_);
v___x_2747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2741_);
v___x_2748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2748_, 0, v_env_2743_);
lean_ctor_set(v___x_2748_, 1, v___x_2744_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
lean_ctor_set(v___x_2748_, 3, v_options_2741_);
v___x_2749_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_msgData_2734_);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_ref_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v_ref_2760_ = lean_ctor_get(v___y_2757_, 2);
v___x_2761_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2756_, v___y_2757_, v___y_2758_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_inc(v_ref_2760_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_ref_2760_);
lean_ctor_set(v___x_2766_, 1, v_a_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 1);
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2776_, lean_object* v_msg_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_toCold_2781_; lean_object* v_currRecDepth_2782_; lean_object* v_ref_2783_; uint16_t v_optionFlags_2784_; uint8_t v_suppressElabErrors_2785_; uint8_t v_isRecordingDeps_2786_; lean_object* v_ref_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_toCold_2781_ = lean_ctor_get(v___y_2778_, 0);
v_currRecDepth_2782_ = lean_ctor_get(v___y_2778_, 1);
v_ref_2783_ = lean_ctor_get(v___y_2778_, 2);
v_optionFlags_2784_ = lean_ctor_get_uint16(v___y_2778_, sizeof(void*)*3);
v_suppressElabErrors_2785_ = lean_ctor_get_uint8(v___y_2778_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2786_ = lean_ctor_get_uint8(v___y_2778_, sizeof(void*)*3 + 3);
v_ref_2787_ = l_Lean_replaceRef(v_ref_2776_, v_ref_2783_);
lean_inc(v_currRecDepth_2782_);
lean_inc_ref(v_toCold_2781_);
v___x_2788_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2788_, 0, v_toCold_2781_);
lean_ctor_set(v___x_2788_, 1, v_currRecDepth_2782_);
lean_ctor_set(v___x_2788_, 2, v_ref_2787_);
lean_ctor_set_uint16(v___x_2788_, sizeof(void*)*3, v_optionFlags_2784_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*3 + 2, v_suppressElabErrors_2785_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*3 + 3, v_isRecordingDeps_2786_);
v___x_2789_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2777_, v___x_2788_, v___y_2779_);
lean_dec_ref_known(v___x_2788_, 3);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2790_, v_msg_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v_ref_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2796_, lean_object* v_msg_2797_, lean_object* v_declHint_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v_a_2803_; lean_object* v___x_2804_; 
v___x_2802_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2797_, v_declHint_2798_, v___y_2799_, v___y_2800_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2802_);
v___x_2804_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2796_, v_a_2803_, v___y_2799_, v___y_2800_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2805_, lean_object* v_msg_2806_, lean_object* v_declHint_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2805_, v_msg_2806_, v_declHint_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v_ref_2805_);
return v_res_2811_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2817_ = l_Lean_stringToMessageData(v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2818_, lean_object* v_constName_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2823_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2824_ = 0;
lean_inc(v_constName_2819_);
v___x_2825_ = l_Lean_MessageData_ofConstName(v_constName_2819_, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2823_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2818_, v___x_2828_, v_constName_2819_, v___y_2820_, v___y_2821_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2830_, lean_object* v_constName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2830_, v_constName_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v_ref_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_ref_2840_; lean_object* v___x_2841_; 
v_ref_2840_ = lean_ctor_get(v___y_2837_, 2);
v___x_2841_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2840_, v_constName_2836_, v___y_2837_, v___y_2838_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v_env_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2851_ = lean_st_ref_get(v___y_2849_);
v_env_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc_ref(v_env_2852_);
lean_dec(v___x_2851_);
v___x_2853_ = 0;
lean_inc(v_constName_2847_);
v___x_2854_ = l_Lean_Environment_find_x3f(v_env_2852_, v_constName_2847_, v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2847_, v___y_2848_, v___y_2849_);
return v___x_2855_;
}
else
{
lean_object* v_val_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_constName_2847_);
v_val_2856_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2854_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_val_2856_);
lean_dec(v___x_2854_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 0);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_val_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Expr_getAppFn(v_type_2869_);
if (lean_obj_tag(v___x_2873_) == 4)
{
lean_object* v_declName_2874_; lean_object* v___x_2875_; 
v_declName_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_declName_2874_);
lean_dec_ref_known(v___x_2873_, 2);
v___x_2875_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2874_, v_a_2870_, v_a_2871_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2893_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2893_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2893_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_a_2876_) == 5)
{
lean_object* v_val_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v_val_2880_ = lean_ctor_get(v_a_2876_, 0);
lean_inc_ref(v_val_2880_);
lean_dec_ref_known(v_a_2876_, 1);
v___x_2881_ = l_Lean_InductiveVal_numCtors(v_val_2880_);
lean_dec_ref(v_val_2880_);
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_dec_le(v___x_2881_, v___x_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(v___x_2883_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
lean_dec(v_a_2876_);
v___x_2888_ = 0;
v___x_2889_ = lean_box(v___x_2888_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2889_);
v___x_2891_ = v___x_2878_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2875_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2875_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec_ref(v___x_2873_);
v___x_2902_ = 0;
v___x_2903_ = lean_box(v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_type_2905_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2910_, lean_object* v_constName_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2911_, v___y_2912_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_constName_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2916_, v_constName_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2922_, lean_object* v_ref_2923_, lean_object* v_constName_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2923_, v_constName_2924_, v___y_2925_, v___y_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2929_, lean_object* v_ref_2930_, lean_object* v_constName_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2929_, v_ref_2930_, v_constName_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_ref_2930_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2936_, lean_object* v_ref_2937_, lean_object* v_msg_2938_, lean_object* v_declHint_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2937_, v_msg_2938_, v_declHint_2939_, v___y_2940_, v___y_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_ref_2945_, lean_object* v_msg_2946_, lean_object* v_declHint_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2944_, v_ref_2945_, v_msg_2946_, v_declHint_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v_ref_2945_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2952_, lean_object* v_declHint_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2952_, v_declHint_2953_, v___y_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2958_, lean_object* v_declHint_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2958_, v_declHint_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2964_, lean_object* v_ref_2965_, lean_object* v_msg_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2965_, v_msg_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_ref_2972_, lean_object* v_msg_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2971_, v_ref_2972_, v_msg_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v_ref_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2978_, lean_object* v_msg_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2979_, v___y_2980_, v___y_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2984_, lean_object* v_msg_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2984_, v_msg_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_2990_, lean_object* v_fvarId_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_toGoalState_2997_; lean_object* v_mvarId_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3034_; 
v_toGoalState_2997_ = lean_ctor_get(v_goal_2990_, 0);
v_mvarId_2998_ = lean_ctor_get(v_goal_2990_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_goal_2990_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3000_ = v_goal_2990_;
v_isShared_3001_ = v_isSharedCheck_3034_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_mvarId_2998_);
lean_inc(v_toGoalState_2997_);
lean_dec(v_goal_2990_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3034_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_2998_, v_fvarId_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3025_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3025_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3025_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
if (lean_obj_tag(v_a_3003_) == 1)
{
lean_object* v_val_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3020_; 
v_val_3007_ = lean_ctor_get(v_a_3003_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_a_3003_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3009_ = v_a_3003_;
v_isShared_3010_ = v_isSharedCheck_3020_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_val_3007_);
lean_dec(v_a_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3020_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v_val_3007_);
v___x_3012_ = v___x_3000_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_toGoalState_2997_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_val_3007_);
v___x_3012_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3016_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3014_);
v___x_3016_ = v___x_3005_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
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
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec(v_a_3003_);
lean_del_object(v___x_3000_);
lean_dec_ref(v_toGoalState_2997_);
v___x_3021_ = lean_box(0);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3021_);
v___x_3023_ = v___x_3005_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_3000_);
lean_dec_ref(v_toGoalState_2997_);
v_a_3026_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3002_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3002_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3035_, lean_object* v_fvarId_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3035_, v_fvarId_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3043_, lean_object* v_x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3043_, v_x_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3050_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3050_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3067_, lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3067_, v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3075_, lean_object* v_mvarId_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3076_, v_x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3084_, lean_object* v_mvarId_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3084_, v_mvarId_3085_, v_x_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3093_, lean_object* v_toGoalState_3094_, lean_object* v_goal_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; 
lean_inc(v_mvarId_3093_);
v___x_3101_ = l_Lean_MVarId_getType(v_mvarId_3093_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_Meta_isProp(v_a_3102_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3130_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3130_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3130_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_goal_3095_);
v___x_3109_ = l_Lean_MVarId_exfalso(v_mvarId_3093_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_toGoalState_3094_);
lean_ctor_set(v___x_3114_, 1, v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_toGoalState_3094_);
v_a_3119_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3109_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3109_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v___x_3128_; 
lean_dec_ref(v_toGoalState_3094_);
lean_dec(v_mvarId_3093_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_goal_3095_);
v___x_3128_ = v___x_3106_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_goal_3095_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_goal_3095_);
lean_dec_ref(v_toGoalState_3094_);
lean_dec(v_mvarId_3093_);
v_a_3131_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3103_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3103_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v_goal_3095_);
lean_dec_ref(v_toGoalState_3094_);
lean_dec(v_mvarId_3093_);
v_a_3139_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3101_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3101_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3147_, lean_object* v_toGoalState_3148_, lean_object* v_goal_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3147_, v_toGoalState_3148_, v_goal_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_toGoalState_3162_; lean_object* v_mvarId_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; 
v_toGoalState_3162_ = lean_ctor_get(v_goal_3156_, 0);
lean_inc_ref(v_toGoalState_3162_);
v_mvarId_3163_ = lean_ctor_get(v_goal_3156_, 1);
lean_inc_n(v_mvarId_3163_, 2);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3164_, 0, v_mvarId_3163_);
lean_closure_set(v___f_3164_, 1, v_toGoalState_3162_);
lean_closure_set(v___f_3164_, 2, v_goal_3156_);
v___x_3165_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3163_, v___f_3164_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object* v_toGoalState_3173_, lean_object* v_mvarId_3174_, lean_object* v_goal_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_mvarId_3187_; lean_object* v___x_3190_; 
lean_inc(v_mvarId_3174_);
v___x_3190_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_n(v_a_3191_, 2);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l_Lean_Meta_Grind_simpCore(v_a_3191_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3224_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3224_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3224_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_expr_3197_; lean_object* v_proof_x3f_3198_; uint8_t v___x_3199_; 
v_expr_3197_ = lean_ctor_get(v_a_3193_, 0);
lean_inc_ref(v_expr_3197_);
v_proof_x3f_3198_ = lean_ctor_get(v_a_3193_, 1);
lean_inc(v_proof_x3f_3198_);
lean_dec(v_a_3193_);
v___x_3199_ = lean_expr_eqv(v_expr_3197_, v_a_3191_);
lean_dec(v_a_3191_);
if (v___x_3199_ == 0)
{
lean_del_object(v___x_3195_);
lean_dec_ref(v_goal_3175_);
if (lean_obj_tag(v_proof_x3f_3198_) == 0)
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_3174_, v_expr_3197_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v_mvarId_3187_ = v_a_3201_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_toGoalState_3173_);
v_a_3202_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3200_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3200_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_val_3210_; lean_object* v___x_3211_; 
v_val_3210_ = lean_ctor_get(v_proof_x3f_3198_, 0);
lean_inc(v_val_3210_);
lean_dec_ref_known(v_proof_x3f_3198_, 1);
v___x_3211_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_3174_, v_expr_3197_, v_val_3210_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v_mvarId_3187_ = v_a_3212_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v_toGoalState_3173_);
v_a_3213_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3211_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3211_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v___x_3222_; 
lean_dec(v_proof_x3f_3198_);
lean_dec_ref(v_expr_3197_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_toGoalState_3173_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_goal_3175_);
v___x_3222_ = v___x_3195_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_goal_3175_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v_a_3191_);
lean_dec_ref(v_goal_3175_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_toGoalState_3173_);
v_a_3225_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3192_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3192_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v_goal_3175_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_toGoalState_3173_);
v_a_3233_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3190_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3190_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
v___jp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_toGoalState_3173_);
lean_ctor_set(v___x_3188_, 1, v_mvarId_3187_);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object* v_toGoalState_3241_, lean_object* v_mvarId_3242_, lean_object* v_goal_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3241_, v_mvarId_3242_, v_goal_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object* v_goal_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_toGoalState_3266_; lean_object* v_mvarId_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
v_toGoalState_3266_ = lean_ctor_get(v_goal_3255_, 0);
lean_inc_ref(v_toGoalState_3266_);
v_mvarId_3267_ = lean_ctor_get(v_goal_3255_, 1);
lean_inc_n(v_mvarId_3267_, 2);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3268_, 0, v_toGoalState_3266_);
lean_closure_set(v___f_3268_, 1, v_mvarId_3267_);
lean_closure_set(v___f_3268_, 2, v_goal_3255_);
v___x_3269_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3267_, v___f_3268_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object* v_goal_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_mvarId_3288_; lean_object* v___x_3289_; 
v_mvarId_3288_ = lean_ctor_get(v_goal_3282_, 1);
lean_inc(v_mvarId_3288_);
lean_dec_ref(v_goal_3282_);
v___x_3289_ = l_Lean_MVarId_getDecl(v_mvarId_3288_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3299_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3299_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3299_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_lctx_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v_lctx_3294_ = lean_ctor_get(v_a_3290_, 1);
lean_inc_ref(v_lctx_3294_);
lean_dec(v_a_3290_);
v___x_3295_ = l_Lean_LocalContext_lastDecl(v_lctx_3294_);
lean_dec_ref(v_lctx_3294_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3295_);
v___x_3297_ = v___x_3292_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_a_3300_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3289_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3289_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_goal_3315_, lean_object* v_fvarId_3316_, lean_object* v_generation_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_st_mk_ref(v_goal_3315_);
lean_inc(v_fvarId_3316_);
v___x_3329_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3316_, v_generation_3317_, v___x_3328_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref_known(v___x_3329_, 1);
v___x_3330_ = l_Lean_FVarId_getType___redArg(v_fvarId_3316_, v___y_3323_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_a_3331_, v___x_3328_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v___x_3332_, 0);
lean_dec(v_unused_3342_);
v___x_3334_ = v___x_3332_;
v_isShared_3335_ = v_isSharedCheck_3341_;
goto v_resetjp_3333_;
}
else
{
lean_dec(v___x_3332_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3341_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3336_ = lean_st_ref_get(v___x_3328_);
v___x_3337_ = lean_st_ref_get(v___x_3328_);
lean_dec(v___x_3328_);
lean_dec(v___x_3337_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3336_);
v___x_3339_ = v___x_3334_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3336_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v___x_3328_);
v_a_3343_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3332_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3332_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v___x_3328_);
v_a_3351_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3330_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3330_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v___x_3328_);
lean_dec(v_fvarId_3316_);
v_a_3359_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3329_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3329_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_goal_3367_, lean_object* v_fvarId_3368_, lean_object* v_generation_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_goal_3367_, v_fvarId_3368_, v_generation_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v___x_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
if (lean_obj_tag(v_a_3382_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v___x_3381_);
v___x_3384_ = l_List_reverse___redArg(v_a_3383_);
return v___x_3384_;
}
else
{
lean_object* v_head_3385_; lean_object* v_tail_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3395_; 
v_head_3385_ = lean_ctor_get(v_a_3382_, 0);
v_tail_3386_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3388_ = v_a_3382_;
v_isShared_3389_ = v_isSharedCheck_3395_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_tail_3386_);
lean_inc(v_head_3385_);
lean_dec(v_a_3382_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3395_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
lean_inc_ref(v___x_3381_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3381_);
lean_ctor_set(v___x_3390_, 1, v_head_3385_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 1, v_a_3383_);
lean_ctor_set(v___x_3388_, 0, v___x_3390_);
v___x_3392_ = v___x_3388_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_a_3383_);
v___x_3392_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v_a_3382_ = v_tail_3386_;
v_a_3383_ = v___x_3392_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3396_, lean_object* v_as_x27_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
if (lean_obj_tag(v_as_x27_3397_) == 0)
{
lean_object* v___x_3409_; 
lean_dec_ref(v_kp_3396_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_b_3398_);
return v___x_3409_;
}
else
{
lean_object* v_head_3410_; lean_object* v_tail_3411_; lean_object* v_fst_3412_; lean_object* v_snd_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3439_; 
v_head_3410_ = lean_ctor_get(v_as_x27_3397_, 0);
v_tail_3411_ = lean_ctor_get(v_as_x27_3397_, 1);
v_fst_3412_ = lean_ctor_get(v_b_3398_, 0);
v_snd_3413_ = lean_ctor_get(v_b_3398_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_b_3398_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3415_ = v_b_3398_;
v_isShared_3416_ = v_isSharedCheck_3439_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_snd_3413_);
lean_inc(v_fst_3412_);
lean_dec(v_b_3398_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3439_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; 
lean_inc_ref(v_kp_3396_);
lean_inc(v___y_3407_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3405_);
lean_inc_ref(v___y_3404_);
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3402_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc(v_head_3410_);
v___x_3417_ = lean_apply_11(v_kp_3396_, v_head_3410_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, lean_box(0));
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
if (lean_obj_tag(v_a_3418_) == 0)
{
lean_object* v_seq_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v_seq_3419_ = lean_ctor_get(v_a_3418_, 0);
lean_inc(v_seq_3419_);
lean_dec_ref_known(v_a_3418_, 1);
v___x_3420_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3412_, v_seq_3419_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3420_);
v___x_3422_ = v___x_3415_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_snd_3413_);
v___x_3422_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v_as_x27_3397_ = v_tail_3411_;
v_b_3398_ = v___x_3422_;
goto _start;
}
}
else
{
lean_object* v_gs_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v_gs_3425_ = lean_ctor_get(v_a_3418_, 0);
lean_inc(v_gs_3425_);
lean_dec_ref_known(v_a_3418_, 1);
v___x_3426_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3413_, v_gs_3425_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3426_);
v___x_3428_ = v___x_3415_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_fst_3412_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
v_as_x27_3397_ = v_tail_3411_;
v_b_3398_ = v___x_3428_;
goto _start;
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_del_object(v___x_3415_);
lean_dec(v_snd_3413_);
lean_dec(v_fst_3412_);
lean_dec_ref(v_kp_3396_);
v_a_3431_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3417_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3417_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3440_, lean_object* v_as_x27_3441_, lean_object* v_b_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3440_, v_as_x27_3441_, v_b_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v_as_x27_3441_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(lean_object* v_fvarId_3458_, lean_object* v_kp_3459_, lean_object* v_goal_3460_, lean_object* v_toGoalState_3461_, lean_object* v_mvarId_3462_, lean_object* v___f_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_goal_3475_; lean_object* v_toGoalState_3476_; lean_object* v_mvarId_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___x_3551_; 
lean_inc(v_fvarId_3458_);
v___x_3551_ = l_Lean_FVarId_getType___redArg(v_fvarId_3458_, v___y_3469_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
lean_inc(v___y_3472_);
lean_inc_ref(v___y_3471_);
lean_inc(v___y_3470_);
lean_inc_ref(v___y_3469_);
v___x_3553_ = lean_whnf(v_a_3552_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3656_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3656_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3656_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___x_3607_; 
v___x_3607_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3554_, v___y_3465_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3647_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
uint8_t v___x_3612_; 
v___x_3612_ = lean_unbox(v_a_3608_);
lean_dec(v_a_3608_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
lean_del_object(v___x_3556_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v___x_3613_ = lean_box(0);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3613_);
v___x_3615_ = v___x_3610_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
else
{
lean_object* v___x_3617_; 
lean_del_object(v___x_3610_);
v___x_3617_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3465_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; uint8_t v___x_3619_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = lean_unbox(v_a_3618_);
lean_dec(v_a_3618_);
if (v___x_3619_ == 0)
{
v___y_3559_ = v___y_3464_;
v___y_3560_ = v___y_3465_;
v___y_3561_ = v___y_3466_;
v___y_3562_ = v___y_3467_;
v___y_3563_ = v___y_3468_;
v___y_3564_ = v___y_3469_;
v___y_3565_ = v___y_3470_;
v___y_3566_ = v___y_3471_;
v___y_3567_ = v___y_3472_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3554_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3630_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3630_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3630_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_unbox(v_a_3621_);
lean_dec(v_a_3621_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
lean_del_object(v___x_3556_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v___x_3626_ = lean_box(0);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3626_);
v___x_3628_ = v___x_3623_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
else
{
lean_del_object(v___x_3623_);
v___y_3559_ = v___y_3464_;
v___y_3560_ = v___y_3465_;
v___y_3561_ = v___y_3466_;
v___y_3562_ = v___y_3467_;
v___y_3563_ = v___y_3468_;
v___y_3564_ = v___y_3469_;
v___y_3565_ = v___y_3470_;
v___y_3566_ = v___y_3471_;
v___y_3567_ = v___y_3472_;
goto v___jp_3558_;
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_del_object(v___x_3556_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3631_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3620_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3620_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_del_object(v___x_3556_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3639_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3617_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3617_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_del_object(v___x_3556_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3648_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3607_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3607_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
v___jp_3558_:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_Expr_getAppFn(v_a_3554_);
if (lean_obj_tag(v___x_3568_) == 4)
{
lean_object* v_declName_3569_; lean_object* v___x_3570_; 
lean_del_object(v___x_3556_);
v_declName_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc_n(v_declName_3569_, 2);
lean_dec_ref_known(v___x_3568_, 2);
v___x_3570_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3569_, v___y_3561_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v___x_3571_; 
lean_dec_ref_known(v___x_3570_, 1);
v___x_3571_ = l_Lean_Meta_isProp(v_a_3554_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; uint8_t v___x_3573_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v___x_3573_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_3569_);
lean_dec(v_declName_3569_);
if (v___x_3573_ == 0)
{
uint8_t v___x_3574_; 
v___x_3574_ = lean_unbox(v_a_3572_);
lean_dec(v_a_3572_);
if (v___x_3574_ == 0)
{
lean_dec_ref(v___f_3463_);
v_goal_3475_ = v_goal_3460_;
v_toGoalState_3476_ = v_toGoalState_3461_;
v_mvarId_3477_ = v_mvarId_3462_;
v___y_3478_ = v___y_3559_;
v___y_3479_ = v___y_3560_;
v___y_3480_ = v___y_3561_;
v___y_3481_ = v___y_3562_;
v___y_3482_ = v___y_3563_;
v___y_3483_ = v___y_3564_;
v___y_3484_ = v___y_3565_;
v___y_3485_ = v___y_3566_;
v___y_3486_ = v___y_3567_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3575_; 
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
v___x_3575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3462_, v___f_3463_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v_toGoalState_3577_; lean_object* v_mvarId_3578_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v_toGoalState_3577_ = lean_ctor_get(v_a_3576_, 0);
lean_inc_ref(v_toGoalState_3577_);
v_mvarId_3578_ = lean_ctor_get(v_a_3576_, 1);
lean_inc(v_mvarId_3578_);
v_goal_3475_ = v_a_3576_;
v_toGoalState_3476_ = v_toGoalState_3577_;
v_mvarId_3477_ = v_mvarId_3578_;
v___y_3478_ = v___y_3559_;
v___y_3479_ = v___y_3560_;
v___y_3480_ = v___y_3561_;
v___y_3481_ = v___y_3562_;
v___y_3482_ = v___y_3563_;
v___y_3483_ = v___y_3564_;
v___y_3484_ = v___y_3565_;
v___y_3485_ = v___y_3566_;
v___y_3486_ = v___y_3567_;
goto v___jp_3474_;
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3579_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3575_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3575_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
else
{
lean_dec(v_a_3572_);
lean_dec_ref(v___f_3463_);
v_goal_3475_ = v_goal_3460_;
v_toGoalState_3476_ = v_toGoalState_3461_;
v_mvarId_3477_ = v_mvarId_3462_;
v___y_3478_ = v___y_3559_;
v___y_3479_ = v___y_3560_;
v___y_3480_ = v___y_3561_;
v___y_3481_ = v___y_3562_;
v___y_3482_ = v___y_3563_;
v___y_3483_ = v___y_3564_;
v___y_3484_ = v___y_3565_;
v___y_3485_ = v___y_3566_;
v___y_3486_ = v___y_3567_;
goto v___jp_3474_;
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v_declName_3569_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3587_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3571_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3571_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_declName_3569_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3595_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3570_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3570_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec_ref(v___x_3568_);
lean_dec(v_a_3554_);
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v___x_3603_ = lean_box(0);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3603_);
v___x_3605_ = v___x_3556_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3657_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3553_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3553_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec_ref(v___f_3463_);
lean_dec(v_mvarId_3462_);
lean_dec_ref(v_toGoalState_3461_);
lean_dec_ref(v_goal_3460_);
lean_dec_ref(v_kp_3459_);
lean_dec(v_fvarId_3458_);
v_a_3665_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3551_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3551_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
v___jp_3474_:
{
uint8_t v_inconsistent_3487_; 
v_inconsistent_3487_ = lean_ctor_get_uint8(v_toGoalState_3476_, sizeof(void*)*18);
if (v_inconsistent_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec_ref(v_goal_3475_);
v___x_3488_ = l_Lean_mkFVar(v_fvarId_3458_);
v___x_3489_ = l_Lean_Meta_Grind_cases(v_mvarId_3477_, v___x_3488_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = lean_box(0);
v___x_3492_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_toGoalState_3476_, v_a_3490_, v___x_3491_);
v___x_3493_ = lean_unsigned_to_nat(0u);
v___x_3494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1));
v___x_3495_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3459_, v___x_3492_, v___x_3494_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___x_3492_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3516_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3516_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3516_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v_fst_3500_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_fst_3500_);
v_snd_3501_ = lean_ctor_get(v_a_3496_, 1);
lean_inc(v_snd_3501_);
lean_dec(v_a_3496_);
v___x_3502_ = lean_array_get_size(v_snd_3501_);
v___x_3503_ = lean_nat_dec_eq(v___x_3502_, v___x_3493_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec(v_fst_3500_);
v___x_3504_ = lean_array_to_list(v_snd_3501_);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3506_);
v___x_3508_ = v___x_3498_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
lean_dec(v_snd_3501_);
v___x_3510_ = lean_array_to_list(v_fst_3500_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3512_);
v___x_3514_ = v___x_3498_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3495_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3495_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v_toGoalState_3476_);
lean_dec_ref(v_kp_3459_);
v_a_3525_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3489_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3489_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v___x_3533_; 
lean_dec(v_mvarId_3477_);
lean_dec_ref(v_toGoalState_3476_);
lean_dec(v_fvarId_3458_);
lean_inc(v___y_3486_);
lean_inc_ref(v___y_3485_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3483_);
lean_inc(v___y_3482_);
lean_inc_ref(v___y_3481_);
lean_inc(v___y_3480_);
lean_inc_ref(v___y_3479_);
lean_inc(v___y_3478_);
v___x_3533_ = lean_apply_11(v_kp_3459_, v_goal_3475_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, lean_box(0));
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3542_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_a_3534_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3538_);
v___x_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3533_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3533_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed(lean_object* v_fvarId_3673_, lean_object* v_kp_3674_, lean_object* v_goal_3675_, lean_object* v_toGoalState_3676_, lean_object* v_mvarId_3677_, lean_object* v___f_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(v_fvarId_3673_, v_kp_3674_, v_goal_3675_, v_toGoalState_3676_, v_mvarId_3677_, v___f_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3690_, lean_object* v_fvarId_3691_, lean_object* v_generation_3692_, lean_object* v_kp_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_toGoalState_3704_; lean_object* v_mvarId_3705_; lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; 
v_toGoalState_3704_ = lean_ctor_get(v_goal_3690_, 0);
lean_inc_ref(v_toGoalState_3704_);
v_mvarId_3705_ = lean_ctor_get(v_goal_3690_, 1);
lean_inc_n(v_mvarId_3705_, 2);
lean_inc(v_fvarId_3691_);
lean_inc_ref(v_goal_3690_);
v___f_3706_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3706_, 0, v_goal_3690_);
lean_closure_set(v___f_3706_, 1, v_fvarId_3691_);
lean_closure_set(v___f_3706_, 2, v_generation_3692_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed), 16, 6);
lean_closure_set(v___f_3707_, 0, v_fvarId_3691_);
lean_closure_set(v___f_3707_, 1, v_kp_3693_);
lean_closure_set(v___f_3707_, 2, v_goal_3690_);
lean_closure_set(v___f_3707_, 3, v_toGoalState_3704_);
lean_closure_set(v___f_3707_, 4, v_mvarId_3705_);
lean_closure_set(v___f_3707_, 5, v___f_3706_);
v___x_3708_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3705_, v___f_3707_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3709_, lean_object* v_fvarId_3710_, lean_object* v_generation_3711_, lean_object* v_kp_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3709_, v_fvarId_3710_, v_generation_3711_, v_kp_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
lean_dec(v_a_3721_);
lean_dec_ref(v_a_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_a_3717_);
lean_dec_ref(v_a_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_a_3714_);
lean_dec(v_a_3713_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3724_, lean_object* v_as_3725_, lean_object* v_as_x27_3726_, lean_object* v_b_3727_, lean_object* v_a_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3724_, v_as_x27_3726_, v_b_3727_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3740_, lean_object* v_as_3741_, lean_object* v_as_x27_3742_, lean_object* v_b_3743_, lean_object* v_a_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3740_, v_as_3741_, v_as_x27_3742_, v_b_3743_, v_a_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec(v_as_x27_3742_);
lean_dec(v_as_3741_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3756_, lean_object* v_fvarId_3757_, lean_object* v_generation_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_st_mk_ref(v_goal_3756_);
v___x_3770_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3757_, v_generation_3758_, v___x_3769_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3779_; 
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v___x_3770_, 0);
lean_dec(v_unused_3780_);
v___x_3772_ = v___x_3770_;
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
else
{
lean_dec(v___x_3770_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3774_ = lean_st_ref_get(v___x_3769_);
v___x_3775_ = lean_st_ref_get(v___x_3769_);
lean_dec(v___x_3769_);
lean_dec(v___x_3775_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3777_ = v___x_3772_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3774_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v___x_3769_);
v_a_3781_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3770_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3770_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3789_, lean_object* v_fvarId_3790_, lean_object* v_generation_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3789_, v_fvarId_3790_, v_generation_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3805_, lean_object* v_goal_3806_, lean_object* v_kna_3807_, lean_object* v_kp_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v_toGoalState_3819_; uint8_t v_inconsistent_3820_; 
v_toGoalState_3819_ = lean_ctor_get(v_goal_3806_, 0);
v_inconsistent_3820_ = lean_ctor_get_uint8(v_toGoalState_3819_, sizeof(void*)*18);
if (v_inconsistent_3820_ == 0)
{
lean_object* v_mvarId_3821_; lean_object* v___x_3822_; 
v_mvarId_3821_ = lean_ctor_get(v_goal_3806_, 1);
lean_inc(v_mvarId_3821_);
v___x_3822_ = l_Lean_MVarId_getType(v_mvarId_3821_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; uint8_t v___x_3824_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3822_, 1);
v___x_3824_ = l_Lean_Expr_isFalse(v_a_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref(v_kna_3807_);
lean_inc(v_generation_3805_);
v___x_3825_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3806_, v_generation_3805_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
switch(lean_obj_tag(v_a_3826_))
{
case 0:
{
lean_object* v_goal_3827_; lean_object* v___x_3828_; 
lean_dec(v_generation_3805_);
v_goal_3827_ = lean_ctor_get(v_a_3826_, 0);
lean_inc_ref(v_goal_3827_);
lean_dec_ref_known(v_a_3826_, 1);
v___x_3828_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3827_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
v___x_3830_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_a_3829_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v_toGoalState_3832_; lean_object* v_mvarId_3833_; lean_object* v___x_3834_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v_toGoalState_3832_ = lean_ctor_get(v_a_3831_, 0);
v_mvarId_3833_ = lean_ctor_get(v_a_3831_, 1);
lean_inc(v_mvarId_3833_);
v___x_3834_ = l_Lean_MVarId_getType(v_mvarId_3833_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; uint8_t v___x_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v___x_3836_ = l_Lean_Expr_isForall(v_a_3835_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
v___x_3837_ = l_Lean_Expr_isLet(v_a_3835_);
lean_dec(v_a_3835_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
lean_inc(v_mvarId_3833_);
v___x_3838_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3833_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
if (lean_obj_tag(v_a_3839_) == 1)
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3848_; 
lean_inc_ref(v_toGoalState_3832_);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_a_3831_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3849_ = lean_ctor_get(v_a_3831_, 1);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_a_3831_, 0);
lean_dec(v_unused_3850_);
v___x_3841_ = v_a_3831_;
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_a_3831_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v_val_3843_; lean_object* v___x_3845_; 
v_val_3843_ = lean_ctor_get(v_a_3839_, 0);
lean_inc(v_val_3843_);
lean_dec_ref_known(v_a_3839_, 1);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v_val_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_toGoalState_3832_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_val_3843_);
v___x_3845_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3846_ = lean_apply_11(v_kp_3808_, v___x_3845_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3846_;
}
}
}
else
{
lean_object* v___x_3851_; 
lean_dec(v_a_3839_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3851_ = lean_apply_11(v_kp_3808_, v_a_3831_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3851_;
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_kp_3808_);
v_a_3852_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3838_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3838_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v___x_3860_; 
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3860_ = lean_apply_11(v_kp_3808_, v_a_3831_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3860_;
}
}
else
{
lean_object* v___x_3861_; 
lean_dec(v_a_3835_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3861_ = lean_apply_11(v_kp_3808_, v_a_3831_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3861_;
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_kp_3808_);
v_a_3862_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3834_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3834_);
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
lean_dec_ref(v_kp_3808_);
v_a_3870_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3830_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3830_);
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
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_kp_3808_);
v_a_3878_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3828_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3828_);
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
case 1:
{
lean_object* v_fvarId_3886_; lean_object* v_goal_3887_; lean_object* v___f_3888_; lean_object* v___x_3889_; 
v_fvarId_3886_ = lean_ctor_get(v_a_3826_, 0);
lean_inc_n(v_fvarId_3886_, 3);
v_goal_3887_ = lean_ctor_get(v_a_3826_, 1);
lean_inc_ref_n(v_goal_3887_, 3);
lean_dec_ref_known(v_a_3826_, 2);
lean_inc(v_generation_3805_);
v___f_3888_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3888_, 0, v_goal_3887_);
lean_closure_set(v___f_3888_, 1, v_fvarId_3886_);
lean_closure_set(v___f_3888_, 2, v_generation_3805_);
v___x_3889_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3887_, v_fvarId_3886_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
if (lean_obj_tag(v_a_3890_) == 1)
{
lean_object* v_val_3891_; lean_object* v___x_3892_; 
lean_dec_ref(v___f_3888_);
lean_dec_ref(v_goal_3887_);
lean_dec(v_fvarId_3886_);
lean_dec(v_generation_3805_);
v_val_3891_ = lean_ctor_get(v_a_3890_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v_a_3890_, 1);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3892_ = lean_apply_11(v_kp_3808_, v_val_3891_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3892_;
}
else
{
lean_object* v___x_3893_; 
lean_dec(v_a_3890_);
lean_inc_ref(v_kp_3808_);
lean_inc_ref(v_goal_3887_);
v___x_3893_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3887_, v_fvarId_3886_, v_generation_3805_, v_kp_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3914_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3914_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3914_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_a_3894_) == 1)
{
lean_object* v_val_3898_; lean_object* v___x_3900_; 
lean_dec_ref(v___f_3888_);
lean_dec_ref(v_goal_3887_);
lean_dec_ref(v_kp_3808_);
v_val_3898_ = lean_ctor_get(v_a_3894_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v_a_3894_, 1);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v_val_3898_);
v___x_3900_ = v___x_3896_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_val_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
else
{
lean_object* v_mvarId_3902_; lean_object* v___x_3903_; 
lean_del_object(v___x_3896_);
lean_dec(v_a_3894_);
v_mvarId_3902_ = lean_ctor_get(v_goal_3887_, 1);
lean_inc(v_mvarId_3902_);
lean_dec_ref(v_goal_3887_);
v___x_3903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3902_, v___f_3888_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3905_ = lean_apply_11(v_kp_3808_, v_a_3904_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3905_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v_kp_3808_);
v_a_3906_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3903_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3903_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___f_3888_);
lean_dec_ref(v_goal_3887_);
lean_dec_ref(v_kp_3808_);
v_a_3915_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3893_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3893_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v___f_3888_);
lean_dec_ref(v_goal_3887_);
lean_dec(v_fvarId_3886_);
lean_dec_ref(v_kp_3808_);
lean_dec(v_generation_3805_);
v_a_3923_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3889_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3889_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
case 2:
{
lean_object* v_goal_3931_; lean_object* v___x_3932_; 
lean_dec(v_generation_3805_);
v_goal_3931_ = lean_ctor_get(v_a_3826_, 0);
lean_inc_ref(v_goal_3931_);
lean_dec_ref_known(v_a_3826_, 1);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3932_ = lean_apply_11(v_kp_3808_, v_goal_3931_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3932_;
}
default: 
{
lean_object* v_fvarId_3933_; lean_object* v_goal_3934_; lean_object* v___x_3935_; 
v_fvarId_3933_ = lean_ctor_get(v_a_3826_, 0);
lean_inc(v_fvarId_3933_);
v_goal_3934_ = lean_ctor_get(v_a_3826_, 1);
lean_inc_ref_n(v_goal_3934_, 2);
lean_dec_ref_known(v_a_3826_, 2);
lean_inc_ref(v_kp_3808_);
v___x_3935_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3934_, v_fvarId_3933_, v_generation_3805_, v_kp_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3945_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3945_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3945_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
if (lean_obj_tag(v_a_3936_) == 1)
{
lean_object* v_val_3940_; lean_object* v___x_3942_; 
lean_dec_ref(v_goal_3934_);
lean_dec_ref(v_kp_3808_);
v_val_3940_ = lean_ctor_get(v_a_3936_, 0);
lean_inc(v_val_3940_);
lean_dec_ref_known(v_a_3936_, 1);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v_val_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_val_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
else
{
lean_object* v___x_3944_; 
lean_del_object(v___x_3938_);
lean_dec(v_a_3936_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3944_ = lean_apply_11(v_kp_3808_, v_goal_3934_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3944_;
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v_goal_3934_);
lean_dec_ref(v_kp_3808_);
v_a_3946_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3935_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3935_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v_kp_3808_);
lean_dec(v_generation_3805_);
v_a_3954_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3825_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3825_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v___x_3962_; 
lean_dec_ref(v_kp_3808_);
lean_dec(v_generation_3805_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc(v_a_3815_);
lean_inc_ref(v_a_3814_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_a_3810_);
lean_inc(v_a_3809_);
v___x_3962_ = lean_apply_11(v_kna_3807_, v_goal_3806_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, lean_box(0));
return v___x_3962_;
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_kp_3808_);
lean_dec_ref(v_kna_3807_);
lean_dec_ref(v_goal_3806_);
lean_dec(v_generation_3805_);
v_a_3963_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3822_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3822_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec_ref(v_kp_3808_);
lean_dec_ref(v_kna_3807_);
lean_dec_ref(v_goal_3806_);
lean_dec(v_generation_3805_);
v___x_3971_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3973_, lean_object* v_goal_3974_, lean_object* v_kna_3975_, lean_object* v_kp_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_Grind_Action_intro(v_generation_3973_, v_goal_3974_, v_kna_3975_, v_kp_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
return v_res_3987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_unsigned_to_nat(1000000u);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3989_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4004_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_4017_, lean_object* v___f_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = lean_unsigned_to_nat(1000000u);
v___x_4033_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_4033_, 0, v_generation_4017_);
v___x_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_4034_, 0, v___x_4032_);
lean_closure_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_Lean_Meta_Grind_Action_andThen(v___x_4034_, v___f_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_4036_, lean_object* v___f_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_4036_, v___f_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_4054_, lean_object* v_a_4055_, lean_object* v_kna_4056_, lean_object* v_kp_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___f_4068_; lean_object* v___f_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___f_4068_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_4069_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4069_, 0, v_generation_4054_);
lean_closure_set(v___f_4069_, 1, v___f_4068_);
v___x_4070_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_4071_ = l_Lean_Meta_Grind_Action_andThen(v___x_4070_, v___f_4069_, v_a_4055_, v_kna_4056_, v_kp_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_4072_, lean_object* v_a_4073_, lean_object* v_kna_4074_, lean_object* v_kp_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Meta_Grind_Action_intros(v_generation_4072_, v_a_4073_, v_kna_4074_, v_kp_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
return v_res_4086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_4096_ = l_Lean_mkConst(v___x_4095_, v___x_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_4097_, lean_object* v_prop_4098_, lean_object* v_proof_4099_, lean_object* v_generation_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_st_mk_ref(v_goal_4097_);
lean_inc(v___y_4109_);
lean_inc_ref(v___y_4108_);
lean_inc(v___y_4107_);
lean_inc_ref(v___y_4106_);
lean_inc(v___y_4105_);
lean_inc_ref(v___y_4104_);
lean_inc(v___y_4103_);
lean_inc_ref(v___y_4102_);
lean_inc(v___y_4101_);
lean_inc(v___x_4111_);
lean_inc_ref(v_prop_4098_);
v___x_4112_ = lean_grind_preprocess(v_prop_4098_, v___x_4111_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_expr_4114_; lean_object* v___x_4115_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v_expr_4114_ = lean_ctor_get(v_a_4113_, 0);
lean_inc_ref(v_expr_4114_);
v___x_4115_ = l_Lean_Meta_Simp_Result_getProof(v_a_4113_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v___x_4115_, 1);
v___x_4117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4114_);
v___x_4118_ = l_Lean_mkApp4(v___x_4117_, v_prop_4098_, v_expr_4114_, v_a_4116_, v_proof_4099_);
v___x_4119_ = l_Lean_Meta_Grind_add(v_expr_4114_, v___x_4118_, v_generation_4100_, v___x_4111_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4128_; 
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v___x_4119_, 0);
lean_dec(v_unused_4129_);
v___x_4121_ = v___x_4119_;
v_isShared_4122_ = v_isSharedCheck_4128_;
goto v_resetjp_4120_;
}
else
{
lean_dec(v___x_4119_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4128_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4123_ = lean_st_ref_get(v___x_4111_);
v___x_4124_ = lean_st_ref_get(v___x_4111_);
lean_dec(v___x_4111_);
lean_dec(v___x_4124_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4123_);
v___x_4126_ = v___x_4121_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4123_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v___x_4111_);
v_a_4130_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4119_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4119_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v_expr_4114_);
lean_dec(v___x_4111_);
lean_dec(v_generation_4100_);
lean_dec_ref(v_proof_4099_);
lean_dec_ref(v_prop_4098_);
v_a_4138_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4115_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4115_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v___x_4111_);
lean_dec(v_generation_4100_);
lean_dec_ref(v_proof_4099_);
lean_dec_ref(v_prop_4098_);
v_a_4146_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4112_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4112_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4154_, lean_object* v_prop_4155_, lean_object* v_proof_4156_, lean_object* v_generation_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4154_, v_prop_4155_, v_proof_4156_, v_generation_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_goal_4169_, lean_object* v___f_4170_, lean_object* v_kp_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_mvarId_4182_; lean_object* v___x_4183_; 
v_mvarId_4182_ = lean_ctor_get(v_goal_4169_, 1);
lean_inc(v_mvarId_4182_);
lean_dec_ref(v_goal_4169_);
v___x_4183_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4182_, v___f_4170_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
lean_inc(v___y_4176_);
lean_inc_ref(v___y_4175_);
lean_inc(v___y_4174_);
lean_inc_ref(v___y_4173_);
lean_inc(v___y_4172_);
v___x_4185_ = lean_apply_11(v_kp_4171_, v_a_4184_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, lean_box(0));
return v___x_4185_;
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref(v_kp_4171_);
v_a_4186_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4183_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4183_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_goal_4194_, lean_object* v___f_4195_, lean_object* v_kp_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4194_, v___f_4195_, v_kp_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4208_, lean_object* v_prop_4209_, lean_object* v_generation_4210_, lean_object* v_goal_4211_, lean_object* v_kna_4212_, lean_object* v_kp_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v___f_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; 
lean_inc(v_generation_4210_);
lean_inc_ref(v_proof_4208_);
lean_inc_ref(v_prop_4209_);
lean_inc_ref_n(v_goal_4211_, 2);
v___f_4224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4224_, 0, v_goal_4211_);
lean_closure_set(v___f_4224_, 1, v_prop_4209_);
lean_closure_set(v___f_4224_, 2, v_proof_4208_);
lean_closure_set(v___f_4224_, 3, v_generation_4210_);
lean_inc_ref(v_kp_4213_);
v___f_4225_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4225_, 0, v_goal_4211_);
lean_closure_set(v___f_4225_, 1, v___f_4224_);
lean_closure_set(v___f_4225_, 2, v_kp_4213_);
v___x_4226_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4209_, v_a_4215_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; uint8_t v___x_4228_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4228_ = lean_unbox(v_a_4227_);
lean_dec(v_a_4227_);
if (v___x_4228_ == 0)
{
lean_object* v_mvarId_4229_; lean_object* v___x_4230_; 
lean_dec_ref(v_kp_4213_);
lean_dec_ref(v_kna_4212_);
lean_dec(v_generation_4210_);
lean_dec_ref(v_prop_4209_);
lean_dec_ref(v_proof_4208_);
v_mvarId_4229_ = lean_ctor_get(v_goal_4211_, 1);
lean_inc(v_mvarId_4229_);
lean_dec_ref(v_goal_4211_);
v___x_4230_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4229_, v___f_4225_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_dec_ref(v___f_4225_);
v___x_4231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4232_ = l_Lean_Core_mkFreshUserName(v___x_4231_, v_a_4221_, v_a_4222_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v_toGoalState_4234_; lean_object* v_mvarId_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4253_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4232_, 1);
v_toGoalState_4234_ = lean_ctor_get(v_goal_4211_, 0);
v_mvarId_4235_ = lean_ctor_get(v_goal_4211_, 1);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_goal_4211_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4237_ = v_goal_4211_;
v_isShared_4238_ = v_isSharedCheck_4253_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_mvarId_4235_);
lean_inc(v_toGoalState_4234_);
lean_dec(v_goal_4211_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4253_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_MVarId_assert(v_mvarId_4235_, v_a_4233_, v_prop_4209_, v_proof_4208_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 1, v_a_4240_);
v___x_4242_ = v___x_4237_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_toGoalState_4234_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_a_4240_);
v___x_4242_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_Meta_Grind_Action_intros(v_generation_4210_, v___x_4242_, v_kna_4212_, v_kp_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
return v___x_4243_;
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_del_object(v___x_4237_);
lean_dec_ref(v_toGoalState_4234_);
lean_dec_ref(v_kp_4213_);
lean_dec_ref(v_kna_4212_);
lean_dec(v_generation_4210_);
v_a_4245_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4239_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4239_);
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
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec_ref(v_kp_4213_);
lean_dec_ref(v_kna_4212_);
lean_dec_ref(v_goal_4211_);
lean_dec(v_generation_4210_);
lean_dec_ref(v_prop_4209_);
lean_dec_ref(v_proof_4208_);
v_a_4254_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4232_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4232_);
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
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v___f_4225_);
lean_dec_ref(v_kp_4213_);
lean_dec_ref(v_kna_4212_);
lean_dec_ref(v_goal_4211_);
lean_dec(v_generation_4210_);
lean_dec_ref(v_prop_4209_);
lean_dec_ref(v_proof_4208_);
v_a_4262_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4226_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4226_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4270_, lean_object* v_prop_4271_, lean_object* v_generation_4272_, lean_object* v_goal_4273_, lean_object* v_kna_4274_, lean_object* v_kp_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4270_, v_prop_4271_, v_generation_4272_, v_goal_4273_, v_kna_4274_, v_kp_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4287_, lean_object* v_kna_4288_, lean_object* v_kp_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v_toGoalState_4300_; uint8_t v_inconsistent_4301_; 
v_toGoalState_4300_ = lean_ctor_get(v_goal_4287_, 0);
lean_inc_ref(v_toGoalState_4300_);
v_inconsistent_4301_ = lean_ctor_get_uint8(v_toGoalState_4300_, sizeof(void*)*18);
if (v_inconsistent_4301_ == 0)
{
lean_object* v_mvarId_4302_; lean_object* v_nextDeclIdx_4303_; lean_object* v_enodeMap_4304_; lean_object* v_exprs_4305_; lean_object* v_parents_4306_; lean_object* v_congrTable_4307_; lean_object* v_appMap_4308_; lean_object* v_indicesFound_4309_; lean_object* v_toProcess_4310_; lean_object* v_internalizing_4311_; lean_object* v_nextIdx_4312_; lean_object* v_newRawFacts_4313_; lean_object* v_facts_4314_; lean_object* v_extThms_4315_; lean_object* v_ematch_4316_; lean_object* v_inj_4317_; lean_object* v_split_4318_; lean_object* v_clean_4319_; lean_object* v_sstates_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4360_; 
v_mvarId_4302_ = lean_ctor_get(v_goal_4287_, 1);
v_nextDeclIdx_4303_ = lean_ctor_get(v_toGoalState_4300_, 0);
v_enodeMap_4304_ = lean_ctor_get(v_toGoalState_4300_, 1);
v_exprs_4305_ = lean_ctor_get(v_toGoalState_4300_, 2);
v_parents_4306_ = lean_ctor_get(v_toGoalState_4300_, 3);
v_congrTable_4307_ = lean_ctor_get(v_toGoalState_4300_, 4);
v_appMap_4308_ = lean_ctor_get(v_toGoalState_4300_, 5);
v_indicesFound_4309_ = lean_ctor_get(v_toGoalState_4300_, 6);
v_toProcess_4310_ = lean_ctor_get(v_toGoalState_4300_, 7);
v_internalizing_4311_ = lean_ctor_get(v_toGoalState_4300_, 8);
v_nextIdx_4312_ = lean_ctor_get(v_toGoalState_4300_, 9);
v_newRawFacts_4313_ = lean_ctor_get(v_toGoalState_4300_, 10);
v_facts_4314_ = lean_ctor_get(v_toGoalState_4300_, 11);
v_extThms_4315_ = lean_ctor_get(v_toGoalState_4300_, 12);
v_ematch_4316_ = lean_ctor_get(v_toGoalState_4300_, 13);
v_inj_4317_ = lean_ctor_get(v_toGoalState_4300_, 14);
v_split_4318_ = lean_ctor_get(v_toGoalState_4300_, 15);
v_clean_4319_ = lean_ctor_get(v_toGoalState_4300_, 16);
v_sstates_4320_ = lean_ctor_get(v_toGoalState_4300_, 17);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_toGoalState_4300_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4322_ = v_toGoalState_4300_;
v_isShared_4323_ = v_isSharedCheck_4360_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_sstates_4320_);
lean_inc(v_clean_4319_);
lean_inc(v_split_4318_);
lean_inc(v_inj_4317_);
lean_inc(v_ematch_4316_);
lean_inc(v_extThms_4315_);
lean_inc(v_facts_4314_);
lean_inc(v_newRawFacts_4313_);
lean_inc(v_nextIdx_4312_);
lean_inc(v_internalizing_4311_);
lean_inc(v_toProcess_4310_);
lean_inc(v_indicesFound_4309_);
lean_inc(v_appMap_4308_);
lean_inc(v_congrTable_4307_);
lean_inc(v_parents_4306_);
lean_inc(v_exprs_4305_);
lean_inc(v_enodeMap_4304_);
lean_inc(v_nextDeclIdx_4303_);
lean_dec(v_toGoalState_4300_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4360_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4313_);
if (lean_obj_tag(v___x_4324_) == 1)
{
lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4356_; 
lean_inc(v_mvarId_4302_);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_goal_4287_);
if (v_isSharedCheck_4356_ == 0)
{
lean_object* v_unused_4357_; lean_object* v_unused_4358_; 
v_unused_4357_ = lean_ctor_get(v_goal_4287_, 1);
lean_dec(v_unused_4357_);
v_unused_4358_ = lean_ctor_get(v_goal_4287_, 0);
lean_dec(v_unused_4358_);
v___x_4326_ = v_goal_4287_;
v_isShared_4327_ = v_isSharedCheck_4356_;
goto v_resetjp_4325_;
}
else
{
lean_dec(v_goal_4287_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4356_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v_val_4328_; lean_object* v_fst_4329_; lean_object* v_snd_4330_; lean_object* v_proof_4331_; lean_object* v_prop_4332_; lean_object* v_generation_4333_; lean_object* v_splitSource_4334_; lean_object* v_ematchDiagSource_4335_; lean_object* v_simp_4336_; lean_object* v_simpMethods_4337_; lean_object* v_symSimpMethods_4338_; lean_object* v_symDSimpMethods_4339_; lean_object* v_config_4340_; lean_object* v_anchorRefs_x3f_4341_; uint8_t v_cheapCases_4342_; uint8_t v_reportMVarIssue_4343_; lean_object* v_symPrios_4344_; lean_object* v_extensions_4345_; uint8_t v_debug_4346_; uint8_t v_ematchDiag_4347_; lean_object* v___x_4349_; 
v_val_4328_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_val_4328_);
lean_dec_ref_known(v___x_4324_, 1);
v_fst_4329_ = lean_ctor_get(v_val_4328_, 0);
lean_inc(v_fst_4329_);
v_snd_4330_ = lean_ctor_get(v_val_4328_, 1);
lean_inc(v_snd_4330_);
lean_dec(v_val_4328_);
v_proof_4331_ = lean_ctor_get(v_fst_4329_, 0);
lean_inc_ref(v_proof_4331_);
v_prop_4332_ = lean_ctor_get(v_fst_4329_, 1);
lean_inc_ref(v_prop_4332_);
v_generation_4333_ = lean_ctor_get(v_fst_4329_, 2);
lean_inc(v_generation_4333_);
v_splitSource_4334_ = lean_ctor_get(v_fst_4329_, 3);
lean_inc(v_splitSource_4334_);
v_ematchDiagSource_4335_ = lean_ctor_get(v_fst_4329_, 4);
lean_inc(v_ematchDiagSource_4335_);
lean_dec(v_fst_4329_);
v_simp_4336_ = lean_ctor_get(v_a_4291_, 0);
v_simpMethods_4337_ = lean_ctor_get(v_a_4291_, 1);
v_symSimpMethods_4338_ = lean_ctor_get(v_a_4291_, 2);
v_symDSimpMethods_4339_ = lean_ctor_get(v_a_4291_, 3);
v_config_4340_ = lean_ctor_get(v_a_4291_, 4);
v_anchorRefs_x3f_4341_ = lean_ctor_get(v_a_4291_, 5);
v_cheapCases_4342_ = lean_ctor_get_uint8(v_a_4291_, sizeof(void*)*10);
v_reportMVarIssue_4343_ = lean_ctor_get_uint8(v_a_4291_, sizeof(void*)*10 + 1);
v_symPrios_4344_ = lean_ctor_get(v_a_4291_, 8);
v_extensions_4345_ = lean_ctor_get(v_a_4291_, 9);
v_debug_4346_ = lean_ctor_get_uint8(v_a_4291_, sizeof(void*)*10 + 2);
v_ematchDiag_4347_ = lean_ctor_get_uint8(v_a_4291_, sizeof(void*)*10 + 3);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 10, v_snd_4330_);
v___x_4349_ = v___x_4322_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_nextDeclIdx_4303_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_enodeMap_4304_);
lean_ctor_set(v_reuseFailAlloc_4355_, 2, v_exprs_4305_);
lean_ctor_set(v_reuseFailAlloc_4355_, 3, v_parents_4306_);
lean_ctor_set(v_reuseFailAlloc_4355_, 4, v_congrTable_4307_);
lean_ctor_set(v_reuseFailAlloc_4355_, 5, v_appMap_4308_);
lean_ctor_set(v_reuseFailAlloc_4355_, 6, v_indicesFound_4309_);
lean_ctor_set(v_reuseFailAlloc_4355_, 7, v_toProcess_4310_);
lean_ctor_set(v_reuseFailAlloc_4355_, 8, v_internalizing_4311_);
lean_ctor_set(v_reuseFailAlloc_4355_, 9, v_nextIdx_4312_);
lean_ctor_set(v_reuseFailAlloc_4355_, 10, v_snd_4330_);
lean_ctor_set(v_reuseFailAlloc_4355_, 11, v_facts_4314_);
lean_ctor_set(v_reuseFailAlloc_4355_, 12, v_extThms_4315_);
lean_ctor_set(v_reuseFailAlloc_4355_, 13, v_ematch_4316_);
lean_ctor_set(v_reuseFailAlloc_4355_, 14, v_inj_4317_);
lean_ctor_set(v_reuseFailAlloc_4355_, 15, v_split_4318_);
lean_ctor_set(v_reuseFailAlloc_4355_, 16, v_clean_4319_);
lean_ctor_set(v_reuseFailAlloc_4355_, 17, v_sstates_4320_);
lean_ctor_set_uint8(v_reuseFailAlloc_4355_, sizeof(void*)*18, v_inconsistent_4301_);
v___x_4349_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v_goal_4351_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4349_);
v_goal_4351_ = v___x_4326_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4354_, 1, v_mvarId_4302_);
v_goal_4351_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_inc_ref(v_extensions_4345_);
lean_inc_ref(v_symPrios_4344_);
lean_inc(v_anchorRefs_x3f_4341_);
lean_inc_ref(v_config_4340_);
lean_inc_ref(v_symDSimpMethods_4339_);
lean_inc_ref(v_symSimpMethods_4338_);
lean_inc_ref(v_simpMethods_4337_);
lean_inc_ref(v_simp_4336_);
v___x_4352_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_4352_, 0, v_simp_4336_);
lean_ctor_set(v___x_4352_, 1, v_simpMethods_4337_);
lean_ctor_set(v___x_4352_, 2, v_symSimpMethods_4338_);
lean_ctor_set(v___x_4352_, 3, v_symDSimpMethods_4339_);
lean_ctor_set(v___x_4352_, 4, v_config_4340_);
lean_ctor_set(v___x_4352_, 5, v_anchorRefs_x3f_4341_);
lean_ctor_set(v___x_4352_, 6, v_splitSource_4334_);
lean_ctor_set(v___x_4352_, 7, v_ematchDiagSource_4335_);
lean_ctor_set(v___x_4352_, 8, v_symPrios_4344_);
lean_ctor_set(v___x_4352_, 9, v_extensions_4345_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*10, v_cheapCases_4342_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*10 + 1, v_reportMVarIssue_4343_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*10 + 2, v_debug_4346_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*10 + 3, v_ematchDiag_4347_);
v___x_4353_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4331_, v_prop_4332_, v_generation_4333_, v_goal_4351_, v_kna_4288_, v_kp_4289_, v_a_4290_, v___x_4352_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
lean_dec_ref_known(v___x_4352_, 10);
return v___x_4353_;
}
}
}
}
else
{
lean_object* v___x_4359_; 
lean_dec(v___x_4324_);
lean_del_object(v___x_4322_);
lean_dec_ref(v_sstates_4320_);
lean_dec_ref(v_clean_4319_);
lean_dec_ref(v_split_4318_);
lean_dec_ref(v_inj_4317_);
lean_dec_ref(v_ematch_4316_);
lean_dec_ref(v_extThms_4315_);
lean_dec_ref(v_facts_4314_);
lean_dec(v_nextIdx_4312_);
lean_dec_ref(v_internalizing_4311_);
lean_dec_ref(v_toProcess_4310_);
lean_dec_ref(v_indicesFound_4309_);
lean_dec_ref(v_appMap_4308_);
lean_dec_ref(v_congrTable_4307_);
lean_dec_ref(v_parents_4306_);
lean_dec_ref(v_exprs_4305_);
lean_dec_ref(v_enodeMap_4304_);
lean_dec(v_nextDeclIdx_4303_);
lean_dec_ref(v_kp_4289_);
lean_inc(v_a_4298_);
lean_inc_ref(v_a_4297_);
lean_inc(v_a_4296_);
lean_inc_ref(v_a_4295_);
lean_inc(v_a_4294_);
lean_inc_ref(v_a_4293_);
lean_inc(v_a_4292_);
lean_inc_ref(v_a_4291_);
lean_inc(v_a_4290_);
v___x_4359_ = lean_apply_11(v_kna_4288_, v_goal_4287_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, lean_box(0));
return v___x_4359_;
}
}
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec_ref(v_toGoalState_4300_);
lean_dec_ref(v_kp_4289_);
lean_dec_ref(v_kna_4288_);
lean_dec_ref(v_goal_4287_);
v___x_4361_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4363_, lean_object* v_kna_4364_, lean_object* v_kp_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4363_, v_kna_4364_, v_kp_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4377_, lean_object* v_kp_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = lean_unsigned_to_nat(1000000u);
v___x_4390_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4391_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4389_, v___x_4390_, v_a_4377_, v_kp_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4392_, lean_object* v_kp_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4392_, v_kp_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4405_, lean_object* v_kna_4406_, lean_object* v_kp_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4405_, v_kp_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4419_, lean_object* v_kna_4420_, lean_object* v_kp_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4419_, v_kna_4420_, v_kp_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_kna_4420_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4433_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4448_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4461_, lean_object* v___f_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Lean_Meta_Grind_Action_andThen(v_a_4461_, v___f_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4477_, lean_object* v___f_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4477_, v___f_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___f_4495_; lean_object* v___x_4496_; 
v___f_4495_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___x_4496_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4505_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4505_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4505_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___f_4501_; lean_object* v___x_4503_; 
v___f_4501_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4501_, 0, v_a_4497_);
lean_closure_set(v___f_4501_, 1, v___f_4495_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v___f_4501_);
v___x_4503_ = v___x_4499_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___f_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
else
{
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4507_;
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
