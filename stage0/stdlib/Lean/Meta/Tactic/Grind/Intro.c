// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Injection import Lean.Meta.Tactic.Grind.Core import Lean.Meta.Tactic.Grind.MarkAccessible import Init.Grind.Util
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_isEagerSplit___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
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
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedGoal_default;
lean_object* l_Lean_Meta_Grind_Solvers_mkActionCore();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx(lean_object* v_x_1_){
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 1:
{
lean_object* v_fvarId_10_; lean_object* v_goal_11_; lean_object* v___x_12_; 
v_fvarId_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_fvarId_10_);
v_goal_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_goal_11_);
lean_dec_ref_known(v_t_8_, 2);
v___x_12_ = lean_apply_2(v_k_9_, v_fvarId_10_, v_goal_11_);
return v___x_12_;
}
case 3:
{
lean_object* v_fvarId_13_; lean_object* v_goal_14_; lean_object* v___x_15_; 
v_fvarId_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_fvarId_13_);
v_goal_14_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_goal_14_);
lean_dec_ref_known(v_t_8_, 2);
v___x_15_ = lean_apply_2(v_k_9_, v_fvarId_13_, v_goal_14_);
return v___x_15_;
}
default: 
{
lean_object* v_goal_16_; lean_object* v___x_17_; 
v_goal_16_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_goal_16_);
lean_dec_ref(v_t_8_);
v___x_17_ = lean_apply_1(v_k_9_, v_goal_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim___redArg(lean_object* v_t_30_, lean_object* v_done_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_30_, v_done_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_done_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_34_, v_done_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim___redArg(lean_object* v_t_38_, lean_object* v_newHyp_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_38_, v_newHyp_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_newHyp_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_42_, v_newHyp_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim___redArg(lean_object* v_t_46_, lean_object* v_newDepHyp_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_46_, v_newDepHyp_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_newDepHyp_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_50_, v_newDepHyp_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim___redArg(lean_object* v_t_54_, lean_object* v_newLocal_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_54_, v_newLocal_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_newLocal_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(v_t_58_, v_newLocal_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = l_Lean_Meta_Grind_instInhabitedGoal_default;
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0, &l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Grind_instInhabitedIntroResult_default;
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object* v_e_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = l_Lean_Expr_cleanupAnnotations(v_e_73_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v___x_74_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v_arg_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_arg_77_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_arg_77_);
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3));
v___x_80_ = l_Lean_Expr_isConstOf(v___x_78_, v___x_79_);
lean_dec_ref(v___x_78_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec_ref(v_arg_77_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v_arg_77_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object* v_e_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
uint8_t v___x_95_; 
lean_inc_ref(v_e_83_);
v___x_95_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_83_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_inc_ref(v_e_83_);
v___x_96_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_83_);
if (lean_obj_tag(v___x_96_) == 1)
{
lean_object* v_val_97_; lean_object* v___x_98_; 
lean_dec_ref(v_e_83_);
v_val_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = l_Lean_Meta_Sym_canon(v_val_97_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = l_Lean_Meta_Sym_shareCommon(v_a_99_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_111_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_105_ = 1;
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_107_, 0, v_a_101_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*2, v___x_105_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_107_);
v___x_109_ = v___x_103_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_100_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_100_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_98_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_98_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v___x_96_);
lean_inc(v_a_93_);
lean_inc_ref(v_a_92_);
lean_inc(v_a_91_);
lean_inc_ref(v_a_90_);
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc(v_a_84_);
v___x_128_ = lean_grind_preprocess(v_e_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_128_;
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_83_);
lean_inc(v_a_93_);
lean_inc_ref(v_a_92_);
lean_inc(v_a_91_);
lean_inc_ref(v_a_90_);
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc(v_a_84_);
v___x_130_ = lean_grind_preprocess(v___x_129_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object* v_e_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec(v_a_132_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_144_, lean_object* v_str_145_, lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_startInclusive_148_; lean_object* v_endExclusive_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_startInclusive_148_ = lean_ctor_get(v___x_144_, 1);
v_endExclusive_149_ = lean_ctor_get(v___x_144_, 2);
v___x_150_ = lean_nat_sub(v_endExclusive_149_, v_startInclusive_148_);
v___x_151_ = lean_nat_dec_eq(v_a_146_, v___x_150_);
lean_dec(v___x_150_);
if (v___x_151_ == 0)
{
uint32_t v___x_152_; uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_152_ = lean_string_utf8_get_fast(v_str_145_, v_a_146_);
v___x_153_ = 95;
v___x_154_ = lean_uint32_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_box(0);
v___x_156_ = lean_string_utf8_next_fast(v_str_145_, v_a_146_);
lean_dec(v_a_146_);
v_a_146_ = v___x_156_;
v_b_147_ = v___x_155_;
goto _start;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_a_146_);
return v___x_158_;
}
}
else
{
lean_dec(v_a_146_);
lean_inc(v_b_147_);
return v_b_147_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_159_, lean_object* v_str_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_159_, v_str_160_, v_a_161_, v_b_162_);
lean_dec(v_b_162_);
lean_dec_ref(v_str_160_);
lean_dec_ref(v___x_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_170_, lean_object* v_type_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___y_181_; 
if (lean_obj_tag(v_name_170_) == 1)
{
lean_object* v_str_205_; lean_object* v___y_207_; lean_object* v_searcher_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_str_205_ = lean_ctor_get(v_name_170_, 1);
lean_inc_ref_n(v_str_205_, 2);
lean_dec_ref_known(v_name_170_, 2);
v_searcher_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_string_utf8_byte_size(v_str_205_);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v_str_205_);
lean_ctor_set(v___x_227_, 1, v_searcher_225_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_227_, v_str_205_, v_searcher_225_, v___x_228_);
lean_dec_ref_known(v___x_227_, 3);
if (lean_obj_tag(v___x_229_) == 0)
{
v___y_207_ = v___x_226_;
goto v___jp_206_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_229_, 1);
v___y_207_ = v_val_230_;
goto v___jp_206_;
}
v___jp_206_:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_string_utf8_byte_size(v_str_205_);
v___x_209_ = lean_nat_dec_eq(v___y_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v_suffix_211_; uint8_t v___x_212_; 
v___x_210_ = lean_string_utf8_next_fast(v_str_205_, v___y_207_);
lean_inc_ref(v_str_205_);
v_suffix_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_211_, 0, v_str_205_);
lean_ctor_set(v_suffix_211_, 1, v___x_210_);
lean_ctor_set(v_suffix_211_, 2, v___x_208_);
v___x_212_ = l_String_Slice_isNat(v_suffix_211_);
lean_dec_ref_known(v_suffix_211_, 3);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v___y_207_);
lean_dec_ref(v_type_171_);
v___x_213_ = lean_box(0);
v___x_214_ = l_Lean_Name_str___override(v___x_213_, v_str_205_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v___y_207_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v_type_171_);
v___x_218_ = lean_string_utf8_extract_fast(v_str_205_, v___x_216_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v_str_205_);
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_Name_str___override(v___x_219_, v___x_218_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
else
{
lean_dec(v___y_207_);
lean_dec_ref(v_str_205_);
v___y_178_ = v_a_172_;
v___y_179_ = v_a_173_;
v___y_180_ = v_a_174_;
v___y_181_ = v_a_175_;
goto v___jp_177_;
}
}
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v___y_207_);
lean_dec_ref(v_type_171_);
v___x_222_ = lean_box(0);
v___x_223_ = l_Lean_Name_str___override(v___x_222_, v_str_205_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
else
{
lean_dec(v_name_170_);
v___y_178_ = v_a_172_;
v___y_179_ = v_a_173_;
v___y_180_ = v_a_174_;
v___y_181_ = v_a_175_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_isProp(v_type_171_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_196_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_196_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_196_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_196_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_a_183_);
lean_dec(v_a_183_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_194_ = v___x_185_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_182_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_182_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_231_, lean_object* v_type_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_231_, v_type_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_239_, lean_object* v_str_240_, lean_object* v_inst_241_, lean_object* v_R_242_, lean_object* v_a_243_, lean_object* v_b_244_, lean_object* v_c_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_239_, v_str_240_, v_a_243_, v_b_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_247_, lean_object* v_str_248_, lean_object* v_inst_249_, lean_object* v_R_250_, lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_c_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_247_, v_str_248_, v_inst_249_, v_R_250_, v_a_251_, v_b_252_, v_c_253_);
lean_dec(v_b_252_);
lean_dec_ref(v_str_248_);
lean_dec_ref(v___x_247_);
return v_res_254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_255_, lean_object* v_i_256_, lean_object* v_k_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_array_get_size(v_keys_255_);
v___x_259_ = lean_nat_dec_lt(v_i_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_dec(v_i_256_);
return v___x_259_;
}
else
{
lean_object* v_k_x27_260_; uint8_t v___x_261_; 
v_k_x27_260_ = lean_array_fget_borrowed(v_keys_255_, v_i_256_);
v___x_261_ = lean_name_eq(v_k_257_, v_k_x27_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_i_256_, v___x_262_);
lean_dec(v_i_256_);
v_i_256_ = v___x_263_;
goto _start;
}
else
{
lean_dec(v_i_256_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_265_, lean_object* v_i_266_, lean_object* v_k_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_265_, v_i_266_, v_k_267_);
lean_dec(v_k_267_);
lean_dec_ref(v_keys_265_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_270_, size_t v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v_es_273_; lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v_j_277_; lean_object* v___x_278_; 
v_es_273_ = lean_ctor_get(v_x_270_, 0);
v___x_274_ = lean_box(2);
v___x_275_ = ((size_t)31ULL);
v___x_276_ = lean_usize_land(v_x_271_, v___x_275_);
v_j_277_ = lean_usize_to_nat(v___x_276_);
v___x_278_ = lean_array_get_borrowed(v___x_274_, v_es_273_, v_j_277_);
lean_dec(v_j_277_);
switch(lean_obj_tag(v___x_278_))
{
case 0:
{
lean_object* v_key_279_; uint8_t v___x_280_; 
v_key_279_ = lean_ctor_get(v___x_278_, 0);
v___x_280_ = lean_name_eq(v_x_272_, v_key_279_);
return v___x_280_;
}
case 1:
{
lean_object* v_node_281_; size_t v___x_282_; size_t v___x_283_; 
v_node_281_ = lean_ctor_get(v___x_278_, 0);
v___x_282_ = ((size_t)5ULL);
v___x_283_ = lean_usize_shift_right(v_x_271_, v___x_282_);
v_x_270_ = v_node_281_;
v_x_271_ = v___x_283_;
goto _start;
}
default: 
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
}
else
{
lean_object* v_ks_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_ks_286_ = lean_ctor_get(v_x_270_, 0);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_286_, v___x_287_, v_x_272_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
size_t v_x_39908__boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_x_39908__boxed_292_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_res_293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_289_, v_x_39908__boxed_292_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_x_289_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint64_t v___y_298_; 
if (lean_obj_tag(v_x_296_) == 0)
{
uint64_t v___x_301_; 
v___x_301_ = 1723ULL;
v___y_298_ = v___x_301_;
goto v___jp_297_;
}
else
{
uint64_t v_hash_302_; 
v_hash_302_ = lean_ctor_get_uint64(v_x_296_, sizeof(void*)*2);
v___y_298_ = v_hash_302_;
goto v___jp_297_;
}
v___jp_297_:
{
size_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_uint64_to_usize(v___y_298_);
v___x_300_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_295_, v___x_299_, v_x_296_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec_ref(v_x_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_toGoalState_312_; lean_object* v_clean_313_; lean_object* v_snd_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_331_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_toGoalState_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_toGoalState_312_);
lean_dec(v___x_311_);
v_clean_313_ = lean_ctor_get(v_toGoalState_312_, 15);
lean_inc_ref(v_clean_313_);
lean_dec_ref(v_toGoalState_312_);
v_snd_314_ = lean_ctor_get(v_a_308_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_a_308_, 0);
lean_dec(v_unused_332_);
v___x_316_ = v_a_308_;
v_isShared_317_ = v_isSharedCheck_331_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snd_314_);
lean_dec(v_a_308_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_331_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_used_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_used_318_ = lean_ctor_get(v_clean_313_, 0);
lean_inc_ref(v_used_318_);
lean_dec_ref(v_clean_313_);
lean_inc(v_snd_314_);
lean_inc(v_a_307_);
v___x_319_ = lean_name_append_index_after(v_a_307_, v_snd_314_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_snd_314_, v___x_320_);
lean_dec(v_snd_314_);
v___x_322_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_318_, v___x_319_);
lean_dec_ref(v_used_318_);
if (v___x_322_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_a_307_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___x_321_);
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_324_ = v___x_316_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_321_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
else
{
lean_object* v___x_328_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___x_321_);
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_328_ = v___x_316_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_321_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_308_ = v___x_328_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_333_, v_a_334_, v___y_335_);
lean_dec(v___y_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_ks_342_; lean_object* v_vs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_367_; 
v_ks_342_ = lean_ctor_get(v_x_338_, 0);
v_vs_343_ = lean_ctor_get(v_x_338_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_367_ == 0)
{
v___x_345_ = v_x_338_;
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_vs_343_);
lean_inc(v_ks_342_);
lean_dec(v_x_338_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_array_get_size(v_ks_342_);
v___x_348_ = lean_nat_dec_lt(v_x_339_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_dec(v_x_339_);
v___x_349_ = lean_array_push(v_ks_342_, v_x_340_);
v___x_350_ = lean_array_push(v_vs_343_, v_x_341_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_350_);
lean_ctor_set(v___x_345_, 0, v___x_349_);
v___x_352_ = v___x_345_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
else
{
lean_object* v_k_x27_354_; uint8_t v___x_355_; 
v_k_x27_354_ = lean_array_fget_borrowed(v_ks_342_, v_x_339_);
v___x_355_ = lean_name_eq(v_x_340_, v_k_x27_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_357_; 
if (v_isShared_346_ == 0)
{
v___x_357_ = v___x_345_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_ks_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_vs_343_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_x_339_, v___x_358_);
lean_dec(v_x_339_);
v_x_338_ = v___x_357_;
v_x_339_ = v___x_359_;
goto _start;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = lean_array_fset(v_ks_342_, v_x_339_, v_x_340_);
v___x_363_ = lean_array_fset(v_vs_343_, v_x_339_, v_x_341_);
lean_dec(v_x_339_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_363_);
lean_ctor_set(v___x_345_, 0, v___x_362_);
v___x_365_ = v___x_345_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_368_, lean_object* v_k_369_, lean_object* v_v_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_368_, v___x_371_, v_k_369_, v_v_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_374_, size_t v_x_375_, size_t v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v_es_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v_j_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_es_379_ = lean_ctor_get(v_x_374_, 0);
v___x_380_ = ((size_t)31ULL);
v___x_381_ = lean_usize_land(v_x_375_, v___x_380_);
v_j_382_ = lean_usize_to_nat(v___x_381_);
v___x_383_ = lean_array_get_size(v_es_379_);
v___x_384_ = lean_nat_dec_lt(v_j_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v_j_382_);
lean_dec(v_x_378_);
lean_dec(v_x_377_);
return v_x_374_;
}
else
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_423_; 
lean_inc_ref(v_es_379_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_x_374_, 0);
lean_dec(v_unused_424_);
v___x_386_ = v_x_374_;
v_isShared_387_ = v_isSharedCheck_423_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_x_374_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_423_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_v_388_; lean_object* v___x_389_; lean_object* v_xs_x27_390_; lean_object* v___y_392_; 
v_v_388_ = lean_array_fget(v_es_379_, v_j_382_);
v___x_389_ = lean_box(0);
v_xs_x27_390_ = lean_array_fset(v_es_379_, v_j_382_, v___x_389_);
switch(lean_obj_tag(v_v_388_))
{
case 0:
{
lean_object* v_key_397_; lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
v_key_397_ = lean_ctor_get(v_v_388_, 0);
v_val_398_ = lean_ctor_get(v_v_388_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_v_388_);
if (v_isSharedCheck_408_ == 0)
{
v___x_400_ = v_v_388_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_inc(v_key_397_);
lean_dec(v_v_388_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v___x_402_; 
v___x_402_ = lean_name_eq(v_x_377_, v_key_397_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_del_object(v___x_400_);
v___x_403_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_397_, v_val_398_, v_x_377_, v_x_378_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___y_392_ = v___x_404_;
goto v___jp_391_;
}
else
{
lean_object* v___x_406_; 
lean_dec(v_val_398_);
lean_dec(v_key_397_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_x_378_);
lean_ctor_set(v___x_400_, 0, v_x_377_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_x_377_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_x_378_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v___y_392_ = v___x_406_;
goto v___jp_391_;
}
}
}
}
case 1:
{
lean_object* v_node_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v_node_409_ = lean_ctor_get(v_v_388_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_v_388_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v_v_388_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_node_409_);
lean_dec(v_v_388_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_413_ = ((size_t)5ULL);
v___x_414_ = lean_usize_shift_right(v_x_375_, v___x_413_);
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_x_376_, v___x_415_);
v___x_417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_409_, v___x_414_, v___x_416_, v_x_377_, v_x_378_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_417_);
v___x_419_ = v___x_411_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v___y_392_ = v___x_419_;
goto v___jp_391_;
}
}
}
default: 
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_x_377_);
lean_ctor_set(v___x_422_, 1, v_x_378_);
v___y_392_ = v___x_422_;
goto v___jp_391_;
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_array_fset(v_xs_x27_390_, v_j_382_, v___y_392_);
lean_dec(v_j_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_393_);
v___x_395_ = v___x_386_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
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
}
else
{
lean_object* v_ks_425_; lean_object* v_vs_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_446_; 
v_ks_425_ = lean_ctor_get(v_x_374_, 0);
v_vs_426_ = lean_ctor_get(v_x_374_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_446_ == 0)
{
v___x_428_ = v_x_374_;
v_isShared_429_ = v_isSharedCheck_446_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_vs_426_);
lean_inc(v_ks_425_);
lean_dec(v_x_374_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_446_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_ks_425_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_vs_426_);
v___x_431_ = v_reuseFailAlloc_445_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v_newNode_432_; uint8_t v___y_434_; size_t v___x_440_; uint8_t v___x_441_; 
v_newNode_432_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_431_, v_x_377_, v_x_378_);
v___x_440_ = ((size_t)7ULL);
v___x_441_ = lean_usize_dec_le(v___x_440_, v_x_376_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_432_);
v___x_443_ = lean_unsigned_to_nat(4u);
v___x_444_ = lean_nat_dec_lt(v___x_442_, v___x_443_);
lean_dec(v___x_442_);
v___y_434_ = v___x_444_;
goto v___jp_433_;
}
else
{
v___y_434_ = v___x_441_;
goto v___jp_433_;
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
lean_object* v_ks_435_; lean_object* v_vs_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_ks_435_ = lean_ctor_get(v_newNode_432_, 0);
lean_inc_ref(v_ks_435_);
v_vs_436_ = lean_ctor_get(v_newNode_432_, 1);
lean_inc_ref(v_vs_436_);
lean_dec_ref(v_newNode_432_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_376_, v_ks_435_, v_vs_436_, v___x_437_, v___x_438_);
lean_dec_ref(v_vs_436_);
lean_dec_ref(v_ks_435_);
return v___x_439_;
}
else
{
return v_newNode_432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_447_, lean_object* v_keys_448_, lean_object* v_vals_449_, lean_object* v_i_450_, lean_object* v_entries_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_array_get_size(v_keys_448_);
v___x_453_ = lean_nat_dec_lt(v_i_450_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v_i_450_);
return v_entries_451_;
}
else
{
lean_object* v_k_454_; lean_object* v_v_455_; uint64_t v___y_457_; 
v_k_454_ = lean_array_fget_borrowed(v_keys_448_, v_i_450_);
v_v_455_ = lean_array_fget_borrowed(v_vals_449_, v_i_450_);
if (lean_obj_tag(v_k_454_) == 0)
{
uint64_t v___x_468_; 
v___x_468_ = 1723ULL;
v___y_457_ = v___x_468_;
goto v___jp_456_;
}
else
{
uint64_t v_hash_469_; 
v_hash_469_ = lean_ctor_get_uint64(v_k_454_, sizeof(void*)*2);
v___y_457_ = v_hash_469_;
goto v___jp_456_;
}
v___jp_456_:
{
size_t v_h_458_; size_t v___x_459_; lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v_h_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_h_458_ = lean_uint64_to_usize(v___y_457_);
v___x_459_ = ((size_t)5ULL);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_sub(v_depth_447_, v___x_461_);
v___x_463_ = lean_usize_mul(v___x_459_, v___x_462_);
v_h_464_ = lean_usize_shift_right(v_h_458_, v___x_463_);
v___x_465_ = lean_nat_add(v_i_450_, v___x_460_);
lean_dec(v_i_450_);
lean_inc(v_v_455_);
lean_inc(v_k_454_);
v___x_466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_451_, v_h_464_, v_depth_447_, v_k_454_, v_v_455_);
v_i_450_ = v___x_465_;
v_entries_451_ = v___x_466_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_i_473_, lean_object* v_entries_474_){
_start:
{
size_t v_depth_boxed_475_; lean_object* v_res_476_; 
v_depth_boxed_475_ = lean_unbox_usize(v_depth_470_);
lean_dec(v_depth_470_);
v_res_476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_475_, v_keys_471_, v_vals_472_, v_i_473_, v_entries_474_);
lean_dec_ref(v_vals_472_);
lean_dec_ref(v_keys_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
size_t v_x_40088__boxed_482_; size_t v_x_40089__boxed_483_; lean_object* v_res_484_; 
v_x_40088__boxed_482_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_x_40089__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_477_, v_x_40088__boxed_482_, v_x_40089__boxed_483_, v_x_480_, v_x_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
uint64_t v___y_489_; 
if (lean_obj_tag(v_x_486_) == 0)
{
uint64_t v___x_493_; 
v___x_493_ = 1723ULL;
v___y_489_ = v___x_493_;
goto v___jp_488_;
}
else
{
uint64_t v_hash_494_; 
v_hash_494_ = lean_ctor_get_uint64(v_x_486_, sizeof(void*)*2);
v___y_489_ = v_hash_494_;
goto v___jp_488_;
}
v___jp_488_:
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_uint64_to_usize(v___y_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_485_, v___x_490_, v___x_491_, v_x_486_, v_x_487_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_495_, lean_object* v_vals_496_, lean_object* v_i_497_, lean_object* v_k_498_){
_start:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_get_size(v_keys_495_);
v___x_500_ = lean_nat_dec_lt(v_i_497_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v_i_497_);
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v_k_x27_502_; uint8_t v___x_503_; 
v_k_x27_502_ = lean_array_fget_borrowed(v_keys_495_, v_i_497_);
v___x_503_ = lean_name_eq(v_k_498_, v_k_x27_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_i_497_, v___x_504_);
lean_dec(v_i_497_);
v_i_497_ = v___x_505_;
goto _start;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_array_fget_borrowed(v_vals_496_, v_i_497_);
lean_dec(v_i_497_);
lean_inc(v___x_507_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_i_511_, lean_object* v_k_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_509_, v_vals_510_, v_i_511_, v_k_512_);
lean_dec(v_k_512_);
lean_dec_ref(v_vals_510_);
lean_dec_ref(v_keys_509_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_514_, size_t v_x_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_es_517_; lean_object* v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v_j_521_; lean_object* v___x_522_; 
v_es_517_ = lean_ctor_get(v_x_514_, 0);
v___x_518_ = lean_box(2);
v___x_519_ = ((size_t)31ULL);
v___x_520_ = lean_usize_land(v_x_515_, v___x_519_);
v_j_521_ = lean_usize_to_nat(v___x_520_);
v___x_522_ = lean_array_get_borrowed(v___x_518_, v_es_517_, v_j_521_);
lean_dec(v_j_521_);
switch(lean_obj_tag(v___x_522_))
{
case 0:
{
lean_object* v_key_523_; lean_object* v_val_524_; uint8_t v___x_525_; 
v_key_523_ = lean_ctor_get(v___x_522_, 0);
v_val_524_ = lean_ctor_get(v___x_522_, 1);
v___x_525_ = lean_name_eq(v_x_516_, v_key_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
else
{
lean_object* v___x_527_; 
lean_inc(v_val_524_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_val_524_);
return v___x_527_;
}
}
case 1:
{
lean_object* v_node_528_; size_t v___x_529_; size_t v___x_530_; 
v_node_528_ = lean_ctor_get(v___x_522_, 0);
v___x_529_ = ((size_t)5ULL);
v___x_530_ = lean_usize_shift_right(v_x_515_, v___x_529_);
v_x_514_ = v_node_528_;
v_x_515_ = v___x_530_;
goto _start;
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
}
else
{
lean_object* v_ks_533_; lean_object* v_vs_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_ks_533_ = lean_ctor_get(v_x_514_, 0);
v_vs_534_ = lean_ctor_get(v_x_514_, 1);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_533_, v_vs_534_, v___x_535_, v_x_516_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
size_t v_x_40282__boxed_540_; lean_object* v_res_541_; 
v_x_40282__boxed_540_ = lean_unbox_usize(v_x_538_);
lean_dec(v_x_538_);
v_res_541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_537_, v_x_40282__boxed_540_, v_x_539_);
lean_dec(v_x_539_);
lean_dec_ref(v_x_537_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
uint64_t v___y_545_; 
if (lean_obj_tag(v_x_543_) == 0)
{
uint64_t v___x_548_; 
v___x_548_ = 1723ULL;
v___y_545_ = v___x_548_;
goto v___jp_544_;
}
else
{
uint64_t v_hash_549_; 
v_hash_549_ = lean_ctor_get_uint64(v_x_543_, sizeof(void*)*2);
v___y_545_ = v_hash_549_;
goto v___jp_544_;
}
v___jp_544_:
{
size_t v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_uint64_to_usize(v___y_545_);
v___x_547_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_542_, v___x_546_, v_x_543_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_550_, v_x_551_);
lean_dec(v_x_551_);
lean_dec_ref(v_x_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_556_, lean_object* v_type_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_name_570_; lean_object* v___y_571_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v_name_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___x_723_; 
v___x_723_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_560_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_784_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_784_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_784_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_784_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
uint8_t v_clean_749_; 
v_clean_749_ = lean_ctor_get_uint8(v_a_724_, sizeof(void*)*14 + 16);
lean_dec(v_a_724_);
if (v_clean_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_556_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_753_; 
lean_dec_ref(v_type_557_);
lean_dec(v_name_556_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v___x_750_, 1);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v_val_751_);
v___x_753_ = v___x_726_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_val_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
uint8_t v___x_755_; 
lean_dec(v___x_750_);
v___x_755_ = l_Lean_Name_hasMacroScopes(v_name_556_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_del_object(v___x_726_);
lean_dec_ref(v_type_557_);
v___x_756_ = l_Lean_Core_mkFreshUserName(v_name_556_, v_a_566_, v_a_567_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_757_ = l_Lean_Name_eraseMacroScopes(v_name_556_);
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_759_ = lean_name_eq(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_761_ = lean_name_eq(v___x_757_, v___x_760_);
lean_dec(v___x_757_);
if (v___x_761_ == 0)
{
lean_object* v___x_763_; 
lean_dec_ref(v_type_557_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v_name_556_);
v___x_763_ = v___x_726_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_name_556_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
lean_del_object(v___x_726_);
goto v___jp_728_;
}
}
else
{
lean_dec(v___x_757_);
lean_del_object(v___x_726_);
goto v___jp_728_;
}
}
}
}
else
{
uint8_t v___x_765_; 
lean_del_object(v___x_726_);
v___x_765_ = l_Lean_Name_hasMacroScopes(v_name_556_);
if (v___x_765_ == 0)
{
v_name_698_ = v_name_556_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
goto v___jp_697_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_766_ = l_Lean_Name_eraseMacroScopes(v_name_556_);
lean_dec(v_name_556_);
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_781_ = lean_name_eq(v___x_766_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_783_ = lean_name_eq(v___x_766_, v___x_782_);
if (v___x_783_ == 0)
{
v_name_698_ = v___x_766_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
goto v___jp_697_;
}
else
{
goto v___jp_767_;
}
}
else
{
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_768_; 
lean_inc_ref(v_type_557_);
v___x_768_ = l_Lean_Meta_isProp(v_type_557_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_unbox(v_a_769_);
lean_dec(v_a_769_);
if (v___x_770_ == 0)
{
v_name_698_ = v___x_766_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
goto v___jp_697_;
}
else
{
lean_object* v___x_771_; 
lean_dec(v___x_766_);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_698_ = v___x_771_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
goto v___jp_697_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v___x_766_);
lean_dec_ref(v_type_557_);
v_a_772_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_768_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
v___jp_728_:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_isProp(v_type_557_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_740_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_740_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
uint8_t v___x_734_; 
v___x_734_ = lean_unbox(v_a_730_);
lean_dec(v_a_730_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v_name_556_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_name_556_);
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
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_del_object(v___x_732_);
lean_dec(v_name_556_);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_739_ = l_Lean_Core_mkFreshUserName(v___x_738_, v_a_566_, v_a_567_);
return v___x_739_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_name_556_);
v_a_741_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_729_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_729_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_type_557_);
lean_dec(v_name_556_);
v_a_785_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_723_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_723_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
v___jp_569_:
{
lean_object* v___x_572_; lean_object* v_toGoalState_573_; lean_object* v_clean_574_; lean_object* v_mvarId_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_620_; 
v___x_572_ = lean_st_ref_take(v___y_571_);
v_toGoalState_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_toGoalState_573_);
v_clean_574_ = lean_ctor_get(v_toGoalState_573_, 15);
lean_inc_ref(v_clean_574_);
v_mvarId_575_ = lean_ctor_get(v___x_572_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_621_);
v___x_577_ = v___x_572_;
v_isShared_578_ = v_isSharedCheck_620_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_mvarId_575_);
lean_dec(v___x_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_620_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_nextDeclIdx_579_; lean_object* v_enodeMap_580_; lean_object* v_exprs_581_; lean_object* v_parents_582_; lean_object* v_congrTable_583_; lean_object* v_appMap_584_; lean_object* v_indicesFound_585_; lean_object* v_newFacts_586_; uint8_t v_inconsistent_587_; lean_object* v_nextIdx_588_; lean_object* v_newRawFacts_589_; lean_object* v_facts_590_; lean_object* v_extThms_591_; lean_object* v_ematch_592_; lean_object* v_inj_593_; lean_object* v_split_594_; lean_object* v_sstates_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_618_; 
v_nextDeclIdx_579_ = lean_ctor_get(v_toGoalState_573_, 0);
v_enodeMap_580_ = lean_ctor_get(v_toGoalState_573_, 1);
v_exprs_581_ = lean_ctor_get(v_toGoalState_573_, 2);
v_parents_582_ = lean_ctor_get(v_toGoalState_573_, 3);
v_congrTable_583_ = lean_ctor_get(v_toGoalState_573_, 4);
v_appMap_584_ = lean_ctor_get(v_toGoalState_573_, 5);
v_indicesFound_585_ = lean_ctor_get(v_toGoalState_573_, 6);
v_newFacts_586_ = lean_ctor_get(v_toGoalState_573_, 7);
v_inconsistent_587_ = lean_ctor_get_uint8(v_toGoalState_573_, sizeof(void*)*17);
v_nextIdx_588_ = lean_ctor_get(v_toGoalState_573_, 8);
v_newRawFacts_589_ = lean_ctor_get(v_toGoalState_573_, 9);
v_facts_590_ = lean_ctor_get(v_toGoalState_573_, 10);
v_extThms_591_ = lean_ctor_get(v_toGoalState_573_, 11);
v_ematch_592_ = lean_ctor_get(v_toGoalState_573_, 12);
v_inj_593_ = lean_ctor_get(v_toGoalState_573_, 13);
v_split_594_ = lean_ctor_get(v_toGoalState_573_, 14);
v_sstates_595_ = lean_ctor_get(v_toGoalState_573_, 16);
v_isSharedCheck_618_ = !lean_is_exclusive(v_toGoalState_573_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_toGoalState_573_, 15);
lean_dec(v_unused_619_);
v___x_597_ = v_toGoalState_573_;
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_sstates_595_);
lean_inc(v_split_594_);
lean_inc(v_inj_593_);
lean_inc(v_ematch_592_);
lean_inc(v_extThms_591_);
lean_inc(v_facts_590_);
lean_inc(v_newRawFacts_589_);
lean_inc(v_nextIdx_588_);
lean_inc(v_newFacts_586_);
lean_inc(v_indicesFound_585_);
lean_inc(v_appMap_584_);
lean_inc(v_congrTable_583_);
lean_inc(v_parents_582_);
lean_inc(v_exprs_581_);
lean_inc(v_enodeMap_580_);
lean_inc(v_nextDeclIdx_579_);
lean_dec(v_toGoalState_573_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_used_599_; lean_object* v_next_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_617_; 
v_used_599_ = lean_ctor_get(v_clean_574_, 0);
v_next_600_ = lean_ctor_get(v_clean_574_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_clean_574_);
if (v_isSharedCheck_617_ == 0)
{
v___x_602_ = v_clean_574_;
v_isShared_603_ = v_isSharedCheck_617_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_next_600_);
lean_inc(v_used_599_);
lean_dec(v_clean_574_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_617_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_604_ = lean_box(0);
lean_inc(v_name_570_);
v___x_605_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_599_, v_name_570_, v___x_604_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_next_600_);
v___x_607_ = v_reuseFailAlloc_616_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 15, v___x_607_);
v___x_609_ = v___x_597_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_nextDeclIdx_579_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_enodeMap_580_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_exprs_581_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_parents_582_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_congrTable_583_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_appMap_584_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_indicesFound_585_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_newFacts_586_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_nextIdx_588_);
lean_ctor_set(v_reuseFailAlloc_615_, 9, v_newRawFacts_589_);
lean_ctor_set(v_reuseFailAlloc_615_, 10, v_facts_590_);
lean_ctor_set(v_reuseFailAlloc_615_, 11, v_extThms_591_);
lean_ctor_set(v_reuseFailAlloc_615_, 12, v_ematch_592_);
lean_ctor_set(v_reuseFailAlloc_615_, 13, v_inj_593_);
lean_ctor_set(v_reuseFailAlloc_615_, 14, v_split_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 15, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 16, v_sstates_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*17, v_inconsistent_587_);
v___x_609_ = v_reuseFailAlloc_615_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_609_);
v___x_611_ = v___x_577_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_mvarId_575_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_st_ref_set(v___y_571_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_name_570_);
return v___x_613_;
}
}
}
}
}
}
}
v___jp_622_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_627_);
lean_ctor_set(v___x_636_, 1, v___y_635_);
lean_inc(v___y_629_);
v___x_637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_629_, v___x_636_, v___y_631_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v_toGoalState_640_; lean_object* v_clean_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v_mvarId_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_687_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_st_ref_take(v___y_631_);
v_toGoalState_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_toGoalState_640_);
v_clean_641_ = lean_ctor_get(v_toGoalState_640_, 15);
lean_inc_ref(v_clean_641_);
v_fst_642_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_fst_642_);
v_snd_643_ = lean_ctor_get(v_a_638_, 1);
lean_inc(v_snd_643_);
lean_dec(v_a_638_);
v_mvarId_644_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_688_);
v___x_646_ = v___x_639_;
v_isShared_647_ = v_isSharedCheck_687_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_mvarId_644_);
lean_dec(v___x_639_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_687_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_nextDeclIdx_648_; lean_object* v_enodeMap_649_; lean_object* v_exprs_650_; lean_object* v_parents_651_; lean_object* v_congrTable_652_; lean_object* v_appMap_653_; lean_object* v_indicesFound_654_; lean_object* v_newFacts_655_; uint8_t v_inconsistent_656_; lean_object* v_nextIdx_657_; lean_object* v_newRawFacts_658_; lean_object* v_facts_659_; lean_object* v_extThms_660_; lean_object* v_ematch_661_; lean_object* v_inj_662_; lean_object* v_split_663_; lean_object* v_sstates_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_685_; 
v_nextDeclIdx_648_ = lean_ctor_get(v_toGoalState_640_, 0);
v_enodeMap_649_ = lean_ctor_get(v_toGoalState_640_, 1);
v_exprs_650_ = lean_ctor_get(v_toGoalState_640_, 2);
v_parents_651_ = lean_ctor_get(v_toGoalState_640_, 3);
v_congrTable_652_ = lean_ctor_get(v_toGoalState_640_, 4);
v_appMap_653_ = lean_ctor_get(v_toGoalState_640_, 5);
v_indicesFound_654_ = lean_ctor_get(v_toGoalState_640_, 6);
v_newFacts_655_ = lean_ctor_get(v_toGoalState_640_, 7);
v_inconsistent_656_ = lean_ctor_get_uint8(v_toGoalState_640_, sizeof(void*)*17);
v_nextIdx_657_ = lean_ctor_get(v_toGoalState_640_, 8);
v_newRawFacts_658_ = lean_ctor_get(v_toGoalState_640_, 9);
v_facts_659_ = lean_ctor_get(v_toGoalState_640_, 10);
v_extThms_660_ = lean_ctor_get(v_toGoalState_640_, 11);
v_ematch_661_ = lean_ctor_get(v_toGoalState_640_, 12);
v_inj_662_ = lean_ctor_get(v_toGoalState_640_, 13);
v_split_663_ = lean_ctor_get(v_toGoalState_640_, 14);
v_sstates_664_ = lean_ctor_get(v_toGoalState_640_, 16);
v_isSharedCheck_685_ = !lean_is_exclusive(v_toGoalState_640_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v_toGoalState_640_, 15);
lean_dec(v_unused_686_);
v___x_666_ = v_toGoalState_640_;
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_sstates_664_);
lean_inc(v_split_663_);
lean_inc(v_inj_662_);
lean_inc(v_ematch_661_);
lean_inc(v_extThms_660_);
lean_inc(v_facts_659_);
lean_inc(v_newRawFacts_658_);
lean_inc(v_nextIdx_657_);
lean_inc(v_newFacts_655_);
lean_inc(v_indicesFound_654_);
lean_inc(v_appMap_653_);
lean_inc(v_congrTable_652_);
lean_inc(v_parents_651_);
lean_inc(v_exprs_650_);
lean_inc(v_enodeMap_649_);
lean_inc(v_nextDeclIdx_648_);
lean_dec(v_toGoalState_640_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_used_668_; lean_object* v_next_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_684_; 
v_used_668_ = lean_ctor_get(v_clean_641_, 0);
v_next_669_ = lean_ctor_get(v_clean_641_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_clean_641_);
if (v_isSharedCheck_684_ == 0)
{
v___x_671_ = v_clean_641_;
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_next_669_);
lean_inc(v_used_668_);
lean_dec(v_clean_641_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_669_, v___y_629_, v_snd_643_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_used_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_683_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 15, v___x_675_);
v___x_677_ = v___x_666_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_nextDeclIdx_648_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_enodeMap_649_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_exprs_650_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_parents_651_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_congrTable_652_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_appMap_653_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_indicesFound_654_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_newFacts_655_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_nextIdx_657_);
lean_ctor_set(v_reuseFailAlloc_682_, 9, v_newRawFacts_658_);
lean_ctor_set(v_reuseFailAlloc_682_, 10, v_facts_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 11, v_extThms_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 12, v_ematch_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 13, v_inj_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 14, v_split_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 15, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 16, v_sstates_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*17, v_inconsistent_656_);
v___x_677_ = v_reuseFailAlloc_682_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_677_);
v___x_679_ = v___x_646_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_mvarId_644_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_st_ref_set(v___y_631_, v___x_679_);
v_name_570_ = v_fst_642_;
v___y_571_ = v___y_631_;
goto v___jp_569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_629_);
v_a_689_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_637_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_637_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_709_; lean_object* v_toGoalState_710_; lean_object* v_clean_711_; lean_object* v_used_712_; uint8_t v___x_713_; 
v___x_709_ = lean_st_ref_get(v___y_699_);
v_toGoalState_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_toGoalState_710_);
lean_dec(v___x_709_);
v_clean_711_ = lean_ctor_get(v_toGoalState_710_, 15);
lean_inc_ref(v_clean_711_);
lean_dec_ref(v_toGoalState_710_);
v_used_712_ = lean_ctor_get(v_clean_711_, 0);
lean_inc_ref(v_used_712_);
lean_dec_ref(v_clean_711_);
v___x_713_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_712_, v_name_698_);
lean_dec_ref(v_used_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v_type_557_);
v_name_570_ = v_name_698_;
v___y_571_ = v___y_699_;
goto v___jp_569_;
}
else
{
lean_object* v___x_714_; 
lean_inc(v_name_698_);
v___x_714_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_698_, v_type_557_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v_toGoalState_717_; lean_object* v_clean_718_; lean_object* v_next_719_; lean_object* v___x_720_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_st_ref_get(v___y_699_);
v_toGoalState_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_toGoalState_717_);
lean_dec(v___x_716_);
v_clean_718_ = lean_ctor_get(v_toGoalState_717_, 15);
lean_inc_ref(v_clean_718_);
lean_dec_ref(v_toGoalState_717_);
v_next_719_ = lean_ctor_get(v_clean_718_, 1);
lean_inc_ref(v_next_719_);
lean_dec_ref(v_clean_718_);
v___x_720_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_719_, v_a_715_);
lean_dec_ref(v_next_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_720_, 1);
v___y_623_ = v___y_707_;
v___y_624_ = v___y_702_;
v___y_625_ = v___y_704_;
v___y_626_ = v___y_706_;
v___y_627_ = v_name_698_;
v___y_628_ = v___y_703_;
v___y_629_ = v_a_715_;
v___y_630_ = v___y_708_;
v___y_631_ = v___y_699_;
v___y_632_ = v___y_705_;
v___y_633_ = v___y_700_;
v___y_634_ = v___y_701_;
v___y_635_ = v_val_721_;
goto v___jp_622_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v___x_720_);
v___x_722_ = lean_unsigned_to_nat(1u);
v___y_623_ = v___y_707_;
v___y_624_ = v___y_702_;
v___y_625_ = v___y_704_;
v___y_626_ = v___y_706_;
v___y_627_ = v_name_698_;
v___y_628_ = v___y_703_;
v___y_629_ = v_a_715_;
v___y_630_ = v___y_708_;
v___y_631_ = v___y_699_;
v___y_632_ = v___y_705_;
v___y_633_ = v___y_700_;
v___y_634_ = v___y_701_;
v___y_635_ = v___x_722_;
goto v___jp_622_;
}
}
else
{
lean_dec(v_name_698_);
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_793_, lean_object* v_type_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_793_, v_type_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_a_795_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_808_, v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_816_, v_x_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec_ref(v_x_817_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_821_, lean_object* v_inst_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_821_, v_a_823_, v___y_824_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_836_, lean_object* v_inst_837_, lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_836_, v_inst_837_, v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_855_, v_x_856_, v_x_857_);
lean_dec(v_x_857_);
lean_dec_ref(v_x_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, size_t v_x_861_, size_t v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_860_, v_x_861_, v_x_862_, v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
size_t v_x_40776__boxed_872_; size_t v_x_40777__boxed_873_; lean_object* v_res_874_; 
v_x_40776__boxed_872_ = lean_unbox_usize(v_x_868_);
lean_dec(v_x_868_);
v_x_40777__boxed_873_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_866_, v_x_867_, v_x_40776__boxed_872_, v_x_40777__boxed_873_, v_x_870_, v_x_871_);
return v_res_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, size_t v_x_877_, lean_object* v_x_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_876_, v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_40793__boxed_884_; uint8_t v_res_885_; lean_object* v_r_886_; 
v_x_40793__boxed_884_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_880_, v_x_881_, v_x_40793__boxed_884_, v_x_883_);
lean_dec(v_x_883_);
lean_dec_ref(v_x_881_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, size_t v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
size_t v_x_40804__boxed_896_; lean_object* v_res_897_; 
v_x_40804__boxed_896_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_res_897_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_892_, v_x_893_, v_x_40804__boxed_896_, v_x_895_);
lean_dec(v_x_895_);
lean_dec_ref(v_x_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_898_, lean_object* v_n_899_, lean_object* v_k_900_, lean_object* v_v_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_899_, v_k_900_, v_v_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_903_, size_t v_depth_904_, lean_object* v_keys_905_, lean_object* v_vals_906_, lean_object* v_heq_907_, lean_object* v_i_908_, lean_object* v_entries_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_904_, v_keys_905_, v_vals_906_, v_i_908_, v_entries_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_911_, lean_object* v_depth_912_, lean_object* v_keys_913_, lean_object* v_vals_914_, lean_object* v_heq_915_, lean_object* v_i_916_, lean_object* v_entries_917_){
_start:
{
size_t v_depth_boxed_918_; lean_object* v_res_919_; 
v_depth_boxed_918_ = lean_unbox_usize(v_depth_912_);
lean_dec(v_depth_912_);
v_res_919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_911_, v_depth_boxed_918_, v_keys_913_, v_vals_914_, v_heq_915_, v_i_916_, v_entries_917_);
lean_dec_ref(v_vals_914_);
lean_dec_ref(v_keys_913_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_920_, lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_heq_923_, lean_object* v_i_924_, lean_object* v_k_925_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_921_, v_i_924_, v_k_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_927_, lean_object* v_keys_928_, lean_object* v_vals_929_, lean_object* v_heq_930_, lean_object* v_i_931_, lean_object* v_k_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_927_, v_keys_928_, v_vals_929_, v_heq_930_, v_i_931_, v_k_932_);
lean_dec(v_k_932_);
lean_dec_ref(v_vals_929_);
lean_dec_ref(v_keys_928_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_935_, lean_object* v_keys_936_, lean_object* v_vals_937_, lean_object* v_heq_938_, lean_object* v_i_939_, lean_object* v_k_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_936_, v_vals_937_, v_i_939_, v_k_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_heq_945_, lean_object* v_i_946_, lean_object* v_k_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_942_, v_keys_943_, v_vals_944_, v_heq_945_, v_i_946_, v_k_947_);
lean_dec(v_k_947_);
lean_dec_ref(v_vals_944_);
lean_dec_ref(v_keys_943_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_950_, v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_env_962_; lean_object* v___x_963_; lean_object* v_mctx_964_; lean_object* v_lctx_965_; lean_object* v_options_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_961_ = lean_st_ref_get(v___y_959_);
v_env_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_961_);
v___x_963_ = lean_st_ref_get(v___y_957_);
v_mctx_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_mctx_964_);
lean_dec(v___x_963_);
v_lctx_965_ = lean_ctor_get(v___y_956_, 2);
v_options_966_ = lean_ctor_get(v___y_958_, 2);
lean_inc_ref(v_options_966_);
lean_inc_ref(v_lctx_965_);
v___x_967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_967_, 0, v_env_962_);
lean_ctor_set(v___x_967_, 1, v_mctx_964_);
lean_ctor_set(v___x_967_, 2, v_lctx_965_);
lean_ctor_set(v___x_967_, 3, v_options_966_);
v___x_968_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_msgData_955_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_ref_983_; lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_ref_983_ = lean_ctor_get(v___y_980_, 5);
v___x_984_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
lean_inc(v_ref_983_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_ref_983_);
lean_ctor_set(v___x_989_, 1, v_a_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___x_1070_; lean_object* v_mvarId_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_st_ref_get(v_a_1004_);
v_mvarId_1071_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_mvarId_1071_);
lean_dec(v___x_1070_);
v___x_1072_ = l_Lean_MVarId_getType(v_mvarId_1071_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
switch(lean_obj_tag(v_a_1073_))
{
case 7:
{
lean_object* v_binderName_1074_; lean_object* v_binderType_1075_; 
v_binderName_1074_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_binderName_1074_);
v_binderType_1075_ = lean_ctor_get(v_a_1073_, 1);
lean_inc_ref(v_binderType_1075_);
lean_dec_ref_known(v_a_1073_, 3);
v_fst_1016_ = v_binderName_1074_;
v_snd_1017_ = v_binderType_1075_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
goto v___jp_1015_;
}
case 8:
{
lean_object* v_declName_1076_; lean_object* v_type_1077_; 
v_declName_1076_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_declName_1076_);
v_type_1077_ = lean_ctor_get(v_a_1073_, 1);
lean_inc_ref(v_type_1077_);
lean_dec_ref_known(v_a_1073_, 4);
v_fst_1016_ = v_declName_1076_;
v_snd_1017_ = v_type_1077_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
goto v___jp_1015_;
}
default: 
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1073_);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1079_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1078_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1072_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1072_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_1015_:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1016_, v_snd_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v_mvarId_1031_; lean_object* v___x_1032_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_st_ref_get(v___y_1018_);
v_mvarId_1031_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_mvarId_1031_);
lean_dec(v___x_1030_);
v___x_1032_ = l_Lean_MVarId_intro(v_mvarId_1031_, v_a_1029_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1053_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1053_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1039_; lean_object* v_toGoalState_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1051_; 
v_fst_1037_ = lean_ctor_get(v_a_1033_, 0);
lean_inc(v_fst_1037_);
v_snd_1038_ = lean_ctor_get(v_a_1033_, 1);
lean_inc(v_snd_1038_);
lean_dec(v_a_1033_);
v___x_1039_ = lean_st_ref_take(v___y_1018_);
v_toGoalState_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1039_, 1);
lean_dec(v_unused_1052_);
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_toGoalState_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v_snd_1038_);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_toGoalState_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_snd_1038_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_st_ref_set(v___y_1018_, v___x_1045_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_fst_1037_);
v___x_1048_ = v___x_1035_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_fst_1037_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1032_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1032_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1028_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1028_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1109_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1122_, lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1122_, v_msg_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec(v___y_1124_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc(v___y_1137_);
v___x_1148_ = lean_apply_11(v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, lean_box(0));
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___f_1175_; lean_object* v___x_1176_; 
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc(v___y_1164_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1175_, 0, v_x_1163_);
lean_closure_set(v___f_1175_, 1, v___y_1164_);
lean_closure_set(v___f_1175_, 2, v___y_1165_);
lean_closure_set(v___f_1175_, 3, v___y_1166_);
lean_closure_set(v___f_1175_, 4, v___y_1167_);
lean_closure_set(v___f_1175_, 5, v___y_1168_);
lean_closure_set(v___f_1175_, 6, v___y_1169_);
v___x_1176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1162_, v___f_1175_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
return v___x_1176_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1185_, v_x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1199_, lean_object* v_mvarId_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1200_, v_x_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_mvarId_1215_, lean_object* v_x_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1214_, v_mvarId_1215_, v_x_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec(v___y_1217_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
v___x_1240_ = lean_apply_10(v_x_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, lean_box(0));
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1253_, lean_object* v_x_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___f_1265_; lean_object* v___x_1266_; 
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
lean_inc(v___y_1255_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1265_, 0, v_x_1254_);
lean_closure_set(v___f_1265_, 1, v___y_1255_);
lean_closure_set(v___f_1265_, 2, v___y_1256_);
lean_closure_set(v___f_1265_, 3, v___y_1257_);
lean_closure_set(v___f_1265_, 4, v___y_1258_);
lean_closure_set(v___f_1265_, 5, v___y_1259_);
v___x_1266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1253_, v___f_1265_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
return v___x_1266_;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1275_, v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1288_, lean_object* v_mvarId_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1289_, v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_mvarId_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1302_, v_mvarId_1303_, v_x_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1316_, lean_object* v_generation_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
lean_inc(v_a_1316_);
v___x_1329_ = l_Lean_FVarId_getDecl___redArg(v_a_1316_, v___y_1324_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = l_Lean_LocalDecl_type(v_a_1330_);
lean_dec(v_a_1330_);
lean_inc_ref(v___x_1331_);
v___x_1332_ = l_Lean_Meta_isProp(v___x_1331_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; uint8_t v___x_1334_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = lean_unbox(v_a_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec_ref(v___x_1331_);
lean_inc(v_a_1316_);
v___x_1335_ = l_Lean_FVarId_getDecl___redArg(v_a_1316_, v___y_1324_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_unbox(v_a_1333_);
lean_dec(v_a_1333_);
v___x_1338_ = l_Lean_LocalDecl_value(v_a_1336_, v___x_1337_);
lean_dec(v_a_1336_);
v___x_1339_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1338_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
lean_inc(v_a_1316_);
v___x_1341_ = l_Lean_mkFVar(v_a_1316_);
v___x_1342_ = l_Lean_Meta_Sym_shareCommon(v___x_1341_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
lean_inc(v_a_1340_);
v___x_1344_ = l_Lean_Meta_Simp_Result_getProof(v_a_1340_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_expr_1346_; lean_object* v___x_1347_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v_expr_1346_ = lean_ctor_get(v_a_1340_, 0);
lean_inc_ref(v_expr_1346_);
lean_dec(v_a_1340_);
v___x_1347_ = l_Lean_Meta_Grind_addNewEq(v_a_1343_, v_expr_1346_, v_a_1345_, v_generation_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1356_; 
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v___x_1347_, 0);
lean_dec(v_unused_1357_);
v___x_1349_ = v___x_1347_;
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
else
{
lean_dec(v___x_1347_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_st_ref_get(v___y_1318_);
v___x_1352_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1316_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_a_1316_);
v_a_1358_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1347_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1347_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1343_);
lean_dec(v_a_1340_);
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1366_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1344_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1344_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1340_);
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1374_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1342_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1342_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1382_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1339_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1339_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1333_);
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1390_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1335_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1335_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v_a_1333_);
lean_dec(v_generation_1317_);
v___x_1398_ = lean_st_ref_get(v___y_1318_);
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1331_);
v___x_1400_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1399_, v___x_1331_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_mvarId_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v_mvarId_1402_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_mvarId_1402_);
lean_dec(v___x_1398_);
v___x_1403_ = l_Lean_mkFVar(v_a_1316_);
v___x_1404_ = l_Lean_MVarId_assert(v_mvarId_1402_, v_a_1401_, v___x_1331_, v___x_1403_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1423_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1423_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1423_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v_toGoalState_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
v___x_1409_ = lean_st_ref_get(v___y_1318_);
v_toGoalState_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1409_, 1);
lean_dec(v_unused_1422_);
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_toGoalState_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_a_1405_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_toGoalState_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_a_1405_);
v___x_1415_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1416_);
v___x_1418_ = v___x_1407_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
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
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1424_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1404_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1404_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v___x_1398_);
lean_dec_ref(v___x_1331_);
lean_dec(v_a_1316_);
v_a_1432_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1400_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1400_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1331_);
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1440_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1332_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1332_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
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
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_generation_1317_);
lean_dec(v_a_1316_);
v_a_1448_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1329_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1329_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1456_, lean_object* v_generation_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1456_, v_generation_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v_ks_1474_; lean_object* v_vs_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1499_; 
v_ks_1474_ = lean_ctor_get(v_x_1470_, 0);
v_vs_1475_ = lean_ctor_get(v_x_1470_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1470_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1477_ = v_x_1470_;
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_vs_1475_);
lean_inc(v_ks_1474_);
lean_dec(v_x_1470_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1499_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_array_get_size(v_ks_1474_);
v___x_1480_ = lean_nat_dec_lt(v_x_1471_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_dec(v_x_1471_);
v___x_1481_ = lean_array_push(v_ks_1474_, v_x_1472_);
v___x_1482_ = lean_array_push(v_vs_1475_, v_x_1473_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1482_);
lean_ctor_set(v___x_1477_, 0, v___x_1481_);
v___x_1484_ = v___x_1477_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
else
{
lean_object* v_k_x27_1486_; uint8_t v___x_1487_; 
v_k_x27_1486_ = lean_array_fget_borrowed(v_ks_1474_, v_x_1471_);
v___x_1487_ = l_Lean_instBEqMVarId_beq(v_x_1472_, v_k_x27_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1489_; 
if (v_isShared_1478_ == 0)
{
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_ks_1474_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_vs_1475_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_x_1471_, v___x_1490_);
lean_dec(v_x_1471_);
v_x_1470_ = v___x_1489_;
v_x_1471_ = v___x_1491_;
goto _start;
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1494_ = lean_array_fset(v_ks_1474_, v_x_1471_, v_x_1472_);
v___x_1495_ = lean_array_fset(v_vs_1475_, v_x_1471_, v_x_1473_);
lean_dec(v_x_1471_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1495_);
lean_ctor_set(v___x_1477_, 0, v___x_1494_);
v___x_1497_ = v___x_1477_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1500_, lean_object* v_k_1501_, lean_object* v_v_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1500_, v___x_1503_, v_k_1501_, v_v_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1505_, size_t v_x_1506_, size_t v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v_es_1510_; size_t v___x_1511_; size_t v___x_1512_; lean_object* v_j_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_es_1510_ = lean_ctor_get(v_x_1505_, 0);
v___x_1511_ = ((size_t)31ULL);
v___x_1512_ = lean_usize_land(v_x_1506_, v___x_1511_);
v_j_1513_ = lean_usize_to_nat(v___x_1512_);
v___x_1514_ = lean_array_get_size(v_es_1510_);
v___x_1515_ = lean_nat_dec_lt(v_j_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_dec(v_j_1513_);
lean_dec(v_x_1509_);
lean_dec(v_x_1508_);
return v_x_1505_;
}
else
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1554_; 
lean_inc_ref(v_es_1510_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_x_1505_, 0);
lean_dec(v_unused_1555_);
v___x_1517_ = v_x_1505_;
v_isShared_1518_ = v_isSharedCheck_1554_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v_x_1505_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1554_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_v_1519_; lean_object* v___x_1520_; lean_object* v_xs_x27_1521_; lean_object* v___y_1523_; 
v_v_1519_ = lean_array_fget(v_es_1510_, v_j_1513_);
v___x_1520_ = lean_box(0);
v_xs_x27_1521_ = lean_array_fset(v_es_1510_, v_j_1513_, v___x_1520_);
switch(lean_obj_tag(v_v_1519_))
{
case 0:
{
lean_object* v_key_1528_; lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1539_; 
v_key_1528_ = lean_ctor_get(v_v_1519_, 0);
v_val_1529_ = lean_ctor_get(v_v_1519_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_v_1519_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1531_ = v_v_1519_;
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_inc(v_key_1528_);
lean_dec(v_v_1519_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
uint8_t v___x_1533_; 
v___x_1533_ = l_Lean_instBEqMVarId_beq(v_x_1508_, v_key_1528_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_del_object(v___x_1531_);
v___x_1534_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1528_, v_val_1529_, v_x_1508_, v_x_1509_);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___y_1523_ = v___x_1535_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_val_1529_);
lean_dec(v_key_1528_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v_x_1509_);
lean_ctor_set(v___x_1531_, 0, v_x_1508_);
v___x_1537_ = v___x_1531_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_x_1508_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_x_1509_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v___y_1523_ = v___x_1537_;
goto v___jp_1522_;
}
}
}
}
case 1:
{
lean_object* v_node_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1552_; 
v_node_1540_ = lean_ctor_get(v_v_1519_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_v_1519_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1542_ = v_v_1519_;
v_isShared_1543_ = v_isSharedCheck_1552_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_node_1540_);
lean_dec(v_v_1519_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1552_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1544_ = ((size_t)5ULL);
v___x_1545_ = lean_usize_shift_right(v_x_1506_, v___x_1544_);
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_x_1507_, v___x_1546_);
v___x_1548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1540_, v___x_1545_, v___x_1547_, v_x_1508_, v_x_1509_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1548_);
v___x_1550_ = v___x_1542_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
v___y_1523_ = v___x_1550_;
goto v___jp_1522_;
}
}
}
default: 
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_x_1508_);
lean_ctor_set(v___x_1553_, 1, v_x_1509_);
v___y_1523_ = v___x_1553_;
goto v___jp_1522_;
}
}
v___jp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_array_fset(v_xs_x27_1521_, v_j_1513_, v___y_1523_);
lean_dec(v_j_1513_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1524_);
v___x_1526_ = v___x_1517_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v_ks_1556_; lean_object* v_vs_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1577_; 
v_ks_1556_ = lean_ctor_get(v_x_1505_, 0);
v_vs_1557_ = lean_ctor_get(v_x_1505_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1559_ = v_x_1505_;
v_isShared_1560_ = v_isSharedCheck_1577_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_vs_1557_);
lean_inc(v_ks_1556_);
lean_dec(v_x_1505_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1577_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_ks_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_vs_1557_);
v___x_1562_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v_newNode_1563_; uint8_t v___y_1565_; size_t v___x_1571_; uint8_t v___x_1572_; 
v_newNode_1563_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1562_, v_x_1508_, v_x_1509_);
v___x_1571_ = ((size_t)7ULL);
v___x_1572_ = lean_usize_dec_le(v___x_1571_, v_x_1507_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1573_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1563_);
v___x_1574_ = lean_unsigned_to_nat(4u);
v___x_1575_ = lean_nat_dec_lt(v___x_1573_, v___x_1574_);
lean_dec(v___x_1573_);
v___y_1565_ = v___x_1575_;
goto v___jp_1564_;
}
else
{
v___y_1565_ = v___x_1572_;
goto v___jp_1564_;
}
v___jp_1564_:
{
if (v___y_1565_ == 0)
{
lean_object* v_ks_1566_; lean_object* v_vs_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_ks_1566_ = lean_ctor_get(v_newNode_1563_, 0);
lean_inc_ref(v_ks_1566_);
v_vs_1567_ = lean_ctor_get(v_newNode_1563_, 1);
lean_inc_ref(v_vs_1567_);
lean_dec_ref(v_newNode_1563_);
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1507_, v_ks_1566_, v_vs_1567_, v___x_1568_, v___x_1569_);
lean_dec_ref(v_vs_1567_);
lean_dec_ref(v_ks_1566_);
return v___x_1570_;
}
else
{
return v_newNode_1563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1578_, lean_object* v_keys_1579_, lean_object* v_vals_1580_, lean_object* v_i_1581_, lean_object* v_entries_1582_){
_start:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_array_get_size(v_keys_1579_);
v___x_1584_ = lean_nat_dec_lt(v_i_1581_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_dec(v_i_1581_);
return v_entries_1582_;
}
else
{
lean_object* v_k_1585_; lean_object* v_v_1586_; uint64_t v___x_1587_; size_t v_h_1588_; size_t v___x_1589_; lean_object* v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; size_t v_h_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_k_1585_ = lean_array_fget_borrowed(v_keys_1579_, v_i_1581_);
v_v_1586_ = lean_array_fget_borrowed(v_vals_1580_, v_i_1581_);
v___x_1587_ = l_Lean_instHashableMVarId_hash(v_k_1585_);
v_h_1588_ = lean_uint64_to_usize(v___x_1587_);
v___x_1589_ = ((size_t)5ULL);
v___x_1590_ = lean_unsigned_to_nat(1u);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_sub(v_depth_1578_, v___x_1591_);
v___x_1593_ = lean_usize_mul(v___x_1589_, v___x_1592_);
v_h_1594_ = lean_usize_shift_right(v_h_1588_, v___x_1593_);
v___x_1595_ = lean_nat_add(v_i_1581_, v___x_1590_);
lean_dec(v_i_1581_);
lean_inc(v_v_1586_);
lean_inc(v_k_1585_);
v___x_1596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1582_, v_h_1594_, v_depth_1578_, v_k_1585_, v_v_1586_);
v_i_1581_ = v___x_1595_;
v_entries_1582_ = v___x_1596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1598_, lean_object* v_keys_1599_, lean_object* v_vals_1600_, lean_object* v_i_1601_, lean_object* v_entries_1602_){
_start:
{
size_t v_depth_boxed_1603_; lean_object* v_res_1604_; 
v_depth_boxed_1603_ = lean_unbox_usize(v_depth_1598_);
lean_dec(v_depth_1598_);
v_res_1604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1603_, v_keys_1599_, v_vals_1600_, v_i_1601_, v_entries_1602_);
lean_dec_ref(v_vals_1600_);
lean_dec_ref(v_keys_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
size_t v_x_195395__boxed_1610_; size_t v_x_195396__boxed_1611_; lean_object* v_res_1612_; 
v_x_195395__boxed_1610_ = lean_unbox_usize(v_x_1606_);
lean_dec(v_x_1606_);
v_x_195396__boxed_1611_ = lean_unbox_usize(v_x_1607_);
lean_dec(v_x_1607_);
v_res_1612_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1605_, v_x_195395__boxed_1610_, v_x_195396__boxed_1611_, v_x_1608_, v_x_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint64_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1616_ = l_Lean_instHashableMVarId_hash(v_x_1614_);
v___x_1617_ = lean_uint64_to_usize(v___x_1616_);
v___x_1618_ = ((size_t)1ULL);
v___x_1619_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1613_, v___x_1617_, v___x_1618_, v_x_1614_, v_x_1615_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1620_, lean_object* v_val_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v_mctx_1625_; lean_object* v_cache_1626_; lean_object* v_zetaDeltaFVarIds_1627_; lean_object* v_postponed_1628_; lean_object* v_diag_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1657_; 
v___x_1624_ = lean_st_ref_take(v___y_1622_);
v_mctx_1625_ = lean_ctor_get(v___x_1624_, 0);
v_cache_1626_ = lean_ctor_get(v___x_1624_, 1);
v_zetaDeltaFVarIds_1627_ = lean_ctor_get(v___x_1624_, 2);
v_postponed_1628_ = lean_ctor_get(v___x_1624_, 3);
v_diag_1629_ = lean_ctor_get(v___x_1624_, 4);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1631_ = v___x_1624_;
v_isShared_1632_ = v_isSharedCheck_1657_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_diag_1629_);
lean_inc(v_postponed_1628_);
lean_inc(v_zetaDeltaFVarIds_1627_);
lean_inc(v_cache_1626_);
lean_inc(v_mctx_1625_);
lean_dec(v___x_1624_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1657_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_depth_1633_; lean_object* v_levelAssignDepth_1634_; lean_object* v_lmvarCounter_1635_; lean_object* v_mvarCounter_1636_; lean_object* v_lDecls_1637_; lean_object* v_decls_1638_; lean_object* v_userNames_1639_; lean_object* v_lAssignment_1640_; lean_object* v_eAssignment_1641_; lean_object* v_dAssignment_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1656_; 
v_depth_1633_ = lean_ctor_get(v_mctx_1625_, 0);
v_levelAssignDepth_1634_ = lean_ctor_get(v_mctx_1625_, 1);
v_lmvarCounter_1635_ = lean_ctor_get(v_mctx_1625_, 2);
v_mvarCounter_1636_ = lean_ctor_get(v_mctx_1625_, 3);
v_lDecls_1637_ = lean_ctor_get(v_mctx_1625_, 4);
v_decls_1638_ = lean_ctor_get(v_mctx_1625_, 5);
v_userNames_1639_ = lean_ctor_get(v_mctx_1625_, 6);
v_lAssignment_1640_ = lean_ctor_get(v_mctx_1625_, 7);
v_eAssignment_1641_ = lean_ctor_get(v_mctx_1625_, 8);
v_dAssignment_1642_ = lean_ctor_get(v_mctx_1625_, 9);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_mctx_1625_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1644_ = v_mctx_1625_;
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_dAssignment_1642_);
lean_inc(v_eAssignment_1641_);
lean_inc(v_lAssignment_1640_);
lean_inc(v_userNames_1639_);
lean_inc(v_decls_1638_);
lean_inc(v_lDecls_1637_);
lean_inc(v_mvarCounter_1636_);
lean_inc(v_lmvarCounter_1635_);
lean_inc(v_levelAssignDepth_1634_);
lean_inc(v_depth_1633_);
lean_dec(v_mctx_1625_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1641_, v_mvarId_1620_, v_val_1621_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 8, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_depth_1633_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_levelAssignDepth_1634_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_lmvarCounter_1635_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_mvarCounter_1636_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_lDecls_1637_);
lean_ctor_set(v_reuseFailAlloc_1655_, 5, v_decls_1638_);
lean_ctor_set(v_reuseFailAlloc_1655_, 6, v_userNames_1639_);
lean_ctor_set(v_reuseFailAlloc_1655_, 7, v_lAssignment_1640_);
lean_ctor_set(v_reuseFailAlloc_1655_, 8, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1655_, 9, v_dAssignment_1642_);
v___x_1648_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1648_);
v___x_1650_ = v___x_1631_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_cache_1626_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_zetaDeltaFVarIds_1627_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_postponed_1628_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_diag_1629_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_st_ref_set(v___y_1622_, v___x_1650_);
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1658_, lean_object* v_val_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1658_, v_val_1659_, v___y_1660_);
lean_dec(v___y_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v_ngen_1666_; lean_object* v_namePrefix_1667_; lean_object* v_idx_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1697_; 
v___x_1665_ = lean_st_ref_get(v___y_1663_);
v_ngen_1666_ = lean_ctor_get(v___x_1665_, 2);
lean_inc_ref(v_ngen_1666_);
lean_dec(v___x_1665_);
v_namePrefix_1667_ = lean_ctor_get(v_ngen_1666_, 0);
v_idx_1668_ = lean_ctor_get(v_ngen_1666_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_ngen_1666_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1670_ = v_ngen_1666_;
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_idx_1668_);
lean_inc(v_namePrefix_1667_);
lean_dec(v_ngen_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_auxDeclNGen_1675_; lean_object* v_traceState_1676_; lean_object* v_cache_1677_; lean_object* v_messages_1678_; lean_object* v_infoState_1679_; lean_object* v_snapshotTasks_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1695_; 
v___x_1672_ = lean_st_ref_take(v___y_1663_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1672_, 1);
v_auxDeclNGen_1675_ = lean_ctor_get(v___x_1672_, 3);
v_traceState_1676_ = lean_ctor_get(v___x_1672_, 4);
v_cache_1677_ = lean_ctor_get(v___x_1672_, 5);
v_messages_1678_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1679_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1680_ = lean_ctor_get(v___x_1672_, 8);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1672_, 2);
lean_dec(v_unused_1696_);
v___x_1682_ = v___x_1672_;
v_isShared_1683_ = v_isSharedCheck_1695_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_snapshotTasks_1680_);
lean_inc(v_infoState_1679_);
lean_inc(v_messages_1678_);
lean_inc(v_cache_1677_);
lean_inc(v_traceState_1676_);
lean_inc(v_auxDeclNGen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1672_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1695_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_r_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_inc(v_idx_1668_);
lean_inc(v_namePrefix_1667_);
v_r_1684_ = l_Lean_Name_num___override(v_namePrefix_1667_, v_idx_1668_);
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v_idx_1668_, v___x_1685_);
lean_dec(v_idx_1668_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1686_);
v___x_1688_ = v___x_1670_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_namePrefix_1667_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 2, v___x_1688_);
v___x_1690_ = v___x_1682_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_env_1673_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_auxDeclNGen_1675_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_traceState_1676_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_cache_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_messages_1678_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_infoState_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_snapshotTasks_1680_);
v___x_1690_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_st_ref_set(v___y_1663_, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_r_1684_);
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1698_);
lean_dec(v___y_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v___x_1712_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1710_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
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
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1721_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1738_, lean_object* v_a_1739_, uint8_t v___y_1740_, uint8_t v___x_1741_, uint8_t v___x_1742_, lean_object* v_a_1743_, lean_object* v___x_1744_, lean_object* v_expr_1745_, lean_object* v___x_1746_, lean_object* v_val_1747_, lean_object* v_mvarId_1748_, lean_object* v___x_1749_, lean_object* v_a_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_mkLambdaFVars(v___x_1738_, v_a_1739_, v___y_1740_, v___x_1741_, v___y_1740_, v___x_1741_, v___x_1742_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1743_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_mkConst(v___x_1764_, v___x_1766_);
v___x_1768_ = lean_unsigned_to_nat(5u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
v___x_1770_ = lean_array_push(v___x_1769_, v___x_1744_);
v___x_1771_ = lean_array_push(v___x_1770_, v_expr_1745_);
v___x_1772_ = lean_array_push(v___x_1771_, v___x_1746_);
v___x_1773_ = lean_array_push(v___x_1772_, v_val_1747_);
v___x_1774_ = lean_array_push(v___x_1773_, v_a_1763_);
v___x_1775_ = l_Lean_mkAppN(v___x_1767_, v___x_1774_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1748_, v___x_1775_, v___y_1758_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1794_; 
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1795_);
v___x_1778_ = v___x_1776_;
v_isShared_1779_ = v_isSharedCheck_1794_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v___x_1776_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1794_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v_toGoalState_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1792_; 
v___x_1780_ = lean_st_ref_get(v___y_1751_);
v_toGoalState_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v___x_1780_, 1);
lean_dec(v_unused_1793_);
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_toGoalState_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v___x_1749_);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_toGoalState_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1749_);
v___x_1786_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1750_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1787_);
v___x_1789_ = v___x_1778_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_a_1750_);
lean_dec(v___x_1749_);
v_a_1796_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1776_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1776_);
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
lean_dec(v_a_1750_);
lean_dec(v___x_1749_);
lean_dec(v_mvarId_1748_);
lean_dec_ref(v_val_1747_);
lean_dec_ref(v___x_1746_);
lean_dec_ref(v_expr_1745_);
lean_dec_ref(v___x_1744_);
lean_dec(v_a_1743_);
v_a_1804_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1762_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1762_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1812_ = _args[0];
lean_object* v_a_1813_ = _args[1];
lean_object* v___y_1814_ = _args[2];
lean_object* v___x_1815_ = _args[3];
lean_object* v___x_1816_ = _args[4];
lean_object* v_a_1817_ = _args[5];
lean_object* v___x_1818_ = _args[6];
lean_object* v_expr_1819_ = _args[7];
lean_object* v___x_1820_ = _args[8];
lean_object* v_val_1821_ = _args[9];
lean_object* v_mvarId_1822_ = _args[10];
lean_object* v___x_1823_ = _args[11];
lean_object* v_a_1824_ = _args[12];
lean_object* v___y_1825_ = _args[13];
lean_object* v___y_1826_ = _args[14];
lean_object* v___y_1827_ = _args[15];
lean_object* v___y_1828_ = _args[16];
lean_object* v___y_1829_ = _args[17];
lean_object* v___y_1830_ = _args[18];
lean_object* v___y_1831_ = _args[19];
lean_object* v___y_1832_ = _args[20];
lean_object* v___y_1833_ = _args[21];
lean_object* v___y_1834_ = _args[22];
lean_object* v___y_1835_ = _args[23];
_start:
{
uint8_t v___y_195721__boxed_1836_; uint8_t v___x_195722__boxed_1837_; uint8_t v___x_195723__boxed_1838_; lean_object* v_res_1839_; 
v___y_195721__boxed_1836_ = lean_unbox(v___y_1814_);
v___x_195722__boxed_1837_ = lean_unbox(v___x_1815_);
v___x_195723__boxed_1838_ = lean_unbox(v___x_1816_);
v_res_1839_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1812_, v_a_1813_, v___y_195721__boxed_1836_, v___x_195722__boxed_1837_, v___x_195723__boxed_1838_, v_a_1817_, v___x_1818_, v_expr_1819_, v___x_1820_, v_val_1821_, v_mvarId_1822_, v___x_1823_, v_a_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___x_1812_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1845_, lean_object* v_a_1846_, uint8_t v___x_1847_, uint8_t v___x_1848_, uint8_t v___x_1849_, lean_object* v_a_1850_, lean_object* v___x_1851_, lean_object* v___x_1852_, lean_object* v_expr_1853_, lean_object* v___x_1854_, lean_object* v_val_1855_, lean_object* v_mvarId_1856_, lean_object* v___x_1857_, lean_object* v_a_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_mkLambdaFVars(v___x_1845_, v_a_1846_, v___x_1847_, v___x_1848_, v___x_1847_, v___x_1848_, v___x_1849_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1850_);
lean_ctor_set(v___x_1873_, 1, v___x_1851_);
v___x_1874_ = l_Lean_mkConst(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_unsigned_to_nat(5u);
v___x_1876_ = lean_mk_empty_array_with_capacity(v___x_1875_);
v___x_1877_ = lean_array_push(v___x_1876_, v___x_1852_);
v___x_1878_ = lean_array_push(v___x_1877_, v_expr_1853_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1854_);
v___x_1880_ = lean_array_push(v___x_1879_, v_val_1855_);
v___x_1881_ = lean_array_push(v___x_1880_, v_a_1871_);
v___x_1882_ = l_Lean_mkAppN(v___x_1874_, v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1856_, v___x_1882_, v___y_1866_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1901_; 
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v___x_1883_, 0);
lean_dec(v_unused_1902_);
v___x_1885_ = v___x_1883_;
v_isShared_1886_ = v_isSharedCheck_1901_;
goto v_resetjp_1884_;
}
else
{
lean_dec(v___x_1883_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1901_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v_toGoalState_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1899_; 
v___x_1887_ = lean_st_ref_get(v___y_1859_);
v_toGoalState_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1887_, 1);
lean_dec(v_unused_1900_);
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1899_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_toGoalState_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1899_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1857_);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_toGoalState_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1857_);
v___x_1893_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1858_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1894_);
v___x_1896_ = v___x_1885_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1858_);
lean_dec(v___x_1857_);
v_a_1903_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1883_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1883_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1858_);
lean_dec(v___x_1857_);
lean_dec(v_mvarId_1856_);
lean_dec_ref(v_val_1855_);
lean_dec_ref(v___x_1854_);
lean_dec_ref(v_expr_1853_);
lean_dec_ref(v___x_1852_);
lean_dec(v___x_1851_);
lean_dec(v_a_1850_);
v_a_1911_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1870_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1870_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1919_ = _args[0];
lean_object* v_a_1920_ = _args[1];
lean_object* v___x_1921_ = _args[2];
lean_object* v___x_1922_ = _args[3];
lean_object* v___x_1923_ = _args[4];
lean_object* v_a_1924_ = _args[5];
lean_object* v___x_1925_ = _args[6];
lean_object* v___x_1926_ = _args[7];
lean_object* v_expr_1927_ = _args[8];
lean_object* v___x_1928_ = _args[9];
lean_object* v_val_1929_ = _args[10];
lean_object* v_mvarId_1930_ = _args[11];
lean_object* v___x_1931_ = _args[12];
lean_object* v_a_1932_ = _args[13];
lean_object* v___y_1933_ = _args[14];
lean_object* v___y_1934_ = _args[15];
lean_object* v___y_1935_ = _args[16];
lean_object* v___y_1936_ = _args[17];
lean_object* v___y_1937_ = _args[18];
lean_object* v___y_1938_ = _args[19];
lean_object* v___y_1939_ = _args[20];
lean_object* v___y_1940_ = _args[21];
lean_object* v___y_1941_ = _args[22];
lean_object* v___y_1942_ = _args[23];
lean_object* v___y_1943_ = _args[24];
_start:
{
uint8_t v___x_195903__boxed_1944_; uint8_t v___x_195904__boxed_1945_; uint8_t v___x_195905__boxed_1946_; lean_object* v_res_1947_; 
v___x_195903__boxed_1944_ = lean_unbox(v___x_1921_);
v___x_195904__boxed_1945_ = lean_unbox(v___x_1922_);
v___x_195905__boxed_1946_ = lean_unbox(v___x_1923_);
v_res_1947_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1919_, v_a_1920_, v___x_195903__boxed_1944_, v___x_195904__boxed_1945_, v___x_195905__boxed_1946_, v_a_1924_, v___x_1925_, v___x_1926_, v_expr_1927_, v___x_1928_, v_val_1929_, v_mvarId_1930_, v___x_1931_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___x_1919_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1948_, lean_object* v_a_1949_, uint8_t v___y_1950_, uint8_t v___x_1951_, uint8_t v___x_1952_, lean_object* v_mvarId_1953_, lean_object* v___x_1954_, lean_object* v_a_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Meta_mkLambdaFVars(v___x_1948_, v_a_1949_, v___y_1950_, v___x_1951_, v___y_1950_, v___x_1951_, v___x_1952_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1953_, v_a_1968_, v___y_1963_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1987_; 
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1988_);
v___x_1971_ = v___x_1969_;
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v___x_1969_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1987_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v_toGoalState_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1985_; 
v___x_1973_ = lean_st_ref_get(v___y_1956_);
v_toGoalState_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1973_, 1);
lean_dec(v_unused_1986_);
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1985_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_toGoalState_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1985_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1954_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_toGoalState_1974_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___x_1954_);
v___x_1979_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1955_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1980_);
v___x_1982_ = v___x_1971_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1955_);
lean_dec(v___x_1954_);
v_a_1989_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1969_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1969_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_a_1955_);
lean_dec(v___x_1954_);
lean_dec(v_mvarId_1953_);
v_a_1997_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1967_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1967_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2005_ = _args[0];
lean_object* v_a_2006_ = _args[1];
lean_object* v___y_2007_ = _args[2];
lean_object* v___x_2008_ = _args[3];
lean_object* v___x_2009_ = _args[4];
lean_object* v_mvarId_2010_ = _args[5];
lean_object* v___x_2011_ = _args[6];
lean_object* v_a_2012_ = _args[7];
lean_object* v___y_2013_ = _args[8];
lean_object* v___y_2014_ = _args[9];
lean_object* v___y_2015_ = _args[10];
lean_object* v___y_2016_ = _args[11];
lean_object* v___y_2017_ = _args[12];
lean_object* v___y_2018_ = _args[13];
lean_object* v___y_2019_ = _args[14];
lean_object* v___y_2020_ = _args[15];
lean_object* v___y_2021_ = _args[16];
lean_object* v___y_2022_ = _args[17];
lean_object* v___y_2023_ = _args[18];
_start:
{
uint8_t v___y_196074__boxed_2024_; uint8_t v___x_196075__boxed_2025_; uint8_t v___x_196076__boxed_2026_; lean_object* v_res_2027_; 
v___y_196074__boxed_2024_ = lean_unbox(v___y_2007_);
v___x_196075__boxed_2025_ = lean_unbox(v___x_2008_);
v___x_196076__boxed_2026_ = lean_unbox(v___x_2009_);
v_res_2027_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2005_, v_a_2006_, v___y_196074__boxed_2024_, v___x_196075__boxed_2025_, v___x_196076__boxed_2026_, v_mvarId_2010_, v___x_2011_, v_a_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___x_2005_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2030_, lean_object* v___x_2031_, lean_object* v_generation_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
lean_inc(v_mvarId_2030_);
v___x_2044_ = l_Lean_MVarId_getTag(v_mvarId_2030_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2031_, v_a_2045_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_n(v_a_2047_, 2);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2030_, v_a_2047_, v___y_2040_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v___x_2049_; lean_object* v_toGoalState_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref_known(v___x_2048_, 1);
v___x_2049_ = lean_st_ref_get(v___y_2033_);
v_toGoalState_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2049_, 1);
lean_dec(v_unused_2060_);
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_toGoalState_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_Expr_mvarId_x21(v_a_2047_);
lean_dec(v_a_2047_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___x_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_toGoalState_2050_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2056_, v_generation_2032_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2057_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_2047_);
lean_dec(v_generation_2032_);
v_a_2061_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2048_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2048_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_generation_2032_);
lean_dec(v_mvarId_2030_);
v_a_2069_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2046_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2046_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_generation_2032_);
lean_dec_ref(v___x_2031_);
lean_dec(v_mvarId_2030_);
v_a_2077_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2044_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2044_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2085_, lean_object* v___x_2086_, lean_object* v_generation_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2085_, v___x_2086_, v_generation_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec(v___y_2088_);
return v_res_2099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2107_ = l_Lean_mkConst(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2108_, lean_object* v_generation_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v_a_2122_; lean_object* v___y_2127_; lean_object* v___x_2137_; lean_object* v_mvarId_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2426_; 
lean_inc_ref(v_goal_2108_);
v___x_2120_ = lean_st_mk_ref(v_goal_2108_);
v___x_2137_ = lean_st_ref_get(v___x_2120_);
v_mvarId_2138_ = lean_ctor_get(v___x_2137_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2137_, 0);
lean_dec(v_unused_2427_);
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2426_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_mvarId_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2426_;
goto v_resetjp_2139_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_st_ref_get(v___x_2120_);
lean_dec(v___x_2120_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
v___jp_2126_:
{
if (lean_obj_tag(v___y_2127_) == 0)
{
lean_object* v_a_2128_; 
v_a_2128_ = lean_ctor_get(v___y_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___y_2127_, 1);
v_a_2122_ = v_a_2128_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v___x_2120_);
v_a_2129_ = lean_ctor_get(v___y_2127_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___y_2127_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___y_2127_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___y_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_MVarId_getType(v_mvarId_2138_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; uint8_t v___x_2144_; uint8_t v___x_2145_; lean_object* v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_Expr_isForall(v_a_2143_);
v___x_2145_ = 1;
if (v___x_2144_ == 0)
{
uint8_t v___x_2187_; 
lean_del_object(v___x_2140_);
v___x_2187_ = l_Lean_Expr_isLet(v_a_2143_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v_a_2143_);
lean_dec_ref(v___y_2115_);
lean_dec(v_generation_2109_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_goal_2108_);
v_a_2122_ = v___x_2188_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_goal_2108_);
v___x_2189_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2111_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; uint8_t v_zetaDelta_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_zetaDelta_2191_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*14 + 19);
lean_dec(v_a_2190_);
if (v_zetaDelta_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_a_2143_);
v___x_2192_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v_mvarId_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = lean_st_ref_get(v___x_2120_);
v_mvarId_2195_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_mvarId_2195_);
lean_dec(v___x_2194_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2196_, 0, v_a_2193_);
lean_closure_set(v___f_2196_, 1, v_generation_2109_);
v___x_2197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2195_, v___f_2196_, v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec_ref(v___y_2115_);
v___y_2127_ = v___x_2197_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
lean_dec(v_generation_2109_);
v_a_2198_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2192_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2192_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v_mvarId_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; 
v___x_2206_ = lean_st_ref_get(v___x_2120_);
v_mvarId_2207_ = lean_ctor_get(v___x_2206_, 1);
lean_inc_n(v_mvarId_2207_, 2);
lean_dec(v___x_2206_);
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2209_ = l_Lean_Meta_expandLet(v_a_2143_, v___x_2208_, v___x_2145_);
lean_dec(v_a_2143_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2210_, 0, v_mvarId_2207_);
lean_closure_set(v___f_2210_, 1, v___x_2209_);
lean_closure_set(v___f_2210_, 2, v_generation_2109_);
v___x_2211_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2207_, v___f_2210_, v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec_ref(v___y_2115_);
v___y_2127_ = v___x_2211_;
goto v___jp_2126_;
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
lean_dec(v_generation_2109_);
v_a_2212_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2189_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2189_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___y_2222_; lean_object* v___y_2223_; uint8_t v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; uint8_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v_localInsts_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___x_2318_; 
lean_dec(v_generation_2109_);
lean_dec_ref(v_goal_2108_);
v___x_2220_ = l_Lean_Expr_bindingDomain_x21(v_a_2143_);
lean_inc_ref(v___x_2220_);
v___x_2318_ = l_Lean_Meta_isProp(v___x_2220_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___y_2321_; uint8_t v___x_2394_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2394_ = lean_unbox(v_a_2319_);
lean_dec(v_a_2319_);
if (v___x_2394_ == 0)
{
if (v___x_2144_ == 0)
{
lean_del_object(v___x_2140_);
v___y_2321_ = v___x_2144_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2395_; 
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
v___x_2395_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec_ref(v___y_2115_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = lean_st_ref_get(v___x_2120_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 3);
lean_ctor_set(v___x_2140_, 1, v___x_2397_);
lean_ctor_set(v___x_2140_, 0, v_a_2396_);
v___x_2399_ = v___x_2140_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
v_a_2122_ = v___x_2399_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_del_object(v___x_2140_);
lean_dec(v___x_2120_);
v_a_2401_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2395_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2395_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
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
}
else
{
uint8_t v___x_2409_; 
lean_del_object(v___x_2140_);
v___x_2409_ = 0;
v___y_2321_ = v___x_2409_;
goto v___jp_2320_;
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v_mvarId_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2392_; 
v___x_2322_ = lean_st_ref_get(v___x_2120_);
v_mvarId_2323_ = lean_ctor_get(v___x_2322_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2393_);
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2392_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_mvarId_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2392_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; 
lean_inc(v_mvarId_2323_);
v___x_2327_ = l_Lean_MVarId_getTag(v_mvarId_2323_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
lean_inc_ref(v___x_2220_);
v___x_2331_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2220_, v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_expr_2333_; lean_object* v_proof_x3f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_expr_2333_ = lean_ctor_get(v_a_2332_, 0);
lean_inc_ref_n(v_expr_2333_, 2);
v_proof_x3f_2334_ = lean_ctor_get(v_a_2332_, 1);
lean_inc(v_proof_x3f_2334_);
lean_dec(v_a_2332_);
v___x_2335_ = l_Lean_Expr_bindingName_x21(v_a_2143_);
lean_inc(v___x_2335_);
v___x_2336_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2335_, v_expr_2333_, v___x_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_lctx_2338_; lean_object* v_localInstances_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_lctx_2338_ = lean_ctor_get(v___y_2115_, 2);
v_localInstances_2339_ = lean_ctor_get(v___y_2115_, 3);
lean_inc_n(v_a_2330_, 2);
v___x_2340_ = l_Lean_mkFVar(v_a_2330_);
v___x_2341_ = l_Lean_Expr_bindingInfo_x21(v_a_2143_);
v___x_2342_ = 0;
lean_inc_ref_n(v_expr_2333_, 2);
lean_inc_ref(v_lctx_2338_);
v___x_2343_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2338_, v_a_2330_, v_a_2337_, v_expr_2333_, v___x_2341_, v___x_2342_);
v___x_2344_ = l_Lean_Meta_isClass_x3f(v_expr_2333_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l_Lean_Expr_bindingBody_x21(v_a_2143_);
if (lean_obj_tag(v_a_2345_) == 1)
{
lean_object* v_val_2347_; lean_object* v___x_2349_; 
v_val_2347_ = lean_ctor_get(v_a_2345_, 0);
lean_inc(v_val_2347_);
lean_dec_ref_known(v_a_2345_, 1);
lean_inc_ref(v___x_2340_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v___x_2340_);
lean_ctor_set(v___x_2325_, 0, v_val_2347_);
v___x_2349_ = v___x_2325_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_val_2347_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2340_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; 
lean_inc_ref(v_localInstances_2339_);
v___x_2350_ = lean_array_push(v_localInstances_2339_, v___x_2349_);
lean_inc(v___x_2120_);
lean_inc_ref(v_expr_2333_);
v___y_2222_ = v_mvarId_2323_;
v___y_2223_ = v___x_2346_;
v___y_2224_ = v___y_2321_;
v___y_2225_ = v_expr_2333_;
v___y_2226_ = v_a_2330_;
v___y_2227_ = v_a_2328_;
v___y_2228_ = v___x_2341_;
v___y_2229_ = v___x_2343_;
v___y_2230_ = v___x_2340_;
v___y_2231_ = v___x_2335_;
v___y_2232_ = v_expr_2333_;
v___y_2233_ = v_proof_x3f_2334_;
v_localInsts_2234_ = v___x_2350_;
v___y_2235_ = v___x_2120_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
goto v___jp_2221_;
}
}
else
{
lean_inc_ref(v_localInstances_2339_);
lean_dec(v_a_2345_);
lean_del_object(v___x_2325_);
lean_inc(v___x_2120_);
lean_inc_ref(v_expr_2333_);
v___y_2222_ = v_mvarId_2323_;
v___y_2223_ = v___x_2346_;
v___y_2224_ = v___y_2321_;
v___y_2225_ = v_expr_2333_;
v___y_2226_ = v_a_2330_;
v___y_2227_ = v_a_2328_;
v___y_2228_ = v___x_2341_;
v___y_2229_ = v___x_2343_;
v___y_2230_ = v___x_2340_;
v___y_2231_ = v___x_2335_;
v___y_2232_ = v_expr_2333_;
v___y_2233_ = v_proof_x3f_2334_;
v_localInsts_2234_ = v_localInstances_2339_;
v___y_2235_ = v___x_2120_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
goto v___jp_2221_;
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v___x_2343_);
lean_dec_ref(v___x_2340_);
lean_dec(v___x_2335_);
lean_dec(v_proof_x3f_2334_);
lean_dec_ref(v_expr_2333_);
lean_dec(v_a_2330_);
lean_dec(v_a_2328_);
lean_del_object(v___x_2325_);
lean_dec(v_mvarId_2323_);
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2352_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2344_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2344_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v___x_2335_);
lean_dec(v_proof_x3f_2334_);
lean_dec_ref(v_expr_2333_);
lean_dec(v_a_2330_);
lean_dec(v_a_2328_);
lean_del_object(v___x_2325_);
lean_dec(v_mvarId_2323_);
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2360_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2336_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2336_);
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
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2330_);
lean_dec(v_a_2328_);
lean_del_object(v___x_2325_);
lean_dec(v_mvarId_2323_);
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2368_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2331_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2331_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2328_);
lean_del_object(v___x_2325_);
lean_dec(v_mvarId_2323_);
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2376_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2329_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2329_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2325_);
lean_dec(v_mvarId_2323_);
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2384_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2327_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2327_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___x_2220_);
lean_dec(v_a_2143_);
lean_del_object(v___x_2140_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
v_a_2410_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2318_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2318_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
v___jp_2221_:
{
if (lean_obj_tag(v___y_2233_) == 0)
{
uint8_t v___x_2245_; 
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v___x_2220_);
v___x_2245_ = l_Lean_Expr_isArrow(v_a_2143_);
lean_dec(v_a_2143_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_expr_instantiate1(v___y_2223_, v___y_2230_);
lean_dec_ref(v___y_2223_);
v___y_2147_ = v___y_2222_;
v___y_2148_ = v___y_2224_;
v___y_2149_ = v___y_2226_;
v___y_2150_ = v___y_2242_;
v___y_2151_ = v___y_2244_;
v___y_2152_ = v_localInsts_2234_;
v___y_2153_ = v___y_2238_;
v___y_2154_ = v___y_2236_;
v___y_2155_ = v___y_2227_;
v___y_2156_ = v___y_2235_;
v___y_2157_ = v___y_2229_;
v___y_2158_ = v___y_2241_;
v___y_2159_ = v___y_2240_;
v___y_2160_ = v___y_2230_;
v___y_2161_ = v___y_2239_;
v___y_2162_ = v___y_2243_;
v___y_2163_ = v___y_2237_;
v___y_2164_ = v___x_2246_;
goto v___jp_2146_;
}
else
{
v___y_2147_ = v___y_2222_;
v___y_2148_ = v___y_2224_;
v___y_2149_ = v___y_2226_;
v___y_2150_ = v___y_2242_;
v___y_2151_ = v___y_2244_;
v___y_2152_ = v_localInsts_2234_;
v___y_2153_ = v___y_2238_;
v___y_2154_ = v___y_2236_;
v___y_2155_ = v___y_2227_;
v___y_2156_ = v___y_2235_;
v___y_2157_ = v___y_2229_;
v___y_2158_ = v___y_2241_;
v___y_2159_ = v___y_2240_;
v___y_2160_ = v___y_2230_;
v___y_2161_ = v___y_2239_;
v___y_2162_ = v___y_2243_;
v___y_2163_ = v___y_2237_;
v___y_2164_ = v___y_2223_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_val_2247_; uint8_t v___x_2248_; 
v_val_2247_ = lean_ctor_get(v___y_2233_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v___y_2233_, 1);
v___x_2248_ = l_Lean_Expr_isArrow(v_a_2143_);
lean_dec(v_a_2143_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_inc_ref(v___y_2223_);
lean_inc_ref_n(v___x_2220_, 2);
v___x_2249_ = l_Lean_mkLambda(v___y_2231_, v___y_2228_, v___x_2220_, v___y_2223_);
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2230_);
lean_inc(v_val_2247_);
v___x_2252_ = l_Lean_mkApp4(v___x_2251_, v___x_2220_, v___y_2232_, v_val_2247_, v___y_2230_);
v___x_2253_ = lean_expr_instantiate1(v___y_2223_, v___x_2252_);
lean_dec_ref(v___x_2252_);
lean_dec_ref(v___y_2223_);
lean_inc_ref(v___x_2253_);
v___x_2254_ = l_Lean_Meta_getLevel(v___x_2253_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
v___x_2256_ = 2;
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2229_, v_localInsts_2234_, v___x_2253_, v___x_2256_, v___y_2227_, v___x_2257_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = l_Lean_Expr_mvarId_x21(v_a_2259_);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_mk_empty_array_with_capacity(v___x_2261_);
v___x_2263_ = lean_array_push(v___x_2262_, v___y_2230_);
v___x_2264_ = 1;
v___x_2265_ = lean_box(v___x_2248_);
v___x_2266_ = lean_box(v___x_2145_);
v___x_2267_ = lean_box(v___x_2264_);
lean_inc(v___x_2260_);
v___f_2268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2268_, 0, v___x_2263_);
lean_closure_set(v___f_2268_, 1, v_a_2259_);
lean_closure_set(v___f_2268_, 2, v___x_2265_);
lean_closure_set(v___f_2268_, 3, v___x_2266_);
lean_closure_set(v___f_2268_, 4, v___x_2267_);
lean_closure_set(v___f_2268_, 5, v_a_2255_);
lean_closure_set(v___f_2268_, 6, v___x_2250_);
lean_closure_set(v___f_2268_, 7, v___x_2220_);
lean_closure_set(v___f_2268_, 8, v___y_2225_);
lean_closure_set(v___f_2268_, 9, v___x_2249_);
lean_closure_set(v___f_2268_, 10, v_val_2247_);
lean_closure_set(v___f_2268_, 11, v___y_2222_);
lean_closure_set(v___f_2268_, 12, v___x_2260_);
lean_closure_set(v___f_2268_, 13, v___y_2226_);
v___x_2269_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2260_, v___f_2268_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
v___y_2127_ = v___x_2269_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2255_);
lean_dec_ref(v___x_2249_);
lean_dec(v_val_2247_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2222_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2120_);
v_a_2270_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2258_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2258_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2249_);
lean_dec(v_val_2247_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
lean_dec_ref(v_localInsts_2234_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2222_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2120_);
v_a_2278_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2254_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2254_);
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
else
{
lean_object* v___x_2286_; 
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_inc_ref(v___y_2223_);
v___x_2286_ = l_Lean_Meta_getLevel(v___y_2223_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = 2;
v___x_2289_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2223_);
v___x_2290_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2229_, v_localInsts_2234_, v___y_2223_, v___x_2288_, v___y_2227_, v___x_2289_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l_Lean_Expr_mvarId_x21(v_a_2291_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_mk_empty_array_with_capacity(v___x_2293_);
v___x_2295_ = lean_array_push(v___x_2294_, v___y_2230_);
v___x_2296_ = 1;
v___x_2297_ = lean_box(v___y_2224_);
v___x_2298_ = lean_box(v___x_2145_);
v___x_2299_ = lean_box(v___x_2296_);
lean_inc(v___x_2292_);
v___f_2300_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2300_, 0, v___x_2295_);
lean_closure_set(v___f_2300_, 1, v_a_2291_);
lean_closure_set(v___f_2300_, 2, v___x_2297_);
lean_closure_set(v___f_2300_, 3, v___x_2298_);
lean_closure_set(v___f_2300_, 4, v___x_2299_);
lean_closure_set(v___f_2300_, 5, v_a_2287_);
lean_closure_set(v___f_2300_, 6, v___x_2220_);
lean_closure_set(v___f_2300_, 7, v___y_2225_);
lean_closure_set(v___f_2300_, 8, v___y_2223_);
lean_closure_set(v___f_2300_, 9, v_val_2247_);
lean_closure_set(v___f_2300_, 10, v___y_2222_);
lean_closure_set(v___f_2300_, 11, v___x_2292_);
lean_closure_set(v___f_2300_, 12, v___y_2226_);
v___x_2301_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2292_, v___f_2300_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
v___y_2127_ = v___x_2301_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_a_2287_);
lean_dec(v_val_2247_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2120_);
v_a_2302_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2290_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2290_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_val_2247_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2235_);
lean_dec_ref(v_localInsts_2234_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___x_2220_);
lean_dec(v___x_2120_);
v_a_2310_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2286_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2286_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
v___jp_2146_:
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = 2;
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2157_, v___y_2152_, v___y_2164_, v___x_2165_, v___y_2155_, v___x_2166_, v___y_2158_, v___y_2150_, v___y_2162_, v___y_2151_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l_Lean_Expr_mvarId_x21(v_a_2168_);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_mk_empty_array_with_capacity(v___x_2170_);
v___x_2172_ = lean_array_push(v___x_2171_, v___y_2160_);
v___x_2173_ = 1;
v___x_2174_ = lean_box(v___y_2148_);
v___x_2175_ = lean_box(v___x_2145_);
v___x_2176_ = lean_box(v___x_2173_);
lean_inc(v___x_2169_);
v___f_2177_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2177_, 0, v___x_2172_);
lean_closure_set(v___f_2177_, 1, v_a_2168_);
lean_closure_set(v___f_2177_, 2, v___x_2174_);
lean_closure_set(v___f_2177_, 3, v___x_2175_);
lean_closure_set(v___f_2177_, 4, v___x_2176_);
lean_closure_set(v___f_2177_, 5, v___y_2147_);
lean_closure_set(v___f_2177_, 6, v___x_2169_);
lean_closure_set(v___f_2177_, 7, v___y_2149_);
v___x_2178_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2169_, v___f_2177_, v___y_2156_, v___y_2154_, v___y_2163_, v___y_2153_, v___y_2161_, v___y_2159_, v___y_2158_, v___y_2150_, v___y_2162_, v___y_2151_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2156_);
v___y_2127_ = v___x_2178_;
goto v___jp_2126_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v___y_2160_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2156_);
lean_dec(v___y_2149_);
lean_dec(v___y_2147_);
lean_dec(v___x_2120_);
v_a_2179_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2167_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2167_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_del_object(v___x_2140_);
lean_dec(v___x_2120_);
lean_dec_ref(v___y_2115_);
lean_dec(v_generation_2109_);
lean_dec_ref(v_goal_2108_);
v_a_2418_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2142_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2142_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2428_, lean_object* v_generation_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2428_, v_generation_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2441_, lean_object* v_generation_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_mvarId_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v_mvarId_2453_ = lean_ctor_get(v_goal_2441_, 1);
lean_inc(v_mvarId_2453_);
v___f_2454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2454_, 0, v_goal_2441_);
lean_closure_set(v___f_2454_, 1, v_generation_2442_);
v___x_2455_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2453_, v___f_2454_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2464_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_fst_2460_; lean_object* v___x_2462_; 
v_fst_2460_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_fst_2460_);
lean_dec(v_a_2456_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v_fst_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_fst_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v_a_2465_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2455_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2455_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2473_, lean_object* v_generation_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2473_, v_generation_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2486_, lean_object* v_val_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2486_, v_val_2487_, v___y_2495_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2500_, lean_object* v_val_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2500_, v_val_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2523_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2539_, v_x_2540_, v_x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2543_, lean_object* v_x_2544_, size_t v_x_2545_, size_t v_x_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2544_, v_x_2545_, v_x_2546_, v_x_2547_, v_x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
size_t v_x_197101__boxed_2556_; size_t v_x_197102__boxed_2557_; lean_object* v_res_2558_; 
v_x_197101__boxed_2556_ = lean_unbox_usize(v_x_2552_);
lean_dec(v_x_2552_);
v_x_197102__boxed_2557_ = lean_unbox_usize(v_x_2553_);
lean_dec(v_x_2553_);
v_res_2558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2550_, v_x_2551_, v_x_197101__boxed_2556_, v_x_197102__boxed_2557_, v_x_2554_, v_x_2555_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2559_, lean_object* v_n_2560_, lean_object* v_k_2561_, lean_object* v_v_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2560_, v_k_2561_, v_v_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2564_, size_t v_depth_2565_, lean_object* v_keys_2566_, lean_object* v_vals_2567_, lean_object* v_heq_2568_, lean_object* v_i_2569_, lean_object* v_entries_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2565_, v_keys_2566_, v_vals_2567_, v_i_2569_, v_entries_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2572_, lean_object* v_depth_2573_, lean_object* v_keys_2574_, lean_object* v_vals_2575_, lean_object* v_heq_2576_, lean_object* v_i_2577_, lean_object* v_entries_2578_){
_start:
{
size_t v_depth_boxed_2579_; lean_object* v_res_2580_; 
v_depth_boxed_2579_ = lean_unbox_usize(v_depth_2573_);
lean_dec(v_depth_2573_);
v_res_2580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2572_, v_depth_boxed_2579_, v_keys_2574_, v_vals_2575_, v_heq_2576_, v_i_2577_, v_entries_2578_);
lean_dec_ref(v_vals_2575_);
lean_dec_ref(v_keys_2574_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2582_, v_x_2583_, v_x_2584_, v_x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Expr_getAppFn(v_type_2587_);
if (lean_obj_tag(v___x_2590_) == 4)
{
lean_object* v_declName_2591_; lean_object* v___x_2592_; 
v_declName_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_declName_2591_);
lean_dec_ref_known(v___x_2590_, 2);
v___x_2592_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2591_, v_a_2588_);
lean_dec(v_declName_2591_);
return v___x_2592_;
}
else
{
uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v___x_2590_);
v___x_2593_ = 0;
v___x_2594_ = lean_box(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2596_, v_a_2597_);
lean_dec_ref(v_a_2597_);
lean_dec_ref(v_type_2596_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2600_, v_a_2602_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_type_2612_);
return v_res_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
lean_ctor_set(v___x_2629_, 2, v___x_2628_);
lean_ctor_set(v___x_2629_, 3, v___x_2628_);
lean_ctor_set(v___x_2629_, 4, v___x_2627_);
lean_ctor_set(v___x_2629_, 5, v___x_2627_);
lean_ctor_set(v___x_2629_, 6, v___x_2627_);
lean_ctor_set(v___x_2629_, 7, v___x_2627_);
lean_ctor_set(v___x_2629_, 8, v___x_2627_);
lean_ctor_set(v___x_2629_, 9, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = lean_unsigned_to_nat(32u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2633_ = ((size_t)5ULL);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_unsigned_to_nat(32u);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2635_);
v___x_2637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
lean_ctor_set(v___x_2638_, 2, v___x_2634_);
lean_ctor_set(v___x_2638_, 3, v___x_2634_);
lean_ctor_set_usize(v___x_2638_, 4, v___x_2633_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2639_ = lean_box(1);
v___x_2640_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v___x_2640_);
lean_ctor_set(v___x_2642_, 2, v___x_2639_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2664_, lean_object* v_declHint_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; lean_object* v_env_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_st_ref_get(v___y_2666_);
v_env_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_env_2669_);
lean_dec(v___x_2668_);
v___x_2670_ = l_Lean_Name_isAnonymous(v_declHint_2665_);
if (v___x_2670_ == 0)
{
uint8_t v_isExporting_2671_; 
v_isExporting_2671_ = lean_ctor_get_uint8(v_env_2669_, sizeof(void*)*8);
if (v_isExporting_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec_ref(v_env_2669_);
lean_dec(v_declHint_2665_);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_msg_2664_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
lean_inc_ref(v_env_2669_);
v___x_2673_ = l_Lean_Environment_setExporting(v_env_2669_, v___x_2670_);
lean_inc(v_declHint_2665_);
lean_inc_ref(v___x_2673_);
v___x_2674_ = l_Lean_Environment_contains(v___x_2673_, v_declHint_2665_, v_isExporting_2671_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v___x_2673_);
lean_dec_ref(v_env_2669_);
lean_dec(v_declHint_2665_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_msg_2664_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_c_2681_; lean_object* v___x_2682_; 
v___x_2676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2678_ = l_Lean_Options_empty;
v___x_2679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2673_);
lean_ctor_set(v___x_2679_, 1, v___x_2676_);
lean_ctor_set(v___x_2679_, 2, v___x_2677_);
lean_ctor_set(v___x_2679_, 3, v___x_2678_);
lean_inc(v_declHint_2665_);
v___x_2680_ = l_Lean_MessageData_ofConstName(v_declHint_2665_, v___x_2670_);
v_c_2681_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2681_, 0, v___x_2679_);
lean_ctor_set(v_c_2681_, 1, v___x_2680_);
v___x_2682_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2669_, v_declHint_2665_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec_ref(v_env_2669_);
lean_dec(v_declHint_2665_);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v_c_2681_);
v___x_2685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_note(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_msg_2664_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
else
{
lean_object* v_val_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2725_; 
v_val_2690_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2692_ = v___x_2682_;
v_isShared_2693_ = v_isSharedCheck_2725_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_val_2690_);
lean_dec(v___x_2682_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2725_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v_mod_2697_; uint8_t v___x_2698_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = l_Lean_Environment_header(v_env_2669_);
lean_dec_ref(v_env_2669_);
v___x_2696_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2695_);
v_mod_2697_ = lean_array_get(v___x_2694_, v___x_2696_, v_val_2690_);
lean_dec(v_val_2690_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l_Lean_isPrivateName(v_declHint_2665_);
lean_dec(v_declHint_2665_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v_c_2681_);
v___x_2701_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_MessageData_ofName(v_mod_2697_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_MessageData_note(v___x_2706_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_msg_2664_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2708_);
v___x_2710_ = v___x_2692_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v_c_2681_);
v___x_2714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Lean_MessageData_ofName(v_mod_2697_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_MessageData_note(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_msg_2664_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2721_);
v___x_2723_ = v___x_2692_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2726_; 
lean_dec_ref(v_env_2669_);
lean_dec(v_declHint_2665_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_msg_2664_);
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2727_, lean_object* v_declHint_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2727_, v_declHint_2728_, v___y_2729_);
lean_dec(v___y_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2747_; 
v___x_2737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2732_, v_declHint_2733_, v___y_2735_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2747_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2742_ = l_Lean_unknownIdentifierMessageTag;
v___x_2743_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v_a_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v_env_2759_; lean_object* v_options_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2758_ = lean_st_ref_get(v___y_2756_);
v_env_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_ref(v_env_2759_);
lean_dec(v___x_2758_);
v_options_2760_ = lean_ctor_get(v___y_2755_, 2);
v___x_2761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2762_ = lean_unsigned_to_nat(32u);
v___x_2763_ = lean_mk_empty_array_with_capacity(v___x_2762_);
lean_dec_ref(v___x_2763_);
v___x_2764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2760_);
v___x_2765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2765_, 0, v_env_2759_);
lean_ctor_set(v___x_2765_, 1, v___x_2761_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
lean_ctor_set(v___x_2765_, 3, v_options_2760_);
v___x_2766_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v_msgData_2754_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_ref_2777_; lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2787_; 
v_ref_2777_ = lean_ctor_get(v___y_2774_, 5);
v___x_2778_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2773_, v___y_2774_, v___y_2775_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_inc(v_ref_2777_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_ref_2777_);
lean_ctor_set(v___x_2783_, 1, v_a_2779_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 1);
lean_ctor_set(v___x_2781_, 0, v___x_2783_);
v___x_2785_ = v___x_2781_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2793_, lean_object* v_msg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_fileName_2798_; lean_object* v_fileMap_2799_; lean_object* v_options_2800_; lean_object* v_currRecDepth_2801_; lean_object* v_maxRecDepth_2802_; lean_object* v_ref_2803_; lean_object* v_currNamespace_2804_; lean_object* v_openDecls_2805_; lean_object* v_initHeartbeats_2806_; lean_object* v_maxHeartbeats_2807_; lean_object* v_quotContext_2808_; lean_object* v_currMacroScope_2809_; uint8_t v_diag_2810_; lean_object* v_cancelTk_x3f_2811_; uint8_t v_suppressElabErrors_2812_; lean_object* v_inheritedTraceOptions_2813_; lean_object* v_ref_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_fileName_2798_ = lean_ctor_get(v___y_2795_, 0);
v_fileMap_2799_ = lean_ctor_get(v___y_2795_, 1);
v_options_2800_ = lean_ctor_get(v___y_2795_, 2);
v_currRecDepth_2801_ = lean_ctor_get(v___y_2795_, 3);
v_maxRecDepth_2802_ = lean_ctor_get(v___y_2795_, 4);
v_ref_2803_ = lean_ctor_get(v___y_2795_, 5);
v_currNamespace_2804_ = lean_ctor_get(v___y_2795_, 6);
v_openDecls_2805_ = lean_ctor_get(v___y_2795_, 7);
v_initHeartbeats_2806_ = lean_ctor_get(v___y_2795_, 8);
v_maxHeartbeats_2807_ = lean_ctor_get(v___y_2795_, 9);
v_quotContext_2808_ = lean_ctor_get(v___y_2795_, 10);
v_currMacroScope_2809_ = lean_ctor_get(v___y_2795_, 11);
v_diag_2810_ = lean_ctor_get_uint8(v___y_2795_, sizeof(void*)*14);
v_cancelTk_x3f_2811_ = lean_ctor_get(v___y_2795_, 12);
v_suppressElabErrors_2812_ = lean_ctor_get_uint8(v___y_2795_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2813_ = lean_ctor_get(v___y_2795_, 13);
v_ref_2814_ = l_Lean_replaceRef(v_ref_2793_, v_ref_2803_);
lean_inc_ref(v_inheritedTraceOptions_2813_);
lean_inc(v_cancelTk_x3f_2811_);
lean_inc(v_currMacroScope_2809_);
lean_inc(v_quotContext_2808_);
lean_inc(v_maxHeartbeats_2807_);
lean_inc(v_initHeartbeats_2806_);
lean_inc(v_openDecls_2805_);
lean_inc(v_currNamespace_2804_);
lean_inc(v_maxRecDepth_2802_);
lean_inc(v_currRecDepth_2801_);
lean_inc_ref(v_options_2800_);
lean_inc_ref(v_fileMap_2799_);
lean_inc_ref(v_fileName_2798_);
v___x_2815_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2815_, 0, v_fileName_2798_);
lean_ctor_set(v___x_2815_, 1, v_fileMap_2799_);
lean_ctor_set(v___x_2815_, 2, v_options_2800_);
lean_ctor_set(v___x_2815_, 3, v_currRecDepth_2801_);
lean_ctor_set(v___x_2815_, 4, v_maxRecDepth_2802_);
lean_ctor_set(v___x_2815_, 5, v_ref_2814_);
lean_ctor_set(v___x_2815_, 6, v_currNamespace_2804_);
lean_ctor_set(v___x_2815_, 7, v_openDecls_2805_);
lean_ctor_set(v___x_2815_, 8, v_initHeartbeats_2806_);
lean_ctor_set(v___x_2815_, 9, v_maxHeartbeats_2807_);
lean_ctor_set(v___x_2815_, 10, v_quotContext_2808_);
lean_ctor_set(v___x_2815_, 11, v_currMacroScope_2809_);
lean_ctor_set(v___x_2815_, 12, v_cancelTk_x3f_2811_);
lean_ctor_set(v___x_2815_, 13, v_inheritedTraceOptions_2813_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*14, v_diag_2810_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*14 + 1, v_suppressElabErrors_2812_);
v___x_2816_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2794_, v___x_2815_, v___y_2796_);
lean_dec_ref_known(v___x_2815_, 14);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2817_, lean_object* v_msg_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2817_, v_msg_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v_ref_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2823_, lean_object* v_msg_2824_, lean_object* v_declHint_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; lean_object* v_a_2830_; lean_object* v___x_2831_; 
v___x_2829_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2824_, v_declHint_2825_, v___y_2826_, v___y_2827_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2823_, v_a_2830_, v___y_2826_, v___y_2827_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2832_, lean_object* v_msg_2833_, lean_object* v_declHint_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2832_, v_msg_2833_, v_declHint_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v_ref_2832_);
return v_res_2838_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2845_, lean_object* v_constName_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2850_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2851_ = 0;
lean_inc(v_constName_2846_);
v___x_2852_ = l_Lean_MessageData_ofConstName(v_constName_2846_, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2850_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2845_, v___x_2855_, v_constName_2846_, v___y_2847_, v___y_2848_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2857_, lean_object* v_constName_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2857_, v_constName_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v_ref_2857_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_ref_2867_; lean_object* v___x_2868_; 
v_ref_2867_ = lean_ctor_get(v___y_2864_, 5);
v___x_2868_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2867_, v_constName_2863_, v___y_2864_, v___y_2865_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; lean_object* v_env_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; 
v___x_2878_ = lean_st_ref_get(v___y_2876_);
v_env_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc_ref(v_env_2879_);
lean_dec(v___x_2878_);
v___x_2880_ = 0;
lean_inc(v_constName_2874_);
v___x_2881_ = l_Lean_Environment_find_x3f(v_env_2879_, v_constName_2874_, v___x_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2874_, v___y_2875_, v___y_2876_);
return v___x_2882_;
}
else
{
lean_object* v_val_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_constName_2874_);
v_val_2883_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2881_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_val_2883_);
lean_dec(v___x_2881_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 0);
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_val_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Expr_getAppFn(v_type_2896_);
if (lean_obj_tag(v___x_2900_) == 4)
{
lean_object* v_declName_2901_; lean_object* v___x_2902_; 
v_declName_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_declName_2901_);
lean_dec_ref_known(v___x_2900_, 2);
v___x_2902_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2901_, v_a_2897_, v_a_2898_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2920_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2920_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2920_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
if (lean_obj_tag(v_a_2903_) == 5)
{
lean_object* v_val_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_val_2907_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_val_2907_);
lean_dec_ref_known(v_a_2903_, 1);
v___x_2908_ = l_Lean_InductiveVal_numCtors(v_val_2907_);
lean_dec_ref(v_val_2907_);
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_dec_le(v___x_2908_, v___x_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(v___x_2910_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2911_);
v___x_2913_ = v___x_2905_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
else
{
uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
lean_dec(v_a_2903_);
v___x_2915_ = 0;
v___x_2916_ = lean_box(v___x_2915_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2916_);
v___x_2918_ = v___x_2905_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2902_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2902_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec_ref(v___x_2900_);
v___x_2929_ = 0;
v___x_2930_ = lean_box(v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec_ref(v_type_2932_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2937_, lean_object* v_constName_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2938_, v___y_2939_, v___y_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_constName_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2943_, v_constName_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2949_, lean_object* v_ref_2950_, lean_object* v_constName_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2950_, v_constName_2951_, v___y_2952_, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_ref_2957_, lean_object* v_constName_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2956_, v_ref_2957_, v_constName_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v_ref_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2963_, lean_object* v_ref_2964_, lean_object* v_msg_2965_, lean_object* v_declHint_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2964_, v_msg_2965_, v_declHint_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_ref_2972_, lean_object* v_msg_2973_, lean_object* v_declHint_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2971_, v_ref_2972_, v_msg_2973_, v_declHint_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v_ref_2972_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2979_, lean_object* v_declHint_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2979_, v_declHint_2980_, v___y_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2985_, lean_object* v_declHint_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2985_, v_declHint_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2991_, lean_object* v_ref_2992_, lean_object* v_msg_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2992_, v_msg_2993_, v___y_2994_, v___y_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2998_, lean_object* v_ref_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2998_, v_ref_2999_, v_msg_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v_ref_2999_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3011_, v_msg_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3017_, lean_object* v_fvarId_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_toGoalState_3024_; lean_object* v_mvarId_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3061_; 
v_toGoalState_3024_ = lean_ctor_get(v_goal_3017_, 0);
v_mvarId_3025_ = lean_ctor_get(v_goal_3017_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_goal_3017_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3027_ = v_goal_3017_;
v_isShared_3028_ = v_isSharedCheck_3061_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_mvarId_3025_);
lean_inc(v_toGoalState_3024_);
lean_dec(v_goal_3017_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3061_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3025_, v_fvarId_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3052_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3052_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3052_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
if (lean_obj_tag(v_a_3030_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3047_; 
v_val_3034_ = lean_ctor_get(v_a_3030_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_a_3030_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3036_ = v_a_3030_;
v_isShared_3037_ = v_isSharedCheck_3047_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_val_3034_);
lean_dec(v_a_3030_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3047_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v_val_3034_);
v___x_3039_ = v___x_3027_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_toGoalState_3024_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_val_3034_);
v___x_3039_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3039_);
v___x_3041_ = v___x_3036_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3041_);
v___x_3043_ = v___x_3032_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_dec(v_a_3030_);
lean_del_object(v___x_3027_);
lean_dec_ref(v_toGoalState_3024_);
v___x_3048_ = lean_box(0);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3048_);
v___x_3050_ = v___x_3032_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_del_object(v___x_3027_);
lean_dec_ref(v_toGoalState_3024_);
v_a_3053_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3029_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3029_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3062_, lean_object* v_fvarId_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3062_, v_fvarId_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3070_, v_x_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
v_a_3086_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3077_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3077_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3094_, v_x_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3102_, lean_object* v_mvarId_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3103_, v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_mvarId_3112_, lean_object* v_x_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3111_, v_mvarId_3112_, v_x_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3120_, lean_object* v_toGoalState_3121_, lean_object* v_goal_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
lean_inc(v_mvarId_3120_);
v___x_3128_ = l_Lean_MVarId_getType(v_mvarId_3120_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3130_ = l_Lean_Meta_isProp(v_a_3129_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3157_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3157_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3157_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_unbox(v_a_3131_);
lean_dec(v_a_3131_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_del_object(v___x_3133_);
lean_dec_ref(v_goal_3122_);
v___x_3136_ = l_Lean_MVarId_exfalso(v_mvarId_3120_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3145_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v_toGoalState_3121_);
lean_ctor_set(v___x_3141_, 1, v_a_3137_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3143_ = v___x_3139_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_toGoalState_3121_);
v_a_3146_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3136_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3136_);
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
else
{
lean_object* v___x_3155_; 
lean_dec_ref(v_toGoalState_3121_);
lean_dec(v_mvarId_3120_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_goal_3122_);
v___x_3155_ = v___x_3133_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_goal_3122_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v_goal_3122_);
lean_dec_ref(v_toGoalState_3121_);
lean_dec(v_mvarId_3120_);
v_a_3158_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3130_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3130_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v_goal_3122_);
lean_dec_ref(v_toGoalState_3121_);
lean_dec(v_mvarId_3120_);
v_a_3166_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3128_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3128_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3174_, lean_object* v_toGoalState_3175_, lean_object* v_goal_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3174_, v_toGoalState_3175_, v_goal_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_toGoalState_3189_; lean_object* v_mvarId_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; 
v_toGoalState_3189_ = lean_ctor_get(v_goal_3183_, 0);
lean_inc_ref(v_toGoalState_3189_);
v_mvarId_3190_ = lean_ctor_get(v_goal_3183_, 1);
lean_inc_n(v_mvarId_3190_, 2);
v___f_3191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3191_, 0, v_mvarId_3190_);
lean_closure_set(v___f_3191_, 1, v_toGoalState_3189_);
lean_closure_set(v___f_3191_, 2, v_goal_3183_);
v___x_3192_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3190_, v___f_3191_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_mvarId_3206_; lean_object* v___x_3207_; 
v_mvarId_3206_ = lean_ctor_get(v_goal_3200_, 1);
lean_inc(v_mvarId_3206_);
lean_dec_ref(v_goal_3200_);
v___x_3207_ = l_Lean_MVarId_getDecl(v_mvarId_3206_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3217_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3217_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3217_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_lctx_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v_lctx_3212_ = lean_ctor_get(v_a_3208_, 1);
lean_inc_ref(v_lctx_3212_);
lean_dec(v_a_3208_);
v___x_3213_ = l_Lean_LocalContext_lastDecl(v_lctx_3212_);
lean_dec_ref(v_lctx_3212_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3213_);
v___x_3215_ = v___x_3210_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3207_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3207_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
if (lean_obj_tag(v_a_3234_) == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = l_List_reverse___redArg(v_a_3235_);
return v___x_3236_;
}
else
{
lean_object* v_head_3237_; lean_object* v_tail_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3248_; 
v_head_3237_ = lean_ctor_get(v_a_3234_, 0);
v_tail_3238_ = lean_ctor_get(v_a_3234_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3240_ = v_a_3234_;
v_isShared_3241_ = v_isSharedCheck_3248_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_tail_3238_);
lean_inc(v_head_3237_);
lean_dec(v_a_3234_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3248_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_toGoalState_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v_toGoalState_3242_ = lean_ctor_get(v_goal_3233_, 0);
lean_inc_ref(v_toGoalState_3242_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_toGoalState_3242_);
lean_ctor_set(v___x_3243_, 1, v_head_3237_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v_a_3235_);
lean_ctor_set(v___x_3240_, 0, v___x_3243_);
v___x_3245_ = v___x_3240_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_a_3235_);
v___x_3245_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
v_a_3234_ = v_tail_3238_;
v_a_3235_ = v___x_3245_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3249_, v_a_3250_, v_a_3251_);
lean_dec_ref(v_goal_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3253_, lean_object* v_as_x27_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
if (lean_obj_tag(v_as_x27_3254_) == 0)
{
lean_object* v___x_3266_; 
lean_dec_ref(v_kp_3253_);
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_b_3255_);
return v___x_3266_;
}
else
{
lean_object* v_head_3267_; lean_object* v_tail_3268_; lean_object* v___x_3269_; 
v_head_3267_ = lean_ctor_get(v_as_x27_3254_, 0);
v_tail_3268_ = lean_ctor_get(v_as_x27_3254_, 1);
lean_inc_ref(v_kp_3253_);
lean_inc(v___y_3264_);
lean_inc_ref(v___y_3263_);
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
lean_inc(v___y_3256_);
lean_inc(v_head_3267_);
v___x_3269_ = lean_apply_11(v_kp_3253_, v_head_3267_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, lean_box(0));
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
if (lean_obj_tag(v_a_3270_) == 0)
{
lean_object* v_fst_3271_; lean_object* v_snd_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3282_; 
v_fst_3271_ = lean_ctor_get(v_b_3255_, 0);
v_snd_3272_ = lean_ctor_get(v_b_3255_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_b_3255_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3274_ = v_b_3255_;
v_isShared_3275_ = v_isSharedCheck_3282_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_snd_3272_);
lean_inc(v_fst_3271_);
lean_dec(v_b_3255_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3282_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_seq_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v_seq_3276_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_seq_3276_);
lean_dec_ref_known(v_a_3270_, 1);
v___x_3277_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3271_, v_seq_3276_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3277_);
v___x_3279_ = v___x_3274_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_snd_3272_);
v___x_3279_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_as_x27_3254_ = v_tail_3268_;
v_b_3255_ = v___x_3279_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3283_; lean_object* v_snd_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3294_; 
v_fst_3283_ = lean_ctor_get(v_b_3255_, 0);
v_snd_3284_ = lean_ctor_get(v_b_3255_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_b_3255_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3286_ = v_b_3255_;
v_isShared_3287_ = v_isSharedCheck_3294_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_snd_3284_);
lean_inc(v_fst_3283_);
lean_dec(v_b_3255_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3294_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_gs_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v_gs_3288_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_gs_3288_);
lean_dec_ref_known(v_a_3270_, 1);
v___x_3289_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3284_, v_gs_3288_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v___x_3289_);
v___x_3291_ = v___x_3286_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_fst_3283_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
v_as_x27_3254_ = v_tail_3268_;
v_b_3255_ = v___x_3291_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v_b_3255_);
lean_dec_ref(v_kp_3253_);
v_a_3295_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3269_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3269_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3303_, lean_object* v_as_x27_3304_, lean_object* v_b_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3303_, v_as_x27_3304_, v_b_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec(v_as_x27_3304_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3321_, lean_object* v_mvarId_3322_, lean_object* v_goal_3323_, lean_object* v_kp_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___x_3390_; 
lean_inc(v_fvarId_3321_);
v___x_3390_ = l_Lean_FVarId_getType___redArg(v_fvarId_3321_, v___y_3330_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
v___x_3392_ = lean_whnf(v_a_3391_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___x_3415_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3415_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3393_, v___y_3326_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3455_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3455_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3455_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_unbox(v_a_3416_);
lean_dec(v_a_3416_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v___x_3421_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3421_);
v___x_3423_ = v___x_3418_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
else
{
lean_object* v___x_3425_; 
lean_del_object(v___x_3418_);
v___x_3425_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3326_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = lean_unbox(v_a_3426_);
lean_dec(v_a_3426_);
if (v___x_3427_ == 0)
{
v___y_3395_ = v___y_3325_;
v___y_3396_ = v___y_3326_;
v___y_3397_ = v___y_3327_;
v___y_3398_ = v___y_3328_;
v___y_3399_ = v___y_3329_;
v___y_3400_ = v___y_3330_;
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3428_; 
v___x_3428_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3393_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3438_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_unbox(v_a_3429_);
lean_dec(v_a_3429_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v___x_3434_ = lean_box(0);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3434_);
v___x_3436_ = v___x_3431_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
else
{
lean_del_object(v___x_3431_);
v___y_3395_ = v___y_3325_;
v___y_3396_ = v___y_3326_;
v___y_3397_ = v___y_3327_;
v___y_3398_ = v___y_3328_;
v___y_3399_ = v___y_3329_;
v___y_3400_ = v___y_3330_;
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
goto v___jp_3394_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3439_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3428_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3428_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3447_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3425_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3425_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_a_3393_);
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3456_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3415_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3415_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
v___jp_3394_:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Expr_getAppFn(v_a_3393_);
lean_dec(v_a_3393_);
if (lean_obj_tag(v___x_3404_) == 4)
{
lean_object* v_declName_3405_; lean_object* v___x_3406_; 
v_declName_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_declName_3405_);
lean_dec_ref_known(v___x_3404_, 2);
v___x_3406_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3405_, v___y_3397_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v___y_3336_ = v___y_3395_;
v___y_3337_ = v___y_3396_;
v___y_3338_ = v___y_3397_;
v___y_3339_ = v___y_3398_;
v___y_3340_ = v___y_3399_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
goto v___jp_3335_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_dec_ref(v___x_3404_);
v___y_3336_ = v___y_3395_;
v___y_3337_ = v___y_3396_;
v___y_3338_ = v___y_3397_;
v___y_3339_ = v___y_3398_;
v___y_3340_ = v___y_3399_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
goto v___jp_3335_;
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3464_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3392_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3392_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v_kp_3324_);
lean_dec(v_mvarId_3322_);
lean_dec(v_fvarId_3321_);
v_a_3472_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3390_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3390_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
v___jp_3335_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = l_Lean_mkFVar(v_fvarId_3321_);
v___x_3346_ = l_Lean_Meta_Grind_cases(v_mvarId_3322_, v___x_3345_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_box(0);
v___x_3349_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3323_, v_a_3347_, v___x_3348_);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3352_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3324_, v___x_3349_, v___x_3351_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___x_3349_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3373_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3373_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3373_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_fst_3357_ = lean_ctor_get(v_a_3353_, 0);
lean_inc(v_fst_3357_);
v_snd_3358_ = lean_ctor_get(v_a_3353_, 1);
lean_inc(v_snd_3358_);
lean_dec(v_a_3353_);
v___x_3359_ = lean_array_get_size(v_snd_3358_);
v___x_3360_ = lean_nat_dec_eq(v___x_3359_, v___x_3350_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
lean_dec(v_fst_3357_);
v___x_3361_ = lean_array_to_list(v_snd_3358_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3363_);
v___x_3365_ = v___x_3355_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
lean_dec(v_snd_3358_);
v___x_3367_ = lean_array_to_list(v_fst_3357_);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3369_);
v___x_3371_ = v___x_3355_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3374_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3352_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3352_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref(v_kp_3324_);
v_a_3382_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3346_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3346_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3480_, lean_object* v_mvarId_3481_, lean_object* v_goal_3482_, lean_object* v_kp_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3480_, v_mvarId_3481_, v_goal_3482_, v_kp_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v_goal_3482_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3495_, lean_object* v_fvarId_3496_, lean_object* v_kp_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_mvarId_3508_; lean_object* v___f_3509_; lean_object* v___x_3510_; 
v_mvarId_3508_ = lean_ctor_get(v_goal_3495_, 1);
lean_inc_n(v_mvarId_3508_, 2);
v___f_3509_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3509_, 0, v_fvarId_3496_);
lean_closure_set(v___f_3509_, 1, v_mvarId_3508_);
lean_closure_set(v___f_3509_, 2, v_goal_3495_);
lean_closure_set(v___f_3509_, 3, v_kp_3497_);
v___x_3510_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3508_, v___f_3509_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3511_, lean_object* v_fvarId_3512_, lean_object* v_kp_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3511_, v_fvarId_3512_, v_kp_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3525_, lean_object* v_as_3526_, lean_object* v_as_x27_3527_, lean_object* v_b_3528_, lean_object* v_a_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3525_, v_as_x27_3527_, v_b_3528_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3541_, lean_object* v_as_3542_, lean_object* v_as_x27_3543_, lean_object* v_b_3544_, lean_object* v_a_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3541_, v_as_3542_, v_as_x27_3543_, v_b_3544_, v_a_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec(v_as_x27_3543_);
lean_dec(v_as_3542_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3557_, lean_object* v_fvarId_3558_, lean_object* v_generation_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_st_mk_ref(v_goal_3557_);
v___x_3571_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3558_, v_generation_3559_, v___x_3570_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3580_; 
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3571_, 0);
lean_dec(v_unused_3581_);
v___x_3573_ = v___x_3571_;
v_isShared_3574_ = v_isSharedCheck_3580_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v___x_3571_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3580_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3575_ = lean_st_ref_get(v___x_3570_);
v___x_3576_ = lean_st_ref_get(v___x_3570_);
lean_dec(v___x_3570_);
lean_dec(v___x_3576_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3575_);
v___x_3578_ = v___x_3573_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3575_);
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
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v___x_3570_);
v_a_3582_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3571_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3571_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3590_, lean_object* v_fvarId_3591_, lean_object* v_generation_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3590_, v_fvarId_3591_, v_generation_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3606_, lean_object* v_goal_3607_, lean_object* v_kna_3608_, lean_object* v_kp_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_toGoalState_3620_; uint8_t v_inconsistent_3621_; 
v_toGoalState_3620_ = lean_ctor_get(v_goal_3607_, 0);
v_inconsistent_3621_ = lean_ctor_get_uint8(v_toGoalState_3620_, sizeof(void*)*17);
if (v_inconsistent_3621_ == 0)
{
lean_object* v_mvarId_3622_; lean_object* v___x_3623_; 
v_mvarId_3622_ = lean_ctor_get(v_goal_3607_, 1);
lean_inc(v_mvarId_3622_);
v___x_3623_ = l_Lean_MVarId_getType(v_mvarId_3622_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; uint8_t v___x_3625_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l_Lean_Expr_isFalse(v_a_3624_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref(v_kna_3608_);
lean_inc(v_generation_3606_);
v___x_3626_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3607_, v_generation_3606_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
switch(lean_obj_tag(v_a_3627_))
{
case 0:
{
lean_object* v_goal_3628_; lean_object* v___x_3629_; 
lean_dec(v_generation_3606_);
v_goal_3628_ = lean_ctor_get(v_a_3627_, 0);
lean_inc_ref(v_goal_3628_);
lean_dec_ref_known(v_a_3627_, 1);
v___x_3629_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3628_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v_toGoalState_3631_; lean_object* v_mvarId_3632_; lean_object* v___x_3633_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v_toGoalState_3631_ = lean_ctor_get(v_a_3630_, 0);
v_mvarId_3632_ = lean_ctor_get(v_a_3630_, 1);
lean_inc(v_mvarId_3632_);
v___x_3633_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3632_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
if (lean_obj_tag(v_a_3634_) == 1)
{
lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3643_; 
lean_inc_ref(v_toGoalState_3631_);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_a_3630_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; lean_object* v_unused_3645_; 
v_unused_3644_ = lean_ctor_get(v_a_3630_, 1);
lean_dec(v_unused_3644_);
v_unused_3645_ = lean_ctor_get(v_a_3630_, 0);
lean_dec(v_unused_3645_);
v___x_3636_ = v_a_3630_;
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
else
{
lean_dec(v_a_3630_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v_val_3638_; lean_object* v___x_3640_; 
v_val_3638_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_val_3638_);
lean_dec_ref_known(v_a_3634_, 1);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v_val_3638_);
v___x_3640_ = v___x_3636_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_toGoalState_3631_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_val_3638_);
v___x_3640_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; 
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3641_ = lean_apply_11(v_kp_3609_, v___x_3640_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3641_;
}
}
}
else
{
lean_object* v___x_3646_; 
lean_dec(v_a_3634_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3646_ = lean_apply_11(v_kp_3609_, v_a_3630_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3646_;
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_a_3630_);
lean_dec_ref(v_kp_3609_);
v_a_3647_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3633_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3633_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec_ref(v_kp_3609_);
v_a_3655_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3629_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3629_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3663_; lean_object* v_goal_3664_; lean_object* v___x_3665_; 
v_fvarId_3663_ = lean_ctor_get(v_a_3627_, 0);
lean_inc_n(v_fvarId_3663_, 2);
v_goal_3664_ = lean_ctor_get(v_a_3627_, 1);
lean_inc_ref_n(v_goal_3664_, 2);
lean_dec_ref_known(v_a_3627_, 2);
v___x_3665_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3664_, v_fvarId_3663_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
if (lean_obj_tag(v_a_3666_) == 1)
{
lean_object* v_val_3667_; lean_object* v___x_3668_; 
lean_dec_ref(v_goal_3664_);
lean_dec(v_fvarId_3663_);
lean_dec(v_generation_3606_);
v_val_3667_ = lean_ctor_get(v_a_3666_, 0);
lean_inc(v_val_3667_);
lean_dec_ref_known(v_a_3666_, 1);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3668_ = lean_apply_11(v_kp_3609_, v_val_3667_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3668_;
}
else
{
lean_object* v___x_3669_; 
lean_dec(v_a_3666_);
lean_inc_ref(v_kp_3609_);
lean_inc(v_fvarId_3663_);
lean_inc_ref(v_goal_3664_);
v___x_3669_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3664_, v_fvarId_3663_, v_kp_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3691_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3691_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3691_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
if (lean_obj_tag(v_a_3670_) == 1)
{
lean_object* v_val_3674_; lean_object* v___x_3676_; 
lean_dec_ref(v_goal_3664_);
lean_dec(v_fvarId_3663_);
lean_dec_ref(v_kp_3609_);
lean_dec(v_generation_3606_);
v_val_3674_ = lean_ctor_get(v_a_3670_, 0);
lean_inc(v_val_3674_);
lean_dec_ref_known(v_a_3670_, 1);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_val_3674_);
v___x_3676_ = v___x_3672_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_val_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
else
{
lean_object* v_mvarId_3678_; lean_object* v___f_3679_; lean_object* v___x_3680_; 
lean_del_object(v___x_3672_);
lean_dec(v_a_3670_);
v_mvarId_3678_ = lean_ctor_get(v_goal_3664_, 1);
lean_inc(v_mvarId_3678_);
v___f_3679_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3679_, 0, v_goal_3664_);
lean_closure_set(v___f_3679_, 1, v_fvarId_3663_);
lean_closure_set(v___f_3679_, 2, v_generation_3606_);
v___x_3680_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3678_, v___f_3679_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3682_ = lean_apply_11(v_kp_3609_, v_a_3681_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_kp_3609_);
v_a_3683_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3680_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3680_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_goal_3664_);
lean_dec(v_fvarId_3663_);
lean_dec_ref(v_kp_3609_);
lean_dec(v_generation_3606_);
v_a_3692_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3669_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3669_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v_goal_3664_);
lean_dec(v_fvarId_3663_);
lean_dec_ref(v_kp_3609_);
lean_dec(v_generation_3606_);
v_a_3700_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3665_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3665_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
case 2:
{
lean_object* v_goal_3708_; lean_object* v___x_3709_; 
lean_dec(v_generation_3606_);
v_goal_3708_ = lean_ctor_get(v_a_3627_, 0);
lean_inc_ref(v_goal_3708_);
lean_dec_ref_known(v_a_3627_, 1);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3709_ = lean_apply_11(v_kp_3609_, v_goal_3708_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3709_;
}
default: 
{
lean_object* v_fvarId_3710_; lean_object* v_goal_3711_; lean_object* v___x_3712_; 
lean_dec(v_generation_3606_);
v_fvarId_3710_ = lean_ctor_get(v_a_3627_, 0);
lean_inc(v_fvarId_3710_);
v_goal_3711_ = lean_ctor_get(v_a_3627_, 1);
lean_inc_ref_n(v_goal_3711_, 2);
lean_dec_ref_known(v_a_3627_, 2);
lean_inc_ref(v_kp_3609_);
v___x_3712_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3711_, v_fvarId_3710_, v_kp_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
if (lean_obj_tag(v_a_3713_) == 1)
{
lean_object* v_val_3717_; lean_object* v___x_3719_; 
lean_dec_ref(v_goal_3711_);
lean_dec_ref(v_kp_3609_);
v_val_3717_ = lean_ctor_get(v_a_3713_, 0);
lean_inc(v_val_3717_);
lean_dec_ref_known(v_a_3713_, 1);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_val_3717_);
v___x_3719_ = v___x_3715_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_val_3717_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
else
{
lean_object* v___x_3721_; 
lean_del_object(v___x_3715_);
lean_dec(v_a_3713_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3721_ = lean_apply_11(v_kp_3609_, v_goal_3711_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3721_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_goal_3711_);
lean_dec_ref(v_kp_3609_);
v_a_3723_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3712_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3712_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v_kp_3609_);
lean_dec(v_generation_3606_);
v_a_3731_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3626_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3626_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v___x_3739_; 
lean_dec_ref(v_kp_3609_);
lean_dec(v_generation_3606_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
lean_inc_ref(v_a_3615_);
lean_inc(v_a_3614_);
lean_inc_ref(v_a_3613_);
lean_inc(v_a_3612_);
lean_inc_ref(v_a_3611_);
lean_inc(v_a_3610_);
v___x_3739_ = lean_apply_11(v_kna_3608_, v_goal_3607_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, lean_box(0));
return v___x_3739_;
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v_kp_3609_);
lean_dec_ref(v_kna_3608_);
lean_dec_ref(v_goal_3607_);
lean_dec(v_generation_3606_);
v_a_3740_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3623_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3623_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_dec_ref(v_kp_3609_);
lean_dec_ref(v_kna_3608_);
lean_dec_ref(v_goal_3607_);
lean_dec(v_generation_3606_);
v___x_3748_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3750_, lean_object* v_goal_3751_, lean_object* v_kna_3752_, lean_object* v_kp_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Meta_Grind_Action_intro(v_generation_3750_, v_goal_3751_, v_kna_3752_, v_kp_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_a_3754_);
return v_res_3764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_unsigned_to_nat(1000000u);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3766_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3781_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3794_, lean_object* v___f_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3809_ = lean_unsigned_to_nat(1000000u);
v___x_3810_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3810_, 0, v_generation_3794_);
v___x_3811_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3811_, 0, v___x_3809_);
lean_closure_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_Meta_Grind_Action_andThen(v___x_3811_, v___f_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3813_, lean_object* v___f_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3813_, v___f_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3831_, lean_object* v_a_3832_, lean_object* v_kna_3833_, lean_object* v_kp_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___f_3845_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3846_, 0, v_generation_3831_);
lean_closure_set(v___f_3846_, 1, v___f_3845_);
v___x_3847_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3848_ = l_Lean_Meta_Grind_Action_andThen(v___x_3847_, v___f_3846_, v_a_3832_, v_kna_3833_, v_kp_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3849_, lean_object* v_a_3850_, lean_object* v_kna_3851_, lean_object* v_kp_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_Grind_Action_intros(v_generation_3849_, v_a_3850_, v_kna_3851_, v_kp_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
return v_res_3863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3873_ = l_Lean_mkConst(v___x_3872_, v___x_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3874_, lean_object* v_prop_3875_, lean_object* v_proof_3876_, lean_object* v_generation_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_st_mk_ref(v_goal_3874_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3885_);
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3883_);
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc(v___x_3888_);
lean_inc_ref(v_prop_3875_);
v___x_3889_ = lean_grind_preprocess(v_prop_3875_, v___x_3888_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v_expr_3891_; lean_object* v___x_3892_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v_expr_3891_ = lean_ctor_get(v_a_3890_, 0);
lean_inc_ref(v_expr_3891_);
v___x_3892_ = l_Lean_Meta_Simp_Result_getProof(v_a_3890_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3891_);
v___x_3895_ = l_Lean_mkApp4(v___x_3894_, v_prop_3875_, v_expr_3891_, v_a_3893_, v_proof_3876_);
v___x_3896_ = l_Lean_Meta_Grind_add(v_expr_3891_, v___x_3895_, v_generation_3877_, v___x_3888_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3905_; 
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3905_ == 0)
{
lean_object* v_unused_3906_; 
v_unused_3906_ = lean_ctor_get(v___x_3896_, 0);
lean_dec(v_unused_3906_);
v___x_3898_ = v___x_3896_;
v_isShared_3899_ = v_isSharedCheck_3905_;
goto v_resetjp_3897_;
}
else
{
lean_dec(v___x_3896_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3905_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3900_ = lean_st_ref_get(v___x_3888_);
v___x_3901_ = lean_st_ref_get(v___x_3888_);
lean_dec(v___x_3888_);
lean_dec(v___x_3901_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3900_);
v___x_3903_ = v___x_3898_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3900_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___x_3888_);
v_a_3907_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3896_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3896_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v_expr_3891_);
lean_dec(v___x_3888_);
lean_dec(v_generation_3877_);
lean_dec_ref(v_proof_3876_);
lean_dec_ref(v_prop_3875_);
v_a_3915_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3892_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3892_);
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
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v___x_3888_);
lean_dec(v_generation_3877_);
lean_dec_ref(v_proof_3876_);
lean_dec_ref(v_prop_3875_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3931_, lean_object* v_prop_3932_, lean_object* v_proof_3933_, lean_object* v_generation_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3931_, v_prop_3932_, v_proof_3933_, v_generation_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3946_, lean_object* v___f_3947_, lean_object* v_kp_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3946_, v___f_3947_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
lean_inc(v___y_3957_);
lean_inc_ref(v___y_3956_);
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3954_);
lean_inc(v___y_3953_);
lean_inc_ref(v___y_3952_);
lean_inc(v___y_3951_);
lean_inc_ref(v___y_3950_);
lean_inc(v___y_3949_);
v___x_3961_ = lean_apply_11(v_kp_3948_, v_a_3960_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, lean_box(0));
return v___x_3961_;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v_kp_3948_);
v_a_3962_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3959_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3959_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3970_, lean_object* v___f_3971_, lean_object* v_kp_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3970_, v___f_3971_, v_kp_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3984_, lean_object* v_prop_3985_, lean_object* v_generation_3986_, lean_object* v_goal_3987_, lean_object* v_kna_3988_, lean_object* v_kp_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3985_, v_a_3991_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; uint8_t v___x_4002_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v___x_4002_ = lean_unbox(v_a_4001_);
lean_dec(v_a_4001_);
if (v___x_4002_ == 0)
{
lean_object* v_mvarId_4003_; lean_object* v___f_4004_; lean_object* v___f_4005_; lean_object* v___x_4006_; 
lean_dec_ref(v_kna_3988_);
v_mvarId_4003_ = lean_ctor_get(v_goal_3987_, 1);
lean_inc_n(v_mvarId_4003_, 2);
v___f_4004_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4004_, 0, v_goal_3987_);
lean_closure_set(v___f_4004_, 1, v_prop_3985_);
lean_closure_set(v___f_4004_, 2, v_proof_3984_);
lean_closure_set(v___f_4004_, 3, v_generation_3986_);
v___f_4005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4005_, 0, v_mvarId_4003_);
lean_closure_set(v___f_4005_, 1, v___f_4004_);
lean_closure_set(v___f_4005_, 2, v_kp_3989_);
v___x_4006_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4003_, v___f_4005_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4008_ = l_Lean_Core_mkFreshUserName(v___x_4007_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v_toGoalState_4010_; lean_object* v_mvarId_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4029_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v_toGoalState_4010_ = lean_ctor_get(v_goal_3987_, 0);
v_mvarId_4011_ = lean_ctor_get(v_goal_3987_, 1);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_goal_3987_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4013_ = v_goal_3987_;
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_mvarId_4011_);
lean_inc(v_toGoalState_4010_);
lean_dec(v_goal_3987_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_MVarId_assert(v_mvarId_4011_, v_a_4009_, v_prop_3985_, v_proof_3984_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v_a_4016_);
v___x_4018_ = v___x_4013_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_toGoalState_4010_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v_a_4016_);
v___x_4018_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_Meta_Grind_Action_intros(v_generation_3986_, v___x_4018_, v_kna_3988_, v_kp_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4019_;
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_del_object(v___x_4013_);
lean_dec_ref(v_toGoalState_4010_);
lean_dec_ref(v_kp_3989_);
lean_dec_ref(v_kna_3988_);
lean_dec(v_generation_3986_);
v_a_4021_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4015_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4015_);
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
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec_ref(v_kp_3989_);
lean_dec_ref(v_kna_3988_);
lean_dec_ref(v_goal_3987_);
lean_dec(v_generation_3986_);
lean_dec_ref(v_prop_3985_);
lean_dec_ref(v_proof_3984_);
v_a_4030_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4008_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4008_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v_kp_3989_);
lean_dec_ref(v_kna_3988_);
lean_dec_ref(v_goal_3987_);
lean_dec(v_generation_3986_);
lean_dec_ref(v_prop_3985_);
lean_dec_ref(v_proof_3984_);
v_a_4038_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4000_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4000_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4046_, lean_object* v_prop_4047_, lean_object* v_generation_4048_, lean_object* v_goal_4049_, lean_object* v_kna_4050_, lean_object* v_kp_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4046_, v_prop_4047_, v_generation_4048_, v_goal_4049_, v_kna_4050_, v_kp_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4063_, lean_object* v_kna_4064_, lean_object* v_kp_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_toGoalState_4076_; uint8_t v_inconsistent_4077_; 
v_toGoalState_4076_ = lean_ctor_get(v_goal_4063_, 0);
lean_inc_ref(v_toGoalState_4076_);
v_inconsistent_4077_ = lean_ctor_get_uint8(v_toGoalState_4076_, sizeof(void*)*17);
if (v_inconsistent_4077_ == 0)
{
lean_object* v_mvarId_4078_; lean_object* v_nextDeclIdx_4079_; lean_object* v_enodeMap_4080_; lean_object* v_exprs_4081_; lean_object* v_parents_4082_; lean_object* v_congrTable_4083_; lean_object* v_appMap_4084_; lean_object* v_indicesFound_4085_; lean_object* v_newFacts_4086_; lean_object* v_nextIdx_4087_; lean_object* v_newRawFacts_4088_; lean_object* v_facts_4089_; lean_object* v_extThms_4090_; lean_object* v_ematch_4091_; lean_object* v_inj_4092_; lean_object* v_split_4093_; lean_object* v_clean_4094_; lean_object* v_sstates_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4133_; 
v_mvarId_4078_ = lean_ctor_get(v_goal_4063_, 1);
v_nextDeclIdx_4079_ = lean_ctor_get(v_toGoalState_4076_, 0);
v_enodeMap_4080_ = lean_ctor_get(v_toGoalState_4076_, 1);
v_exprs_4081_ = lean_ctor_get(v_toGoalState_4076_, 2);
v_parents_4082_ = lean_ctor_get(v_toGoalState_4076_, 3);
v_congrTable_4083_ = lean_ctor_get(v_toGoalState_4076_, 4);
v_appMap_4084_ = lean_ctor_get(v_toGoalState_4076_, 5);
v_indicesFound_4085_ = lean_ctor_get(v_toGoalState_4076_, 6);
v_newFacts_4086_ = lean_ctor_get(v_toGoalState_4076_, 7);
v_nextIdx_4087_ = lean_ctor_get(v_toGoalState_4076_, 8);
v_newRawFacts_4088_ = lean_ctor_get(v_toGoalState_4076_, 9);
v_facts_4089_ = lean_ctor_get(v_toGoalState_4076_, 10);
v_extThms_4090_ = lean_ctor_get(v_toGoalState_4076_, 11);
v_ematch_4091_ = lean_ctor_get(v_toGoalState_4076_, 12);
v_inj_4092_ = lean_ctor_get(v_toGoalState_4076_, 13);
v_split_4093_ = lean_ctor_get(v_toGoalState_4076_, 14);
v_clean_4094_ = lean_ctor_get(v_toGoalState_4076_, 15);
v_sstates_4095_ = lean_ctor_get(v_toGoalState_4076_, 16);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_toGoalState_4076_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4097_ = v_toGoalState_4076_;
v_isShared_4098_ = v_isSharedCheck_4133_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_sstates_4095_);
lean_inc(v_clean_4094_);
lean_inc(v_split_4093_);
lean_inc(v_inj_4092_);
lean_inc(v_ematch_4091_);
lean_inc(v_extThms_4090_);
lean_inc(v_facts_4089_);
lean_inc(v_newRawFacts_4088_);
lean_inc(v_nextIdx_4087_);
lean_inc(v_newFacts_4086_);
lean_inc(v_indicesFound_4085_);
lean_inc(v_appMap_4084_);
lean_inc(v_congrTable_4083_);
lean_inc(v_parents_4082_);
lean_inc(v_exprs_4081_);
lean_inc(v_enodeMap_4080_);
lean_inc(v_nextDeclIdx_4079_);
lean_dec(v_toGoalState_4076_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4133_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4088_);
if (lean_obj_tag(v___x_4099_) == 1)
{
lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4129_; 
lean_inc(v_mvarId_4078_);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_goal_4063_);
if (v_isSharedCheck_4129_ == 0)
{
lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4130_ = lean_ctor_get(v_goal_4063_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_goal_4063_, 0);
lean_dec(v_unused_4131_);
v___x_4101_ = v_goal_4063_;
v_isShared_4102_ = v_isSharedCheck_4129_;
goto v_resetjp_4100_;
}
else
{
lean_dec(v_goal_4063_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4129_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v_val_4103_; lean_object* v_fst_4104_; lean_object* v_snd_4105_; lean_object* v_proof_4106_; lean_object* v_prop_4107_; lean_object* v_generation_4108_; lean_object* v_splitSource_4109_; lean_object* v_ematchDiagSource_4110_; lean_object* v_simp_4111_; lean_object* v_simpMethods_4112_; lean_object* v_config_4113_; lean_object* v_anchorRefs_x3f_4114_; uint8_t v_cheapCases_4115_; uint8_t v_reportMVarIssue_4116_; lean_object* v_symPrios_4117_; lean_object* v_extensions_4118_; uint8_t v_debug_4119_; uint8_t v_ematchDiag_4120_; lean_object* v___x_4122_; 
v_val_4103_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v___x_4099_, 1);
v_fst_4104_ = lean_ctor_get(v_val_4103_, 0);
lean_inc(v_fst_4104_);
v_snd_4105_ = lean_ctor_get(v_val_4103_, 1);
lean_inc(v_snd_4105_);
lean_dec(v_val_4103_);
v_proof_4106_ = lean_ctor_get(v_fst_4104_, 0);
lean_inc_ref(v_proof_4106_);
v_prop_4107_ = lean_ctor_get(v_fst_4104_, 1);
lean_inc_ref(v_prop_4107_);
v_generation_4108_ = lean_ctor_get(v_fst_4104_, 2);
lean_inc(v_generation_4108_);
v_splitSource_4109_ = lean_ctor_get(v_fst_4104_, 3);
lean_inc(v_splitSource_4109_);
v_ematchDiagSource_4110_ = lean_ctor_get(v_fst_4104_, 4);
lean_inc(v_ematchDiagSource_4110_);
lean_dec(v_fst_4104_);
v_simp_4111_ = lean_ctor_get(v_a_4067_, 0);
v_simpMethods_4112_ = lean_ctor_get(v_a_4067_, 1);
v_config_4113_ = lean_ctor_get(v_a_4067_, 2);
v_anchorRefs_x3f_4114_ = lean_ctor_get(v_a_4067_, 3);
v_cheapCases_4115_ = lean_ctor_get_uint8(v_a_4067_, sizeof(void*)*8);
v_reportMVarIssue_4116_ = lean_ctor_get_uint8(v_a_4067_, sizeof(void*)*8 + 1);
v_symPrios_4117_ = lean_ctor_get(v_a_4067_, 6);
v_extensions_4118_ = lean_ctor_get(v_a_4067_, 7);
v_debug_4119_ = lean_ctor_get_uint8(v_a_4067_, sizeof(void*)*8 + 2);
v_ematchDiag_4120_ = lean_ctor_get_uint8(v_a_4067_, sizeof(void*)*8 + 3);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 9, v_snd_4105_);
v___x_4122_ = v___x_4097_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_nextDeclIdx_4079_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_enodeMap_4080_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_exprs_4081_);
lean_ctor_set(v_reuseFailAlloc_4128_, 3, v_parents_4082_);
lean_ctor_set(v_reuseFailAlloc_4128_, 4, v_congrTable_4083_);
lean_ctor_set(v_reuseFailAlloc_4128_, 5, v_appMap_4084_);
lean_ctor_set(v_reuseFailAlloc_4128_, 6, v_indicesFound_4085_);
lean_ctor_set(v_reuseFailAlloc_4128_, 7, v_newFacts_4086_);
lean_ctor_set(v_reuseFailAlloc_4128_, 8, v_nextIdx_4087_);
lean_ctor_set(v_reuseFailAlloc_4128_, 9, v_snd_4105_);
lean_ctor_set(v_reuseFailAlloc_4128_, 10, v_facts_4089_);
lean_ctor_set(v_reuseFailAlloc_4128_, 11, v_extThms_4090_);
lean_ctor_set(v_reuseFailAlloc_4128_, 12, v_ematch_4091_);
lean_ctor_set(v_reuseFailAlloc_4128_, 13, v_inj_4092_);
lean_ctor_set(v_reuseFailAlloc_4128_, 14, v_split_4093_);
lean_ctor_set(v_reuseFailAlloc_4128_, 15, v_clean_4094_);
lean_ctor_set(v_reuseFailAlloc_4128_, 16, v_sstates_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4128_, sizeof(void*)*17, v_inconsistent_4077_);
v___x_4122_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
lean_object* v_goal_4124_; 
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4122_);
v_goal_4124_ = v___x_4101_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4122_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_mvarId_4078_);
v_goal_4124_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_inc_ref(v_extensions_4118_);
lean_inc_ref(v_symPrios_4117_);
lean_inc(v_anchorRefs_x3f_4114_);
lean_inc_ref(v_config_4113_);
lean_inc_ref(v_simpMethods_4112_);
lean_inc_ref(v_simp_4111_);
v___x_4125_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_4125_, 0, v_simp_4111_);
lean_ctor_set(v___x_4125_, 1, v_simpMethods_4112_);
lean_ctor_set(v___x_4125_, 2, v_config_4113_);
lean_ctor_set(v___x_4125_, 3, v_anchorRefs_x3f_4114_);
lean_ctor_set(v___x_4125_, 4, v_splitSource_4109_);
lean_ctor_set(v___x_4125_, 5, v_ematchDiagSource_4110_);
lean_ctor_set(v___x_4125_, 6, v_symPrios_4117_);
lean_ctor_set(v___x_4125_, 7, v_extensions_4118_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*8, v_cheapCases_4115_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*8 + 1, v_reportMVarIssue_4116_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*8 + 2, v_debug_4119_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*8 + 3, v_ematchDiag_4120_);
v___x_4126_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4106_, v_prop_4107_, v_generation_4108_, v_goal_4124_, v_kna_4064_, v_kp_4065_, v_a_4066_, v___x_4125_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
lean_dec_ref_known(v___x_4125_, 8);
return v___x_4126_;
}
}
}
}
else
{
lean_object* v___x_4132_; 
lean_dec(v___x_4099_);
lean_del_object(v___x_4097_);
lean_dec_ref(v_sstates_4095_);
lean_dec_ref(v_clean_4094_);
lean_dec_ref(v_split_4093_);
lean_dec_ref(v_inj_4092_);
lean_dec_ref(v_ematch_4091_);
lean_dec_ref(v_extThms_4090_);
lean_dec_ref(v_facts_4089_);
lean_dec(v_nextIdx_4087_);
lean_dec_ref(v_newFacts_4086_);
lean_dec_ref(v_indicesFound_4085_);
lean_dec_ref(v_appMap_4084_);
lean_dec_ref(v_congrTable_4083_);
lean_dec_ref(v_parents_4082_);
lean_dec_ref(v_exprs_4081_);
lean_dec_ref(v_enodeMap_4080_);
lean_dec(v_nextDeclIdx_4079_);
lean_dec_ref(v_kp_4065_);
lean_inc(v_a_4074_);
lean_inc_ref(v_a_4073_);
lean_inc(v_a_4072_);
lean_inc_ref(v_a_4071_);
lean_inc(v_a_4070_);
lean_inc_ref(v_a_4069_);
lean_inc(v_a_4068_);
lean_inc_ref(v_a_4067_);
lean_inc(v_a_4066_);
v___x_4132_ = lean_apply_11(v_kna_4064_, v_goal_4063_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, lean_box(0));
return v___x_4132_;
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v_toGoalState_4076_);
lean_dec_ref(v_kp_4065_);
lean_dec_ref(v_kna_4064_);
lean_dec_ref(v_goal_4063_);
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4136_, lean_object* v_kna_4137_, lean_object* v_kp_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4136_, v_kna_4137_, v_kp_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_a_4139_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4150_, lean_object* v_kp_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4162_ = lean_unsigned_to_nat(1000000u);
v___x_4163_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4164_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4162_, v___x_4163_, v_a_4150_, v_kp_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4165_, lean_object* v_kp_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4165_, v_kp_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4178_, lean_object* v_kna_4179_, lean_object* v_kp_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4178_, v_kp_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4192_, lean_object* v_kna_4193_, lean_object* v_kp_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4192_, v_kna_4193_, v_kp_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_kna_4193_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4206_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4221_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4234_, lean_object* v___f_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_Meta_Grind_Action_andThen(v_a_4234_, v___f_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4250_, lean_object* v___f_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4250_, v___f_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4278_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4278_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4278_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___f_4273_; lean_object* v___f_4274_; lean_object* v___x_4276_; 
v___f_4273_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4274_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4274_, 0, v_a_4269_);
lean_closure_set(v___f_4274_, 1, v___f_4273_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___f_4274_);
v___x_4276_ = v___x_4271_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___f_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
else
{
return v___x_4268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4280_;
}
}
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
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
