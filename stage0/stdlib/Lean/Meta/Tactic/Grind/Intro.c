// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Injection import Lean.Meta.Tactic.Grind.Core import Lean.Meta.Tactic.Grind.RevertAll import Init.Grind.Util
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_8_);
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
lean_dec_ref(v_t_8_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = l_Lean_Meta_Grind_instInhabitedGoal_default;
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default;
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
lean_dec_ref(v___x_96_);
v___x_98_ = l_Lean_Meta_Sym_canon(v_val_97_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_99_, v_a_89_);
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
lean_dec_ref(v_name_170_);
v_searcher_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_string_utf8_byte_size(v_str_205_);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v_str_205_);
lean_ctor_set(v___x_227_, 1, v_searcher_225_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_227_, v_str_205_, v_searcher_225_, v___x_228_);
lean_dec_ref(v___x_227_);
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
lean_dec_ref(v___x_229_);
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
lean_dec_ref(v_suffix_211_);
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
v___x_218_ = lean_string_utf8_extract(v_str_205_, v___x_216_, v___y_207_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_284_; 
v_ks_259_ = lean_ctor_get(v_x_255_, 0);
v_vs_260_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_284_ == 0)
{
v___x_262_ = v_x_255_;
v_isShared_263_ = v_isSharedCheck_284_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_255_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_284_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_get_size(v_ks_259_);
v___x_265_ = lean_nat_dec_lt(v_x_256_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_x_256_);
v___x_266_ = lean_array_push(v_ks_259_, v_x_257_);
v___x_267_ = lean_array_push(v_vs_260_, v_x_258_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_267_);
lean_ctor_set(v___x_262_, 0, v___x_266_);
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
lean_object* v_k_x27_271_; uint8_t v___x_272_; 
v_k_x27_271_ = lean_array_fget_borrowed(v_ks_259_, v_x_256_);
v___x_272_ = lean_name_eq(v_x_257_, v_k_x27_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
if (v_isShared_263_ == 0)
{
v___x_274_ = v___x_262_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_vs_260_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_x_256_, v___x_275_);
lean_dec(v_x_256_);
v_x_255_ = v___x_274_;
v_x_256_ = v___x_276_;
goto _start;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_array_fset(v_ks_259_, v_x_256_, v_x_257_);
v___x_280_ = lean_array_fset(v_vs_260_, v_x_256_, v_x_258_);
lean_dec(v_x_256_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_280_);
lean_ctor_set(v___x_262_, 0, v___x_279_);
v___x_282_ = v___x_262_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_285_, lean_object* v_k_286_, lean_object* v_v_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_285_, v___x_288_, v_k_286_, v_v_287_);
return v___x_289_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_290_; uint64_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1723u);
v___x_291_ = lean_uint64_of_nat(v___x_290_);
return v___x_291_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; 
v___x_292_ = ((size_t)5ULL);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_shift_left(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; 
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_297_ = lean_usize_sub(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_299_, size_t v_x_300_, size_t v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v_es_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v_j_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_es_304_ = lean_ctor_get(v_x_299_, 0);
v___x_305_ = ((size_t)5ULL);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_308_ = lean_usize_land(v_x_300_, v___x_307_);
v_j_309_ = lean_usize_to_nat(v___x_308_);
v___x_310_ = lean_array_get_size(v_es_304_);
v___x_311_ = lean_nat_dec_lt(v_j_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v_j_309_);
lean_dec(v_x_303_);
lean_dec(v_x_302_);
return v_x_299_;
}
else
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_348_; 
lean_inc_ref(v_es_304_);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_x_299_, 0);
lean_dec(v_unused_349_);
v___x_313_ = v_x_299_;
v_isShared_314_ = v_isSharedCheck_348_;
goto v_resetjp_312_;
}
else
{
lean_dec(v_x_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_348_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_v_315_; lean_object* v___x_316_; lean_object* v_xs_x27_317_; lean_object* v___y_319_; 
v_v_315_ = lean_array_fget(v_es_304_, v_j_309_);
v___x_316_ = lean_box(0);
v_xs_x27_317_ = lean_array_fset(v_es_304_, v_j_309_, v___x_316_);
switch(lean_obj_tag(v_v_315_))
{
case 0:
{
lean_object* v_key_324_; lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_335_; 
v_key_324_ = lean_ctor_get(v_v_315_, 0);
v_val_325_ = lean_ctor_get(v_v_315_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_v_315_);
if (v_isSharedCheck_335_ == 0)
{
v___x_327_ = v_v_315_;
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_inc(v_key_324_);
lean_dec(v_v_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; 
v___x_329_ = lean_name_eq(v_x_302_, v_key_324_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_del_object(v___x_327_);
v___x_330_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_324_, v_val_325_, v_x_302_, v_x_303_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___y_319_ = v___x_331_;
goto v___jp_318_;
}
else
{
lean_object* v___x_333_; 
lean_dec(v_val_325_);
lean_dec(v_key_324_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_x_303_);
lean_ctor_set(v___x_327_, 0, v_x_302_);
v___x_333_ = v___x_327_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_x_303_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
v___y_319_ = v___x_333_;
goto v___jp_318_;
}
}
}
}
case 1:
{
lean_object* v_node_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_346_; 
v_node_336_ = lean_ctor_get(v_v_315_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_v_315_);
if (v_isSharedCheck_346_ == 0)
{
v___x_338_ = v_v_315_;
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_node_336_);
lean_dec(v_v_315_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_346_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_340_ = lean_usize_shift_right(v_x_300_, v___x_305_);
v___x_341_ = lean_usize_add(v_x_301_, v___x_306_);
v___x_342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_336_, v___x_340_, v___x_341_, v_x_302_, v_x_303_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_342_);
v___x_344_ = v___x_338_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
v___y_319_ = v___x_344_;
goto v___jp_318_;
}
}
}
default: 
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_x_302_);
lean_ctor_set(v___x_347_, 1, v_x_303_);
v___y_319_ = v___x_347_;
goto v___jp_318_;
}
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_array_fset(v_xs_x27_317_, v_j_309_, v___y_319_);
lean_dec(v_j_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_320_);
v___x_322_ = v___x_313_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
else
{
lean_object* v_ks_350_; lean_object* v_vs_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_371_; 
v_ks_350_ = lean_ctor_get(v_x_299_, 0);
v_vs_351_ = lean_ctor_get(v_x_299_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_371_ == 0)
{
v___x_353_ = v_x_299_;
v_isShared_354_ = v_isSharedCheck_371_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_vs_351_);
lean_inc(v_ks_350_);
lean_dec(v_x_299_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_371_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_ks_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_vs_351_);
v___x_356_ = v_reuseFailAlloc_370_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v_newNode_357_; uint8_t v___y_359_; size_t v___x_365_; uint8_t v___x_366_; 
v_newNode_357_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_356_, v_x_302_, v_x_303_);
v___x_365_ = ((size_t)7ULL);
v___x_366_ = lean_usize_dec_le(v___x_365_, v_x_301_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_357_);
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
lean_dec(v___x_367_);
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
else
{
v___y_359_ = v___x_366_;
goto v___jp_358_;
}
v___jp_358_:
{
if (v___y_359_ == 0)
{
lean_object* v_ks_360_; lean_object* v_vs_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_ks_360_ = lean_ctor_get(v_newNode_357_, 0);
lean_inc_ref(v_ks_360_);
v_vs_361_ = lean_ctor_get(v_newNode_357_, 1);
lean_inc_ref(v_vs_361_);
lean_dec_ref(v_newNode_357_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2);
v___x_364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_301_, v_ks_360_, v_vs_361_, v___x_362_, v___x_363_);
lean_dec_ref(v_vs_361_);
lean_dec_ref(v_ks_360_);
return v___x_364_;
}
else
{
return v_newNode_357_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_i_375_, lean_object* v_entries_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_array_get_size(v_keys_373_);
v___x_378_ = lean_nat_dec_lt(v_i_375_, v___x_377_);
if (v___x_378_ == 0)
{
lean_dec(v_i_375_);
return v_entries_376_;
}
else
{
lean_object* v_k_379_; lean_object* v_v_380_; uint64_t v___y_382_; 
v_k_379_ = lean_array_fget_borrowed(v_keys_373_, v_i_375_);
v_v_380_ = lean_array_fget_borrowed(v_vals_374_, v_i_375_);
if (lean_obj_tag(v_k_379_) == 0)
{
uint64_t v___x_393_; 
v___x_393_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_382_ = v___x_393_;
goto v___jp_381_;
}
else
{
uint64_t v_hash_394_; 
v_hash_394_ = lean_ctor_get_uint64(v_k_379_, sizeof(void*)*2);
v___y_382_ = v_hash_394_;
goto v___jp_381_;
}
v___jp_381_:
{
size_t v_h_383_; size_t v___x_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v_h_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_h_383_ = lean_uint64_to_usize(v___y_382_);
v___x_384_ = ((size_t)5ULL);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_sub(v_depth_372_, v___x_386_);
v___x_388_ = lean_usize_mul(v___x_384_, v___x_387_);
v_h_389_ = lean_usize_shift_right(v_h_383_, v___x_388_);
v___x_390_ = lean_nat_add(v_i_375_, v___x_385_);
lean_dec(v_i_375_);
lean_inc(v_v_380_);
lean_inc(v_k_379_);
v___x_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_376_, v_h_389_, v_depth_372_, v_k_379_, v_v_380_);
v_i_375_ = v___x_390_;
v_entries_376_ = v___x_391_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_395_, lean_object* v_keys_396_, lean_object* v_vals_397_, lean_object* v_i_398_, lean_object* v_entries_399_){
_start:
{
size_t v_depth_boxed_400_; lean_object* v_res_401_; 
v_depth_boxed_400_ = lean_unbox_usize(v_depth_395_);
lean_dec(v_depth_395_);
v_res_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_400_, v_keys_396_, v_vals_397_, v_i_398_, v_entries_399_);
lean_dec_ref(v_vals_397_);
lean_dec_ref(v_keys_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
size_t v_x_37000__boxed_407_; size_t v_x_37001__boxed_408_; lean_object* v_res_409_; 
v_x_37000__boxed_407_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_x_37001__boxed_408_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_res_409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_402_, v_x_37000__boxed_407_, v_x_37001__boxed_408_, v_x_405_, v_x_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint64_t v___y_414_; 
if (lean_obj_tag(v_x_411_) == 0)
{
uint64_t v___x_418_; 
v___x_418_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_414_ = v___x_418_;
goto v___jp_413_;
}
else
{
uint64_t v_hash_419_; 
v_hash_419_ = lean_ctor_get_uint64(v_x_411_, sizeof(void*)*2);
v___y_414_ = v_hash_419_;
goto v___jp_413_;
}
v___jp_413_:
{
size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_uint64_to_usize(v___y_414_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_410_, v___x_415_, v___x_416_, v_x_411_, v_x_412_);
return v___x_417_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_420_, lean_object* v_i_421_, lean_object* v_k_422_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_array_get_size(v_keys_420_);
v___x_424_ = lean_nat_dec_lt(v_i_421_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec(v_i_421_);
return v___x_424_;
}
else
{
lean_object* v_k_x27_425_; uint8_t v___x_426_; 
v_k_x27_425_ = lean_array_fget_borrowed(v_keys_420_, v_i_421_);
v___x_426_ = lean_name_eq(v_k_422_, v_k_x27_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_i_421_, v___x_427_);
lean_dec(v_i_421_);
v_i_421_ = v___x_428_;
goto _start;
}
else
{
lean_dec(v_i_421_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_430_, lean_object* v_i_431_, lean_object* v_k_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_430_, v_i_431_, v_k_432_);
lean_dec(v_k_432_);
lean_dec_ref(v_keys_430_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_435_, size_t v_x_436_, lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v_es_438_; lean_object* v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v_j_443_; lean_object* v___x_444_; 
v_es_438_ = lean_ctor_get(v_x_435_, 0);
v___x_439_ = lean_box(2);
v___x_440_ = ((size_t)5ULL);
v___x_441_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_442_ = lean_usize_land(v_x_436_, v___x_441_);
v_j_443_ = lean_usize_to_nat(v___x_442_);
v___x_444_ = lean_array_get_borrowed(v___x_439_, v_es_438_, v_j_443_);
lean_dec(v_j_443_);
switch(lean_obj_tag(v___x_444_))
{
case 0:
{
lean_object* v_key_445_; uint8_t v___x_446_; 
v_key_445_ = lean_ctor_get(v___x_444_, 0);
v___x_446_ = lean_name_eq(v_x_437_, v_key_445_);
return v___x_446_;
}
case 1:
{
lean_object* v_node_447_; size_t v___x_448_; 
v_node_447_ = lean_ctor_get(v___x_444_, 0);
v___x_448_ = lean_usize_shift_right(v_x_436_, v___x_440_);
v_x_435_ = v_node_447_;
v_x_436_ = v___x_448_;
goto _start;
}
default: 
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
}
}
else
{
lean_object* v_ks_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_ks_451_ = lean_ctor_get(v_x_435_, 0);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_451_, v___x_452_, v_x_437_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
size_t v_x_37205__boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v_x_37205__boxed_457_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_res_458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_454_, v_x_37205__boxed_457_, v_x_456_);
lean_dec(v_x_456_);
lean_dec_ref(v_x_454_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint64_t v___y_463_; 
if (lean_obj_tag(v_x_461_) == 0)
{
uint64_t v___x_466_; 
v___x_466_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_463_ = v___x_466_;
goto v___jp_462_;
}
else
{
uint64_t v_hash_467_; 
v_hash_467_ = lean_ctor_get_uint64(v_x_461_, sizeof(void*)*2);
v___y_463_ = v_hash_467_;
goto v___jp_462_;
}
v___jp_462_:
{
size_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_uint64_to_usize(v___y_463_);
v___x_465_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_460_, v___x_464_, v_x_461_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec_ref(v_x_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; lean_object* v_toGoalState_477_; lean_object* v_clean_478_; lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_496_; 
v___x_476_ = lean_st_ref_get(v___y_474_);
v_toGoalState_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc_ref(v_toGoalState_477_);
lean_dec(v___x_476_);
v_clean_478_ = lean_ctor_get(v_toGoalState_477_, 15);
lean_inc_ref(v_clean_478_);
lean_dec_ref(v_toGoalState_477_);
v_snd_479_ = lean_ctor_get(v_b_473_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_b_473_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_b_473_, 0);
lean_dec(v_unused_497_);
v___x_481_ = v_b_473_;
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_dec(v_b_473_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_496_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_used_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_used_483_ = lean_ctor_get(v_clean_478_, 0);
lean_inc_ref(v_used_483_);
lean_dec_ref(v_clean_478_);
lean_inc(v_snd_479_);
lean_inc(v_a_472_);
v___x_484_ = lean_name_append_index_after(v_a_472_, v_snd_479_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_snd_479_, v___x_485_);
lean_dec(v_snd_479_);
v___x_487_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_483_, v___x_484_);
lean_dec_ref(v_used_483_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_a_472_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_486_);
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_489_ = v___x_481_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_486_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_486_);
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_493_ = v___x_481_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_486_);
v___x_493_ = v_reuseFailAlloc_495_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_b_473_ = v___x_493_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_498_, v_b_499_, v___y_500_);
lean_dec(v___y_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_i_505_, lean_object* v_k_506_){
_start:
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_array_get_size(v_keys_503_);
v___x_508_ = lean_nat_dec_lt(v_i_505_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec(v_i_505_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v_k_x27_510_; uint8_t v___x_511_; 
v_k_x27_510_ = lean_array_fget_borrowed(v_keys_503_, v_i_505_);
v___x_511_ = lean_name_eq(v_k_506_, v_k_x27_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_i_505_, v___x_512_);
lean_dec(v_i_505_);
v_i_505_ = v___x_513_;
goto _start;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_fget_borrowed(v_vals_504_, v_i_505_);
lean_dec(v_i_505_);
lean_inc(v___x_515_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_i_519_, lean_object* v_k_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_517_, v_vals_518_, v_i_519_, v_k_520_);
lean_dec(v_k_520_);
lean_dec_ref(v_vals_518_);
lean_dec_ref(v_keys_517_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_522_, size_t v_x_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_es_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_546_; 
v_es_525_ = lean_ctor_get(v_x_522_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_546_ == 0)
{
v___x_527_ = v_x_522_;
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_es_525_);
lean_dec(v_x_522_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v_j_533_; lean_object* v___x_534_; 
v___x_529_ = lean_box(2);
v___x_530_ = ((size_t)5ULL);
v___x_531_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_532_ = lean_usize_land(v_x_523_, v___x_531_);
v_j_533_ = lean_usize_to_nat(v___x_532_);
v___x_534_ = lean_array_get(v___x_529_, v_es_525_, v_j_533_);
lean_dec(v_j_533_);
lean_dec_ref(v_es_525_);
switch(lean_obj_tag(v___x_534_))
{
case 0:
{
lean_object* v_key_535_; lean_object* v_val_536_; uint8_t v___x_537_; 
v_key_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_key_535_);
v_val_536_ = lean_ctor_get(v___x_534_, 1);
lean_inc(v_val_536_);
lean_dec_ref(v___x_534_);
v___x_537_ = lean_name_eq(v_x_524_, v_key_535_);
lean_dec(v_key_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec(v_val_536_);
lean_del_object(v___x_527_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
lean_object* v___x_540_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 1);
lean_ctor_set(v___x_527_, 0, v_val_536_);
v___x_540_ = v___x_527_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_val_536_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
case 1:
{
lean_object* v_node_542_; size_t v___x_543_; 
lean_del_object(v___x_527_);
v_node_542_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_node_542_);
lean_dec_ref(v___x_534_);
v___x_543_ = lean_usize_shift_right(v_x_523_, v___x_530_);
v_x_522_ = v_node_542_;
v_x_523_ = v___x_543_;
goto _start;
}
default: 
{
lean_object* v___x_545_; 
lean_del_object(v___x_527_);
v___x_545_ = lean_box(0);
return v___x_545_;
}
}
}
}
else
{
lean_object* v_ks_547_; lean_object* v_vs_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_ks_547_ = lean_ctor_get(v_x_522_, 0);
lean_inc_ref(v_ks_547_);
v_vs_548_ = lean_ctor_get(v_x_522_, 1);
lean_inc_ref(v_vs_548_);
lean_dec_ref(v_x_522_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_547_, v_vs_548_, v___x_549_, v_x_524_);
lean_dec_ref(v_vs_548_);
lean_dec_ref(v_ks_547_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
size_t v_x_37336__boxed_554_; lean_object* v_res_555_; 
v_x_37336__boxed_554_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_551_, v_x_37336__boxed_554_, v_x_553_);
lean_dec(v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
uint64_t v___y_559_; 
if (lean_obj_tag(v_x_557_) == 0)
{
uint64_t v___x_562_; 
v___x_562_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_559_ = v___x_562_;
goto v___jp_558_;
}
else
{
uint64_t v_hash_563_; 
v_hash_563_ = lean_ctor_get_uint64(v_x_557_, sizeof(void*)*2);
v___y_559_ = v_hash_563_;
goto v___jp_558_;
}
v___jp_558_:
{
size_t v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_uint64_to_usize(v___y_559_);
v___x_561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_556_, v___x_560_, v_x_557_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_564_, v_x_565_);
lean_dec(v_x_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_570_, lean_object* v_type_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_name_584_; lean_object* v___y_585_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_name_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_574_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_798_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_798_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_798_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_798_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v_clean_763_; 
v_clean_763_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*11 + 16);
lean_dec(v_a_738_);
if (v_clean_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_570_);
if (lean_obj_tag(v___x_764_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_767_; 
lean_dec_ref(v_type_571_);
lean_dec(v_name_570_);
v_val_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v___x_764_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_val_765_);
v___x_767_ = v___x_740_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_val_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
uint8_t v___x_769_; 
lean_dec(v___x_764_);
v___x_769_ = l_Lean_Name_hasMacroScopes(v_name_570_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_del_object(v___x_740_);
lean_dec_ref(v_type_571_);
v___x_770_ = l_Lean_Core_mkFreshUserName(v_name_570_, v_a_580_, v_a_581_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
lean_inc(v_name_570_);
v___x_771_ = lean_erase_macro_scopes(v_name_570_);
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_773_ = lean_name_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_775_ = lean_name_eq(v___x_771_, v___x_774_);
lean_dec(v___x_771_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; 
lean_dec_ref(v_type_571_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_name_570_);
v___x_777_ = v___x_740_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_name_570_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_del_object(v___x_740_);
goto v___jp_742_;
}
}
else
{
lean_dec(v___x_771_);
lean_del_object(v___x_740_);
goto v___jp_742_;
}
}
}
}
else
{
uint8_t v___x_779_; 
lean_del_object(v___x_740_);
v___x_779_ = l_Lean_Name_hasMacroScopes(v_name_570_);
if (v___x_779_ == 0)
{
v_name_712_ = v_name_570_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
v___y_717_ = v_a_576_;
v___y_718_ = v_a_577_;
v___y_719_ = v_a_578_;
v___y_720_ = v_a_579_;
v___y_721_ = v_a_580_;
v___y_722_ = v_a_581_;
goto v___jp_711_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_780_ = lean_erase_macro_scopes(v_name_570_);
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_795_ = lean_name_eq(v___x_780_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_797_ = lean_name_eq(v___x_780_, v___x_796_);
if (v___x_797_ == 0)
{
v_name_712_ = v___x_780_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
v___y_717_ = v_a_576_;
v___y_718_ = v_a_577_;
v___y_719_ = v_a_578_;
v___y_720_ = v_a_579_;
v___y_721_ = v_a_580_;
v___y_722_ = v_a_581_;
goto v___jp_711_;
}
else
{
goto v___jp_781_;
}
}
else
{
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_782_; 
lean_inc_ref(v_type_571_);
v___x_782_ = l_Lean_Meta_isProp(v_type_571_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = lean_unbox(v_a_783_);
lean_dec(v_a_783_);
if (v___x_784_ == 0)
{
v_name_712_ = v___x_780_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
v___y_717_ = v_a_576_;
v___y_718_ = v_a_577_;
v___y_719_ = v_a_578_;
v___y_720_ = v_a_579_;
v___y_721_ = v_a_580_;
v___y_722_ = v_a_581_;
goto v___jp_711_;
}
else
{
lean_object* v___x_785_; 
lean_dec(v___x_780_);
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_712_ = v___x_785_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
v___y_717_ = v_a_576_;
v___y_718_ = v_a_577_;
v___y_719_ = v_a_578_;
v___y_720_ = v_a_579_;
v___y_721_ = v_a_580_;
v___y_722_ = v_a_581_;
goto v___jp_711_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___x_780_);
lean_dec_ref(v_type_571_);
v_a_786_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_782_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
v___jp_742_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_isProp(v_type_571_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_754_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; 
v___x_748_ = lean_unbox(v_a_744_);
lean_dec(v_a_744_);
if (v___x_748_ == 0)
{
lean_object* v___x_750_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v_name_570_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_name_570_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_del_object(v___x_746_);
lean_dec(v_name_570_);
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_753_ = l_Lean_Core_mkFreshUserName(v___x_752_, v_a_580_, v_a_581_);
return v___x_753_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_name_570_);
v_a_755_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_743_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_743_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_type_571_);
lean_dec(v_name_570_);
v_a_799_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_737_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_737_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
v___jp_583_:
{
lean_object* v___x_586_; lean_object* v_toGoalState_587_; lean_object* v_clean_588_; lean_object* v_mvarId_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_634_; 
v___x_586_ = lean_st_ref_take(v___y_585_);
v_toGoalState_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc_ref(v_toGoalState_587_);
v_clean_588_ = lean_ctor_get(v_toGoalState_587_, 15);
lean_inc_ref(v_clean_588_);
v_mvarId_589_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_635_);
v___x_591_ = v___x_586_;
v_isShared_592_ = v_isSharedCheck_634_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_mvarId_589_);
lean_dec(v___x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_634_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_nextDeclIdx_593_; lean_object* v_enodeMap_594_; lean_object* v_exprs_595_; lean_object* v_parents_596_; lean_object* v_congrTable_597_; lean_object* v_appMap_598_; lean_object* v_indicesFound_599_; lean_object* v_newFacts_600_; uint8_t v_inconsistent_601_; lean_object* v_nextIdx_602_; lean_object* v_newRawFacts_603_; lean_object* v_facts_604_; lean_object* v_extThms_605_; lean_object* v_ematch_606_; lean_object* v_inj_607_; lean_object* v_split_608_; lean_object* v_sstates_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_632_; 
v_nextDeclIdx_593_ = lean_ctor_get(v_toGoalState_587_, 0);
v_enodeMap_594_ = lean_ctor_get(v_toGoalState_587_, 1);
v_exprs_595_ = lean_ctor_get(v_toGoalState_587_, 2);
v_parents_596_ = lean_ctor_get(v_toGoalState_587_, 3);
v_congrTable_597_ = lean_ctor_get(v_toGoalState_587_, 4);
v_appMap_598_ = lean_ctor_get(v_toGoalState_587_, 5);
v_indicesFound_599_ = lean_ctor_get(v_toGoalState_587_, 6);
v_newFacts_600_ = lean_ctor_get(v_toGoalState_587_, 7);
v_inconsistent_601_ = lean_ctor_get_uint8(v_toGoalState_587_, sizeof(void*)*17);
v_nextIdx_602_ = lean_ctor_get(v_toGoalState_587_, 8);
v_newRawFacts_603_ = lean_ctor_get(v_toGoalState_587_, 9);
v_facts_604_ = lean_ctor_get(v_toGoalState_587_, 10);
v_extThms_605_ = lean_ctor_get(v_toGoalState_587_, 11);
v_ematch_606_ = lean_ctor_get(v_toGoalState_587_, 12);
v_inj_607_ = lean_ctor_get(v_toGoalState_587_, 13);
v_split_608_ = lean_ctor_get(v_toGoalState_587_, 14);
v_sstates_609_ = lean_ctor_get(v_toGoalState_587_, 16);
v_isSharedCheck_632_ = !lean_is_exclusive(v_toGoalState_587_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_toGoalState_587_, 15);
lean_dec(v_unused_633_);
v___x_611_ = v_toGoalState_587_;
v_isShared_612_ = v_isSharedCheck_632_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_sstates_609_);
lean_inc(v_split_608_);
lean_inc(v_inj_607_);
lean_inc(v_ematch_606_);
lean_inc(v_extThms_605_);
lean_inc(v_facts_604_);
lean_inc(v_newRawFacts_603_);
lean_inc(v_nextIdx_602_);
lean_inc(v_newFacts_600_);
lean_inc(v_indicesFound_599_);
lean_inc(v_appMap_598_);
lean_inc(v_congrTable_597_);
lean_inc(v_parents_596_);
lean_inc(v_exprs_595_);
lean_inc(v_enodeMap_594_);
lean_inc(v_nextDeclIdx_593_);
lean_dec(v_toGoalState_587_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_632_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_used_613_; lean_object* v_next_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_631_; 
v_used_613_ = lean_ctor_get(v_clean_588_, 0);
v_next_614_ = lean_ctor_get(v_clean_588_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_clean_588_);
if (v_isSharedCheck_631_ == 0)
{
v___x_616_ = v_clean_588_;
v_isShared_617_ = v_isSharedCheck_631_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_next_614_);
lean_inc(v_used_613_);
lean_dec(v_clean_588_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_631_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = lean_box(0);
lean_inc(v_name_584_);
v___x_619_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_613_, v_name_584_, v___x_618_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_next_614_);
v___x_621_ = v_reuseFailAlloc_630_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 15, v___x_621_);
v___x_623_ = v___x_611_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_nextDeclIdx_593_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_enodeMap_594_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_exprs_595_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_parents_596_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_congrTable_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_appMap_598_);
lean_ctor_set(v_reuseFailAlloc_629_, 6, v_indicesFound_599_);
lean_ctor_set(v_reuseFailAlloc_629_, 7, v_newFacts_600_);
lean_ctor_set(v_reuseFailAlloc_629_, 8, v_nextIdx_602_);
lean_ctor_set(v_reuseFailAlloc_629_, 9, v_newRawFacts_603_);
lean_ctor_set(v_reuseFailAlloc_629_, 10, v_facts_604_);
lean_ctor_set(v_reuseFailAlloc_629_, 11, v_extThms_605_);
lean_ctor_set(v_reuseFailAlloc_629_, 12, v_ematch_606_);
lean_ctor_set(v_reuseFailAlloc_629_, 13, v_inj_607_);
lean_ctor_set(v_reuseFailAlloc_629_, 14, v_split_608_);
lean_ctor_set(v_reuseFailAlloc_629_, 15, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_629_, 16, v_sstates_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_629_, sizeof(void*)*17, v_inconsistent_601_);
v___x_623_ = v_reuseFailAlloc_629_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_623_);
v___x_625_ = v___x_591_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_mvarId_589_);
v___x_625_ = v_reuseFailAlloc_628_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_st_ref_set(v___y_585_, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_name_584_);
return v___x_627_;
}
}
}
}
}
}
}
v___jp_636_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_645_);
lean_ctor_set(v___x_650_, 1, v___y_649_);
lean_inc(v___y_639_);
v___x_651_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_639_, v___x_650_, v___y_638_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v_toGoalState_654_; lean_object* v_clean_655_; lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v_mvarId_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_701_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v___x_653_ = lean_st_ref_take(v___y_638_);
v_toGoalState_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_toGoalState_654_);
v_clean_655_ = lean_ctor_get(v_toGoalState_654_, 15);
lean_inc_ref(v_clean_655_);
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_656_);
v_snd_657_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_657_);
lean_dec(v_a_652_);
v_mvarId_658_ = lean_ctor_get(v___x_653_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_653_, 0);
lean_dec(v_unused_702_);
v___x_660_ = v___x_653_;
v_isShared_661_ = v_isSharedCheck_701_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_mvarId_658_);
lean_dec(v___x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_701_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_nextDeclIdx_662_; lean_object* v_enodeMap_663_; lean_object* v_exprs_664_; lean_object* v_parents_665_; lean_object* v_congrTable_666_; lean_object* v_appMap_667_; lean_object* v_indicesFound_668_; lean_object* v_newFacts_669_; uint8_t v_inconsistent_670_; lean_object* v_nextIdx_671_; lean_object* v_newRawFacts_672_; lean_object* v_facts_673_; lean_object* v_extThms_674_; lean_object* v_ematch_675_; lean_object* v_inj_676_; lean_object* v_split_677_; lean_object* v_sstates_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_699_; 
v_nextDeclIdx_662_ = lean_ctor_get(v_toGoalState_654_, 0);
v_enodeMap_663_ = lean_ctor_get(v_toGoalState_654_, 1);
v_exprs_664_ = lean_ctor_get(v_toGoalState_654_, 2);
v_parents_665_ = lean_ctor_get(v_toGoalState_654_, 3);
v_congrTable_666_ = lean_ctor_get(v_toGoalState_654_, 4);
v_appMap_667_ = lean_ctor_get(v_toGoalState_654_, 5);
v_indicesFound_668_ = lean_ctor_get(v_toGoalState_654_, 6);
v_newFacts_669_ = lean_ctor_get(v_toGoalState_654_, 7);
v_inconsistent_670_ = lean_ctor_get_uint8(v_toGoalState_654_, sizeof(void*)*17);
v_nextIdx_671_ = lean_ctor_get(v_toGoalState_654_, 8);
v_newRawFacts_672_ = lean_ctor_get(v_toGoalState_654_, 9);
v_facts_673_ = lean_ctor_get(v_toGoalState_654_, 10);
v_extThms_674_ = lean_ctor_get(v_toGoalState_654_, 11);
v_ematch_675_ = lean_ctor_get(v_toGoalState_654_, 12);
v_inj_676_ = lean_ctor_get(v_toGoalState_654_, 13);
v_split_677_ = lean_ctor_get(v_toGoalState_654_, 14);
v_sstates_678_ = lean_ctor_get(v_toGoalState_654_, 16);
v_isSharedCheck_699_ = !lean_is_exclusive(v_toGoalState_654_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_toGoalState_654_, 15);
lean_dec(v_unused_700_);
v___x_680_ = v_toGoalState_654_;
v_isShared_681_ = v_isSharedCheck_699_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_sstates_678_);
lean_inc(v_split_677_);
lean_inc(v_inj_676_);
lean_inc(v_ematch_675_);
lean_inc(v_extThms_674_);
lean_inc(v_facts_673_);
lean_inc(v_newRawFacts_672_);
lean_inc(v_nextIdx_671_);
lean_inc(v_newFacts_669_);
lean_inc(v_indicesFound_668_);
lean_inc(v_appMap_667_);
lean_inc(v_congrTable_666_);
lean_inc(v_parents_665_);
lean_inc(v_exprs_664_);
lean_inc(v_enodeMap_663_);
lean_inc(v_nextDeclIdx_662_);
lean_dec(v_toGoalState_654_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_699_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_used_682_; lean_object* v_next_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_698_; 
v_used_682_ = lean_ctor_get(v_clean_655_, 0);
v_next_683_ = lean_ctor_get(v_clean_655_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_clean_655_);
if (v_isSharedCheck_698_ == 0)
{
v___x_685_ = v_clean_655_;
v_isShared_686_ = v_isSharedCheck_698_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_next_683_);
lean_inc(v_used_682_);
lean_dec(v_clean_655_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_698_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_683_, v___y_639_, v_snd_657_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_used_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_697_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 15, v___x_689_);
v___x_691_ = v___x_680_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_nextDeclIdx_662_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_enodeMap_663_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_exprs_664_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_parents_665_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_congrTable_666_);
lean_ctor_set(v_reuseFailAlloc_696_, 5, v_appMap_667_);
lean_ctor_set(v_reuseFailAlloc_696_, 6, v_indicesFound_668_);
lean_ctor_set(v_reuseFailAlloc_696_, 7, v_newFacts_669_);
lean_ctor_set(v_reuseFailAlloc_696_, 8, v_nextIdx_671_);
lean_ctor_set(v_reuseFailAlloc_696_, 9, v_newRawFacts_672_);
lean_ctor_set(v_reuseFailAlloc_696_, 10, v_facts_673_);
lean_ctor_set(v_reuseFailAlloc_696_, 11, v_extThms_674_);
lean_ctor_set(v_reuseFailAlloc_696_, 12, v_ematch_675_);
lean_ctor_set(v_reuseFailAlloc_696_, 13, v_inj_676_);
lean_ctor_set(v_reuseFailAlloc_696_, 14, v_split_677_);
lean_ctor_set(v_reuseFailAlloc_696_, 15, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_696_, 16, v_sstates_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_696_, sizeof(void*)*17, v_inconsistent_670_);
v___x_691_ = v_reuseFailAlloc_696_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_691_);
v___x_693_ = v___x_660_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_mvarId_658_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; 
v___x_694_ = lean_st_ref_set(v___y_638_, v___x_693_);
v_name_584_ = v_fst_656_;
v___y_585_ = v___y_638_;
goto v___jp_583_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___y_639_);
v_a_703_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_651_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_651_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
v___jp_711_:
{
lean_object* v___x_723_; lean_object* v_toGoalState_724_; lean_object* v_clean_725_; lean_object* v_used_726_; uint8_t v___x_727_; 
v___x_723_ = lean_st_ref_get(v___y_713_);
v_toGoalState_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc_ref(v_toGoalState_724_);
lean_dec(v___x_723_);
v_clean_725_ = lean_ctor_get(v_toGoalState_724_, 15);
lean_inc_ref(v_clean_725_);
lean_dec_ref(v_toGoalState_724_);
v_used_726_ = lean_ctor_get(v_clean_725_, 0);
lean_inc_ref(v_used_726_);
lean_dec_ref(v_clean_725_);
v___x_727_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_726_, v_name_712_);
lean_dec_ref(v_used_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v_type_571_);
v_name_584_ = v_name_712_;
v___y_585_ = v___y_713_;
goto v___jp_583_;
}
else
{
lean_object* v___x_728_; 
lean_inc(v_name_712_);
v___x_728_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_712_, v_type_571_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v_toGoalState_731_; lean_object* v_clean_732_; lean_object* v_next_733_; lean_object* v___x_734_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_728_);
v___x_730_ = lean_st_ref_get(v___y_713_);
v_toGoalState_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_toGoalState_731_);
lean_dec(v___x_730_);
v_clean_732_ = lean_ctor_get(v_toGoalState_731_, 15);
lean_inc_ref(v_clean_732_);
lean_dec_ref(v_toGoalState_731_);
v_next_733_ = lean_ctor_get(v_clean_732_, 1);
lean_inc_ref(v_next_733_);
lean_dec_ref(v_clean_732_);
v___x_734_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_733_, v_a_729_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref(v___x_734_);
v___y_637_ = v___y_721_;
v___y_638_ = v___y_713_;
v___y_639_ = v_a_729_;
v___y_640_ = v___y_716_;
v___y_641_ = v___y_715_;
v___y_642_ = v___y_722_;
v___y_643_ = v___y_717_;
v___y_644_ = v___y_714_;
v___y_645_ = v_name_712_;
v___y_646_ = v___y_719_;
v___y_647_ = v___y_718_;
v___y_648_ = v___y_720_;
v___y_649_ = v_val_735_;
goto v___jp_636_;
}
else
{
lean_object* v___x_736_; 
lean_dec(v___x_734_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___y_637_ = v___y_721_;
v___y_638_ = v___y_713_;
v___y_639_ = v_a_729_;
v___y_640_ = v___y_716_;
v___y_641_ = v___y_715_;
v___y_642_ = v___y_722_;
v___y_643_ = v___y_717_;
v___y_644_ = v___y_714_;
v___y_645_ = v_name_712_;
v___y_646_ = v___y_719_;
v___y_647_ = v___y_718_;
v___y_648_ = v___y_720_;
v___y_649_ = v___x_736_;
goto v___jp_636_;
}
}
else
{
lean_dec(v_name_712_);
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_807_, lean_object* v_type_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_807_, v_type_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_822_, v_x_823_, v_x_824_);
return v___x_825_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_827_, v_x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_830_, v_x_831_, v_x_832_);
lean_dec(v_x_832_);
lean_dec_ref(v_x_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_835_, v_b_836_, v___y_837_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_849_, v_b_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_867_, v_x_868_, v_x_869_);
lean_dec(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, size_t v_x_873_, size_t v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_872_, v_x_873_, v_x_874_, v_x_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_37844__boxed_884_; size_t v_x_37845__boxed_885_; lean_object* v_res_886_; 
v_x_37844__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_x_37845__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_878_, v_x_879_, v_x_37844__boxed_884_, v_x_37845__boxed_885_, v_x_882_, v_x_883_);
return v_res_886_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, size_t v_x_889_, lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_888_, v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
size_t v_x_37861__boxed_896_; uint8_t v_res_897_; lean_object* v_r_898_; 
v_x_37861__boxed_896_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_res_897_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_892_, v_x_893_, v_x_37861__boxed_896_, v_x_895_);
lean_dec(v_x_895_);
lean_dec_ref(v_x_893_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, size_t v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_900_, v_x_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
size_t v_x_37872__boxed_908_; lean_object* v_res_909_; 
v_x_37872__boxed_908_ = lean_unbox_usize(v_x_906_);
lean_dec(v_x_906_);
v_res_909_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_904_, v_x_905_, v_x_37872__boxed_908_, v_x_907_);
lean_dec(v_x_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_910_, lean_object* v_n_911_, lean_object* v_k_912_, lean_object* v_v_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_911_, v_k_912_, v_v_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_915_, size_t v_depth_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_heq_919_, lean_object* v_i_920_, lean_object* v_entries_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_916_, v_keys_917_, v_vals_918_, v_i_920_, v_entries_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_923_, lean_object* v_depth_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_entries_929_){
_start:
{
size_t v_depth_boxed_930_; lean_object* v_res_931_; 
v_depth_boxed_930_ = lean_unbox_usize(v_depth_924_);
lean_dec(v_depth_924_);
v_res_931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_923_, v_depth_boxed_930_, v_keys_925_, v_vals_926_, v_heq_927_, v_i_928_, v_entries_929_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_932_, lean_object* v_keys_933_, lean_object* v_vals_934_, lean_object* v_heq_935_, lean_object* v_i_936_, lean_object* v_k_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_933_, v_i_936_, v_k_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_heq_942_, lean_object* v_i_943_, lean_object* v_k_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_939_, v_keys_940_, v_vals_941_, v_heq_942_, v_i_943_, v_k_944_);
lean_dec(v_k_944_);
lean_dec_ref(v_vals_941_);
lean_dec_ref(v_keys_940_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_947_, lean_object* v_keys_948_, lean_object* v_vals_949_, lean_object* v_heq_950_, lean_object* v_i_951_, lean_object* v_k_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_948_, v_vals_949_, v_i_951_, v_k_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_954_, lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_heq_957_, lean_object* v_i_958_, lean_object* v_k_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_954_, v_keys_955_, v_vals_956_, v_heq_957_, v_i_958_, v_k_959_);
lean_dec(v_k_959_);
lean_dec_ref(v_vals_956_);
lean_dec_ref(v_keys_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_962_, v_x_963_, v_x_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_env_974_; lean_object* v___x_975_; lean_object* v_mctx_976_; lean_object* v_lctx_977_; lean_object* v_options_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_973_ = lean_st_ref_get(v___y_971_);
v_env_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_env_974_);
lean_dec(v___x_973_);
v___x_975_ = lean_st_ref_get(v___y_969_);
v_mctx_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_mctx_976_);
lean_dec(v___x_975_);
v_lctx_977_ = lean_ctor_get(v___y_968_, 2);
v_options_978_ = lean_ctor_get(v___y_970_, 2);
lean_inc_ref(v_options_978_);
lean_inc_ref(v_lctx_977_);
v___x_979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_979_, 0, v_env_974_);
lean_ctor_set(v___x_979_, 1, v_mctx_976_);
lean_ctor_set(v___x_979_, 2, v_lctx_977_);
lean_ctor_set(v___x_979_, 3, v_options_978_);
v___x_980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_msgData_967_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_ref_995_; lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
v_ref_995_ = lean_ctor_get(v___y_992_, 5);
v___x_996_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_inc(v_ref_995_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_ref_995_);
lean_ctor_set(v___x_1001_, 1, v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 1);
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___x_1082_; lean_object* v_mvarId_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_st_ref_get(v_a_1016_);
v_mvarId_1083_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_mvarId_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = l_Lean_MVarId_getType(v_mvarId_1083_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
switch(lean_obj_tag(v_a_1085_))
{
case 7:
{
lean_object* v_binderName_1086_; lean_object* v_binderType_1087_; 
v_binderName_1086_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_binderName_1086_);
v_binderType_1087_ = lean_ctor_get(v_a_1085_, 1);
lean_inc_ref(v_binderType_1087_);
lean_dec_ref(v_a_1085_);
v_fst_1028_ = v_binderName_1086_;
v_snd_1029_ = v_binderType_1087_;
v___y_1030_ = v_a_1016_;
v___y_1031_ = v_a_1017_;
v___y_1032_ = v_a_1018_;
v___y_1033_ = v_a_1019_;
v___y_1034_ = v_a_1020_;
v___y_1035_ = v_a_1021_;
v___y_1036_ = v_a_1022_;
v___y_1037_ = v_a_1023_;
v___y_1038_ = v_a_1024_;
v___y_1039_ = v_a_1025_;
goto v___jp_1027_;
}
case 8:
{
lean_object* v_declName_1088_; lean_object* v_type_1089_; 
v_declName_1088_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_declName_1088_);
v_type_1089_ = lean_ctor_get(v_a_1085_, 1);
lean_inc_ref(v_type_1089_);
lean_dec_ref(v_a_1085_);
v_fst_1028_ = v_declName_1088_;
v_snd_1029_ = v_type_1089_;
v___y_1030_ = v_a_1016_;
v___y_1031_ = v_a_1017_;
v___y_1032_ = v_a_1018_;
v___y_1033_ = v_a_1019_;
v___y_1034_ = v_a_1020_;
v___y_1035_ = v_a_1021_;
v___y_1036_ = v_a_1022_;
v___y_1037_ = v_a_1023_;
v___y_1038_ = v_a_1024_;
v___y_1039_ = v_a_1025_;
goto v___jp_1027_;
}
default: 
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1085_);
v___x_1090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1091_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1090_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1084_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1084_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_1027_:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1028_, v_snd_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v_mvarId_1043_; lean_object* v___x_1044_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = lean_st_ref_get(v___y_1030_);
v_mvarId_1043_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_mvarId_1043_);
lean_dec(v___x_1042_);
v___x_1044_ = l_Lean_MVarId_intro(v_mvarId_1043_, v_a_1041_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1065_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1065_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1065_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1051_; lean_object* v_toGoalState_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1063_; 
v_fst_1049_ = lean_ctor_get(v_a_1045_, 0);
lean_inc(v_fst_1049_);
v_snd_1050_ = lean_ctor_get(v_a_1045_, 1);
lean_inc(v_snd_1050_);
lean_dec(v_a_1045_);
v___x_1051_ = lean_st_ref_take(v___y_1030_);
v_toGoalState_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1051_, 1);
lean_dec(v_unused_1064_);
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_toGoalState_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_snd_1050_);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_toGoalState_1052_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_snd_1050_);
v___x_1057_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_st_ref_set(v___y_1030_, v___x_1057_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v_fst_1049_);
v___x_1060_ = v___x_1047_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_fst_1049_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1044_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1044_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1040_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1040_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec(v_a_1108_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1120_, lean_object* v_msg_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1121_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1134_, v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec(v___y_1136_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v___y_1150_);
lean_inc(v___y_1149_);
v___x_1160_ = lean_apply_11(v_x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, lean_box(0));
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec(v___y_1162_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___f_1187_; lean_object* v___x_1188_; 
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc(v___y_1176_);
v___f_1187_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1187_, 0, v_x_1175_);
lean_closure_set(v___f_1187_, 1, v___y_1176_);
lean_closure_set(v___f_1187_, 2, v___y_1177_);
lean_closure_set(v___f_1187_, 3, v___y_1178_);
lean_closure_set(v___f_1187_, 4, v___y_1179_);
lean_closure_set(v___f_1187_, 5, v___y_1180_);
lean_closure_set(v___f_1187_, 6, v___y_1181_);
v___x_1188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1174_, v___f_1187_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1197_, v_x_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1211_, lean_object* v_mvarId_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1212_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_mvarId_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1226_, v_mvarId_1227_, v_x_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v___y_1229_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
v___x_1252_ = lean_apply_10(v_x_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, lean_box(0));
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___f_1277_; lean_object* v___x_1278_; 
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1277_, 0, v_x_1266_);
lean_closure_set(v___f_1277_, 1, v___y_1267_);
lean_closure_set(v___f_1277_, 2, v___y_1268_);
lean_closure_set(v___f_1277_, 3, v___y_1269_);
lean_closure_set(v___f_1277_, 4, v___y_1270_);
lean_closure_set(v___f_1277_, 5, v___y_1271_);
v___x_1278_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1265_, v___f_1277_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1278_) == 0)
{
return v___x_1278_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1287_, lean_object* v_x_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1287_, v_x_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1300_, lean_object* v_mvarId_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1301_, v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_mvarId_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1314_, v_mvarId_1315_, v_x_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1328_, lean_object* v_generation_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
lean_inc(v_a_1328_);
v___x_1341_ = l_Lean_FVarId_getDecl___redArg(v_a_1328_, v___y_1336_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = l_Lean_LocalDecl_type(v_a_1342_);
lean_dec(v_a_1342_);
lean_inc_ref(v___x_1343_);
v___x_1344_ = l_Lean_Meta_isProp(v___x_1343_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = lean_unbox(v_a_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref(v___x_1343_);
lean_inc(v_a_1328_);
v___x_1347_ = l_Lean_FVarId_getDecl___redArg(v_a_1328_, v___y_1336_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
v___x_1350_ = l_Lean_LocalDecl_value(v_a_1348_, v___x_1349_);
lean_dec(v_a_1348_);
v___x_1351_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1350_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref(v___x_1351_);
lean_inc(v_a_1328_);
v___x_1353_ = l_Lean_mkFVar(v_a_1328_);
v___x_1354_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1353_, v___y_1335_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
lean_inc(v_a_1352_);
v___x_1356_ = l_Lean_Meta_Simp_Result_getProof(v_a_1352_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_expr_1358_; lean_object* v___x_1359_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v_expr_1358_ = lean_ctor_get(v_a_1352_, 0);
lean_inc_ref(v_expr_1358_);
lean_dec(v_a_1352_);
v___x_1359_ = l_Lean_Meta_Grind_addNewEq(v_a_1355_, v_expr_1358_, v_a_1357_, v_generation_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1368_; 
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1369_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1363_ = lean_st_ref_get(v___y_1330_);
v___x_1364_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1328_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1328_);
v_a_1370_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1359_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1359_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_a_1355_);
lean_dec(v_a_1352_);
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1378_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1356_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1356_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1352_);
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1386_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1354_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1354_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1394_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1351_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1351_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_a_1345_);
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1402_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1347_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1347_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec(v_a_1345_);
lean_dec(v_generation_1329_);
v___x_1410_ = lean_st_ref_get(v___y_1330_);
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1343_);
v___x_1412_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1411_, v___x_1343_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v_mvarId_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v_mvarId_1414_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_mvarId_1414_);
lean_dec(v___x_1410_);
v___x_1415_ = l_Lean_mkFVar(v_a_1328_);
v___x_1416_ = l_Lean_MVarId_assert(v_mvarId_1414_, v_a_1413_, v___x_1343_, v___x_1415_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1435_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1435_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v_toGoalState_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1433_; 
v___x_1421_ = lean_st_ref_get(v___y_1330_);
v_toGoalState_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1421_, 1);
lean_dec(v_unused_1434_);
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_toGoalState_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v_a_1417_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_toGoalState_1422_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_a_1417_);
v___x_1427_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1428_);
v___x_1430_ = v___x_1419_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1416_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1416_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v___x_1410_);
lean_dec_ref(v___x_1343_);
lean_dec(v_a_1328_);
v_a_1444_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1412_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1412_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v___x_1343_);
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1452_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1344_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1344_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_generation_1329_);
lean_dec(v_a_1328_);
v_a_1460_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1341_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1341_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1468_, lean_object* v_generation_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1468_, v_generation_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v_ks_1486_; lean_object* v_vs_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1511_; 
v_ks_1486_ = lean_ctor_get(v_x_1482_, 0);
v_vs_1487_ = lean_ctor_get(v_x_1482_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_x_1482_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1489_ = v_x_1482_;
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_vs_1487_);
lean_inc(v_ks_1486_);
lean_dec(v_x_1482_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1511_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_array_get_size(v_ks_1486_);
v___x_1492_ = lean_nat_dec_lt(v_x_1483_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_dec(v_x_1483_);
v___x_1493_ = lean_array_push(v_ks_1486_, v_x_1484_);
v___x_1494_ = lean_array_push(v_vs_1487_, v_x_1485_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1494_);
lean_ctor_set(v___x_1489_, 0, v___x_1493_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
lean_object* v_k_x27_1498_; uint8_t v___x_1499_; 
v_k_x27_1498_ = lean_array_fget_borrowed(v_ks_1486_, v_x_1483_);
v___x_1499_ = l_Lean_instBEqMVarId_beq(v_x_1484_, v_k_x27_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1501_; 
if (v_isShared_1490_ == 0)
{
v___x_1501_ = v___x_1489_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_ks_1486_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_vs_1487_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_x_1483_, v___x_1502_);
lean_dec(v_x_1483_);
v_x_1482_ = v___x_1501_;
v_x_1483_ = v___x_1503_;
goto _start;
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = lean_array_fset(v_ks_1486_, v_x_1483_, v_x_1484_);
v___x_1507_ = lean_array_fset(v_vs_1487_, v_x_1483_, v_x_1485_);
lean_dec(v_x_1483_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1507_);
lean_ctor_set(v___x_1489_, 0, v___x_1506_);
v___x_1509_ = v___x_1489_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1512_, lean_object* v_k_1513_, lean_object* v_v_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1512_, v___x_1515_, v_k_1513_, v_v_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1517_, size_t v_x_1518_, size_t v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
lean_object* v_es_1522_; size_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; lean_object* v_j_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_es_1522_ = lean_ctor_get(v_x_1517_, 0);
v___x_1523_ = ((size_t)5ULL);
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_1526_ = lean_usize_land(v_x_1518_, v___x_1525_);
v_j_1527_ = lean_usize_to_nat(v___x_1526_);
v___x_1528_ = lean_array_get_size(v_es_1522_);
v___x_1529_ = lean_nat_dec_lt(v_j_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_dec(v_j_1527_);
lean_dec(v_x_1521_);
lean_dec(v_x_1520_);
return v_x_1517_;
}
else
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1566_; 
lean_inc_ref(v_es_1522_);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_x_1517_, 0);
lean_dec(v_unused_1567_);
v___x_1531_ = v_x_1517_;
v_isShared_1532_ = v_isSharedCheck_1566_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v_x_1517_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1566_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_v_1533_; lean_object* v___x_1534_; lean_object* v_xs_x27_1535_; lean_object* v___y_1537_; 
v_v_1533_ = lean_array_fget(v_es_1522_, v_j_1527_);
v___x_1534_ = lean_box(0);
v_xs_x27_1535_ = lean_array_fset(v_es_1522_, v_j_1527_, v___x_1534_);
switch(lean_obj_tag(v_v_1533_))
{
case 0:
{
lean_object* v_key_1542_; lean_object* v_val_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1553_; 
v_key_1542_ = lean_ctor_get(v_v_1533_, 0);
v_val_1543_ = lean_ctor_get(v_v_1533_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_v_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1545_ = v_v_1533_;
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_val_1543_);
lean_inc(v_key_1542_);
lean_dec(v_v_1533_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; 
v___x_1547_ = l_Lean_instBEqMVarId_beq(v_x_1520_, v_key_1542_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1545_);
v___x_1548_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1542_, v_val_1543_, v_x_1520_, v_x_1521_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
v___y_1537_ = v___x_1549_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1551_; 
lean_dec(v_val_1543_);
lean_dec(v_key_1542_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_x_1521_);
lean_ctor_set(v___x_1545_, 0, v_x_1520_);
v___x_1551_ = v___x_1545_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_x_1520_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_x_1521_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
v___y_1537_ = v___x_1551_;
goto v___jp_1536_;
}
}
}
}
case 1:
{
lean_object* v_node_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1564_; 
v_node_1554_ = lean_ctor_get(v_v_1533_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_v_1533_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1556_ = v_v_1533_;
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_node_1554_);
lean_dec(v_v_1533_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1558_ = lean_usize_shift_right(v_x_1518_, v___x_1523_);
v___x_1559_ = lean_usize_add(v_x_1519_, v___x_1524_);
v___x_1560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1554_, v___x_1558_, v___x_1559_, v_x_1520_, v_x_1521_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1560_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v___y_1537_ = v___x_1562_;
goto v___jp_1536_;
}
}
}
default: 
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_x_1520_);
lean_ctor_set(v___x_1565_, 1, v_x_1521_);
v___y_1537_ = v___x_1565_;
goto v___jp_1536_;
}
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_array_fset(v_xs_x27_1535_, v_j_1527_, v___y_1537_);
lean_dec(v_j_1527_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1538_);
v___x_1540_ = v___x_1531_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_object* v_ks_1568_; lean_object* v_vs_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1589_; 
v_ks_1568_ = lean_ctor_get(v_x_1517_, 0);
v_vs_1569_ = lean_ctor_get(v_x_1517_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1517_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1571_ = v_x_1517_;
v_isShared_1572_ = v_isSharedCheck_1589_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_vs_1569_);
lean_inc(v_ks_1568_);
lean_dec(v_x_1517_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1589_;
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
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_ks_1568_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_vs_1569_);
v___x_1574_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v_newNode_1575_; uint8_t v___y_1577_; size_t v___x_1583_; uint8_t v___x_1584_; 
v_newNode_1575_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1574_, v_x_1520_, v_x_1521_);
v___x_1583_ = ((size_t)7ULL);
v___x_1584_ = lean_usize_dec_le(v___x_1583_, v_x_1519_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1575_);
v___x_1586_ = lean_unsigned_to_nat(4u);
v___x_1587_ = lean_nat_dec_lt(v___x_1585_, v___x_1586_);
lean_dec(v___x_1585_);
v___y_1577_ = v___x_1587_;
goto v___jp_1576_;
}
else
{
v___y_1577_ = v___x_1584_;
goto v___jp_1576_;
}
v___jp_1576_:
{
if (v___y_1577_ == 0)
{
lean_object* v_ks_1578_; lean_object* v_vs_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_ks_1578_ = lean_ctor_get(v_newNode_1575_, 0);
lean_inc_ref(v_ks_1578_);
v_vs_1579_ = lean_ctor_get(v_newNode_1575_, 1);
lean_inc_ref(v_vs_1579_);
lean_dec_ref(v_newNode_1575_);
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2);
v___x_1582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1519_, v_ks_1578_, v_vs_1579_, v___x_1580_, v___x_1581_);
lean_dec_ref(v_vs_1579_);
lean_dec_ref(v_ks_1578_);
return v___x_1582_;
}
else
{
return v_newNode_1575_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1590_, lean_object* v_keys_1591_, lean_object* v_vals_1592_, lean_object* v_i_1593_, lean_object* v_entries_1594_){
_start:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_array_get_size(v_keys_1591_);
v___x_1596_ = lean_nat_dec_lt(v_i_1593_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_dec(v_i_1593_);
return v_entries_1594_;
}
else
{
lean_object* v_k_1597_; lean_object* v_v_1598_; uint64_t v___x_1599_; size_t v_h_1600_; size_t v___x_1601_; lean_object* v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; size_t v_h_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_k_1597_ = lean_array_fget_borrowed(v_keys_1591_, v_i_1593_);
v_v_1598_ = lean_array_fget_borrowed(v_vals_1592_, v_i_1593_);
v___x_1599_ = l_Lean_instHashableMVarId_hash(v_k_1597_);
v_h_1600_ = lean_uint64_to_usize(v___x_1599_);
v___x_1601_ = ((size_t)5ULL);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_sub(v_depth_1590_, v___x_1603_);
v___x_1605_ = lean_usize_mul(v___x_1601_, v___x_1604_);
v_h_1606_ = lean_usize_shift_right(v_h_1600_, v___x_1605_);
v___x_1607_ = lean_nat_add(v_i_1593_, v___x_1602_);
lean_dec(v_i_1593_);
lean_inc(v_v_1598_);
lean_inc(v_k_1597_);
v___x_1608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1594_, v_h_1606_, v_depth_1590_, v_k_1597_, v_v_1598_);
v_i_1593_ = v___x_1607_;
v_entries_1594_ = v___x_1608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1610_, lean_object* v_keys_1611_, lean_object* v_vals_1612_, lean_object* v_i_1613_, lean_object* v_entries_1614_){
_start:
{
size_t v_depth_boxed_1615_; lean_object* v_res_1616_; 
v_depth_boxed_1615_ = lean_unbox_usize(v_depth_1610_);
lean_dec(v_depth_1610_);
v_res_1616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1615_, v_keys_1611_, v_vals_1612_, v_i_1613_, v_entries_1614_);
lean_dec_ref(v_vals_1612_);
lean_dec_ref(v_keys_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
size_t v_x_195291__boxed_1622_; size_t v_x_195292__boxed_1623_; lean_object* v_res_1624_; 
v_x_195291__boxed_1622_ = lean_unbox_usize(v_x_1618_);
lean_dec(v_x_1618_);
v_x_195292__boxed_1623_ = lean_unbox_usize(v_x_1619_);
lean_dec(v_x_1619_);
v_res_1624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1617_, v_x_195291__boxed_1622_, v_x_195292__boxed_1623_, v_x_1620_, v_x_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
uint64_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = l_Lean_instHashableMVarId_hash(v_x_1626_);
v___x_1629_ = lean_uint64_to_usize(v___x_1628_);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1625_, v___x_1629_, v___x_1630_, v_x_1626_, v_x_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1632_, lean_object* v_val_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v_mctx_1637_; lean_object* v_cache_1638_; lean_object* v_zetaDeltaFVarIds_1639_; lean_object* v_postponed_1640_; lean_object* v_diag_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1668_; 
v___x_1636_ = lean_st_ref_take(v___y_1634_);
v_mctx_1637_ = lean_ctor_get(v___x_1636_, 0);
v_cache_1638_ = lean_ctor_get(v___x_1636_, 1);
v_zetaDeltaFVarIds_1639_ = lean_ctor_get(v___x_1636_, 2);
v_postponed_1640_ = lean_ctor_get(v___x_1636_, 3);
v_diag_1641_ = lean_ctor_get(v___x_1636_, 4);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1643_ = v___x_1636_;
v_isShared_1644_ = v_isSharedCheck_1668_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_diag_1641_);
lean_inc(v_postponed_1640_);
lean_inc(v_zetaDeltaFVarIds_1639_);
lean_inc(v_cache_1638_);
lean_inc(v_mctx_1637_);
lean_dec(v___x_1636_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1668_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_depth_1645_; lean_object* v_levelAssignDepth_1646_; lean_object* v_mvarCounter_1647_; lean_object* v_lDepth_1648_; lean_object* v_decls_1649_; lean_object* v_userNames_1650_; lean_object* v_lAssignment_1651_; lean_object* v_eAssignment_1652_; lean_object* v_dAssignment_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1667_; 
v_depth_1645_ = lean_ctor_get(v_mctx_1637_, 0);
v_levelAssignDepth_1646_ = lean_ctor_get(v_mctx_1637_, 1);
v_mvarCounter_1647_ = lean_ctor_get(v_mctx_1637_, 2);
v_lDepth_1648_ = lean_ctor_get(v_mctx_1637_, 3);
v_decls_1649_ = lean_ctor_get(v_mctx_1637_, 4);
v_userNames_1650_ = lean_ctor_get(v_mctx_1637_, 5);
v_lAssignment_1651_ = lean_ctor_get(v_mctx_1637_, 6);
v_eAssignment_1652_ = lean_ctor_get(v_mctx_1637_, 7);
v_dAssignment_1653_ = lean_ctor_get(v_mctx_1637_, 8);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_mctx_1637_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1655_ = v_mctx_1637_;
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_dAssignment_1653_);
lean_inc(v_eAssignment_1652_);
lean_inc(v_lAssignment_1651_);
lean_inc(v_userNames_1650_);
lean_inc(v_decls_1649_);
lean_inc(v_lDepth_1648_);
lean_inc(v_mvarCounter_1647_);
lean_inc(v_levelAssignDepth_1646_);
lean_inc(v_depth_1645_);
lean_dec(v_mctx_1637_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1652_, v_mvarId_1632_, v_val_1633_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 7, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_depth_1645_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_levelAssignDepth_1646_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_mvarCounter_1647_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_lDepth_1648_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_decls_1649_);
lean_ctor_set(v_reuseFailAlloc_1666_, 5, v_userNames_1650_);
lean_ctor_set(v_reuseFailAlloc_1666_, 6, v_lAssignment_1651_);
lean_ctor_set(v_reuseFailAlloc_1666_, 7, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 8, v_dAssignment_1653_);
v___x_1659_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1659_);
v___x_1661_ = v___x_1643_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_cache_1638_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_zetaDeltaFVarIds_1639_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_postponed_1640_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_diag_1641_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_st_ref_set(v___y_1634_, v___x_1661_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1669_, lean_object* v_val_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1669_, v_val_1670_, v___y_1671_);
lean_dec(v___y_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; lean_object* v_ngen_1677_; lean_object* v_namePrefix_1678_; lean_object* v_idx_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1708_; 
v___x_1676_ = lean_st_ref_get(v___y_1674_);
v_ngen_1677_ = lean_ctor_get(v___x_1676_, 2);
lean_inc_ref(v_ngen_1677_);
lean_dec(v___x_1676_);
v_namePrefix_1678_ = lean_ctor_get(v_ngen_1677_, 0);
v_idx_1679_ = lean_ctor_get(v_ngen_1677_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_ngen_1677_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1681_ = v_ngen_1677_;
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_idx_1679_);
lean_inc(v_namePrefix_1678_);
lean_dec(v_ngen_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v_env_1684_; lean_object* v_nextMacroScope_1685_; lean_object* v_auxDeclNGen_1686_; lean_object* v_traceState_1687_; lean_object* v_cache_1688_; lean_object* v_messages_1689_; lean_object* v_infoState_1690_; lean_object* v_snapshotTasks_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1706_; 
v___x_1683_ = lean_st_ref_take(v___y_1674_);
v_env_1684_ = lean_ctor_get(v___x_1683_, 0);
v_nextMacroScope_1685_ = lean_ctor_get(v___x_1683_, 1);
v_auxDeclNGen_1686_ = lean_ctor_get(v___x_1683_, 3);
v_traceState_1687_ = lean_ctor_get(v___x_1683_, 4);
v_cache_1688_ = lean_ctor_get(v___x_1683_, 5);
v_messages_1689_ = lean_ctor_get(v___x_1683_, 6);
v_infoState_1690_ = lean_ctor_get(v___x_1683_, 7);
v_snapshotTasks_1691_ = lean_ctor_get(v___x_1683_, 8);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v___x_1683_, 2);
lean_dec(v_unused_1707_);
v___x_1693_ = v___x_1683_;
v_isShared_1694_ = v_isSharedCheck_1706_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_snapshotTasks_1691_);
lean_inc(v_infoState_1690_);
lean_inc(v_messages_1689_);
lean_inc(v_cache_1688_);
lean_inc(v_traceState_1687_);
lean_inc(v_auxDeclNGen_1686_);
lean_inc(v_nextMacroScope_1685_);
lean_inc(v_env_1684_);
lean_dec(v___x_1683_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1706_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_r_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_inc(v_idx_1679_);
lean_inc(v_namePrefix_1678_);
v_r_1695_ = l_Lean_Name_num___override(v_namePrefix_1678_, v_idx_1679_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_add(v_idx_1679_, v___x_1696_);
lean_dec(v_idx_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1697_);
v___x_1699_ = v___x_1681_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_namePrefix_1678_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 2, v___x_1699_);
v___x_1701_ = v___x_1693_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_env_1684_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_nextMacroScope_1685_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_auxDeclNGen_1686_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_traceState_1687_);
lean_ctor_set(v_reuseFailAlloc_1704_, 5, v_cache_1688_);
lean_ctor_set(v_reuseFailAlloc_1704_, 6, v_messages_1689_);
lean_ctor_set(v_reuseFailAlloc_1704_, 7, v_infoState_1690_);
lean_ctor_set(v_reuseFailAlloc_1704_, 8, v_snapshotTasks_1691_);
v___x_1701_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_st_ref_set(v___y_1674_, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_r_1695_);
return v___x_1703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1709_);
lean_dec(v___y_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v___x_1723_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1721_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec(v___y_1732_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1749_, lean_object* v_a_1750_, uint8_t v___y_1751_, uint8_t v___x_1752_, uint8_t v___x_1753_, lean_object* v_a_1754_, lean_object* v___x_1755_, lean_object* v_expr_1756_, lean_object* v___x_1757_, lean_object* v_val_1758_, lean_object* v_mvarId_1759_, lean_object* v___x_1760_, lean_object* v_a_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_mkLambdaFVars(v___x_1749_, v_a_1750_, v___y_1751_, v___x_1752_, v___y_1751_, v___x_1752_, v___x_1753_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_a_1754_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_mkConst(v___x_1775_, v___x_1777_);
v___x_1779_ = lean_unsigned_to_nat(5u);
v___x_1780_ = lean_mk_empty_array_with_capacity(v___x_1779_);
v___x_1781_ = lean_array_push(v___x_1780_, v___x_1755_);
v___x_1782_ = lean_array_push(v___x_1781_, v_expr_1756_);
v___x_1783_ = lean_array_push(v___x_1782_, v___x_1757_);
v___x_1784_ = lean_array_push(v___x_1783_, v_val_1758_);
v___x_1785_ = lean_array_push(v___x_1784_, v_a_1774_);
v___x_1786_ = l_Lean_mkAppN(v___x_1778_, v___x_1785_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1759_, v___x_1786_, v___y_1769_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1805_; 
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1787_, 0);
lean_dec(v_unused_1806_);
v___x_1789_ = v___x_1787_;
v_isShared_1790_ = v_isSharedCheck_1805_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v___x_1787_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1805_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v_toGoalState_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1803_; 
v___x_1791_ = lean_st_ref_get(v___y_1762_);
v_toGoalState_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1791_, 1);
lean_dec(v_unused_1804_);
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1803_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_toGoalState_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1803_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1760_);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_toGoalState_1792_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1760_);
v___x_1797_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1761_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1798_);
v___x_1800_ = v___x_1789_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
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
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_a_1761_);
lean_dec(v___x_1760_);
v_a_1807_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1787_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1787_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_a_1761_);
lean_dec(v___x_1760_);
lean_dec(v_mvarId_1759_);
lean_dec_ref(v_val_1758_);
lean_dec_ref(v___x_1757_);
lean_dec_ref(v_expr_1756_);
lean_dec_ref(v___x_1755_);
lean_dec(v_a_1754_);
v_a_1815_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1773_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1773_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1823_ = _args[0];
lean_object* v_a_1824_ = _args[1];
lean_object* v___y_1825_ = _args[2];
lean_object* v___x_1826_ = _args[3];
lean_object* v___x_1827_ = _args[4];
lean_object* v_a_1828_ = _args[5];
lean_object* v___x_1829_ = _args[6];
lean_object* v_expr_1830_ = _args[7];
lean_object* v___x_1831_ = _args[8];
lean_object* v_val_1832_ = _args[9];
lean_object* v_mvarId_1833_ = _args[10];
lean_object* v___x_1834_ = _args[11];
lean_object* v_a_1835_ = _args[12];
lean_object* v___y_1836_ = _args[13];
lean_object* v___y_1837_ = _args[14];
lean_object* v___y_1838_ = _args[15];
lean_object* v___y_1839_ = _args[16];
lean_object* v___y_1840_ = _args[17];
lean_object* v___y_1841_ = _args[18];
lean_object* v___y_1842_ = _args[19];
lean_object* v___y_1843_ = _args[20];
lean_object* v___y_1844_ = _args[21];
lean_object* v___y_1845_ = _args[22];
lean_object* v___y_1846_ = _args[23];
_start:
{
uint8_t v___y_195618__boxed_1847_; uint8_t v___x_195619__boxed_1848_; uint8_t v___x_195620__boxed_1849_; lean_object* v_res_1850_; 
v___y_195618__boxed_1847_ = lean_unbox(v___y_1825_);
v___x_195619__boxed_1848_ = lean_unbox(v___x_1826_);
v___x_195620__boxed_1849_ = lean_unbox(v___x_1827_);
v_res_1850_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1823_, v_a_1824_, v___y_195618__boxed_1847_, v___x_195619__boxed_1848_, v___x_195620__boxed_1849_, v_a_1828_, v___x_1829_, v_expr_1830_, v___x_1831_, v_val_1832_, v_mvarId_1833_, v___x_1834_, v_a_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___x_1823_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1856_, lean_object* v_a_1857_, uint8_t v___x_1858_, uint8_t v___x_1859_, uint8_t v___x_1860_, lean_object* v_a_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, lean_object* v_expr_1864_, lean_object* v___x_1865_, lean_object* v_val_1866_, lean_object* v_mvarId_1867_, lean_object* v___x_1868_, lean_object* v_a_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_mkLambdaFVars(v___x_1856_, v_a_1857_, v___x_1858_, v___x_1859_, v___x_1858_, v___x_1859_, v___x_1860_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_a_1861_);
lean_ctor_set(v___x_1884_, 1, v___x_1862_);
v___x_1885_ = l_Lean_mkConst(v___x_1883_, v___x_1884_);
v___x_1886_ = lean_unsigned_to_nat(5u);
v___x_1887_ = lean_mk_empty_array_with_capacity(v___x_1886_);
v___x_1888_ = lean_array_push(v___x_1887_, v___x_1863_);
v___x_1889_ = lean_array_push(v___x_1888_, v_expr_1864_);
v___x_1890_ = lean_array_push(v___x_1889_, v___x_1865_);
v___x_1891_ = lean_array_push(v___x_1890_, v_val_1866_);
v___x_1892_ = lean_array_push(v___x_1891_, v_a_1882_);
v___x_1893_ = l_Lean_mkAppN(v___x_1885_, v___x_1892_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1867_, v___x_1893_, v___y_1877_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1912_; 
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1913_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1912_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1912_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v_toGoalState_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1910_; 
v___x_1898_ = lean_st_ref_get(v___y_1870_);
v_toGoalState_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1898_, 1);
lean_dec(v_unused_1911_);
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_toGoalState_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1910_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v___x_1868_);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_toGoalState_1899_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1868_);
v___x_1904_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1869_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1905_);
v___x_1907_ = v___x_1896_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
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
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1869_);
lean_dec(v___x_1868_);
v_a_1914_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1894_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1894_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
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
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1869_);
lean_dec(v___x_1868_);
lean_dec(v_mvarId_1867_);
lean_dec_ref(v_val_1866_);
lean_dec_ref(v___x_1865_);
lean_dec_ref(v_expr_1864_);
lean_dec_ref(v___x_1863_);
lean_dec(v___x_1862_);
lean_dec(v_a_1861_);
v_a_1922_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1881_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1881_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1930_ = _args[0];
lean_object* v_a_1931_ = _args[1];
lean_object* v___x_1932_ = _args[2];
lean_object* v___x_1933_ = _args[3];
lean_object* v___x_1934_ = _args[4];
lean_object* v_a_1935_ = _args[5];
lean_object* v___x_1936_ = _args[6];
lean_object* v___x_1937_ = _args[7];
lean_object* v_expr_1938_ = _args[8];
lean_object* v___x_1939_ = _args[9];
lean_object* v_val_1940_ = _args[10];
lean_object* v_mvarId_1941_ = _args[11];
lean_object* v___x_1942_ = _args[12];
lean_object* v_a_1943_ = _args[13];
lean_object* v___y_1944_ = _args[14];
lean_object* v___y_1945_ = _args[15];
lean_object* v___y_1946_ = _args[16];
lean_object* v___y_1947_ = _args[17];
lean_object* v___y_1948_ = _args[18];
lean_object* v___y_1949_ = _args[19];
lean_object* v___y_1950_ = _args[20];
lean_object* v___y_1951_ = _args[21];
lean_object* v___y_1952_ = _args[22];
lean_object* v___y_1953_ = _args[23];
lean_object* v___y_1954_ = _args[24];
_start:
{
uint8_t v___x_195800__boxed_1955_; uint8_t v___x_195801__boxed_1956_; uint8_t v___x_195802__boxed_1957_; lean_object* v_res_1958_; 
v___x_195800__boxed_1955_ = lean_unbox(v___x_1932_);
v___x_195801__boxed_1956_ = lean_unbox(v___x_1933_);
v___x_195802__boxed_1957_ = lean_unbox(v___x_1934_);
v_res_1958_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1930_, v_a_1931_, v___x_195800__boxed_1955_, v___x_195801__boxed_1956_, v___x_195802__boxed_1957_, v_a_1935_, v___x_1936_, v___x_1937_, v_expr_1938_, v___x_1939_, v_val_1940_, v_mvarId_1941_, v___x_1942_, v_a_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___x_1930_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1959_, lean_object* v_a_1960_, uint8_t v___y_1961_, uint8_t v___x_1962_, uint8_t v___x_1963_, lean_object* v_mvarId_1964_, lean_object* v___x_1965_, lean_object* v_a_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Meta_mkLambdaFVars(v___x_1959_, v_a_1960_, v___y_1961_, v___x_1962_, v___y_1961_, v___x_1962_, v___x_1963_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1964_, v_a_1979_, v___y_1974_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1998_; 
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v___x_1980_, 0);
lean_dec(v_unused_1999_);
v___x_1982_ = v___x_1980_;
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v___x_1980_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1998_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v_toGoalState_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1996_; 
v___x_1984_ = lean_st_ref_get(v___y_1967_);
v_toGoalState_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1984_, 1);
lean_dec(v_unused_1997_);
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1996_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_toGoalState_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1996_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_1965_);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_toGoalState_1985_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1965_);
v___x_1990_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_a_1966_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1991_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
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
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1966_);
lean_dec(v___x_1965_);
v_a_2000_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1980_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1980_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1966_);
lean_dec(v___x_1965_);
lean_dec(v_mvarId_1964_);
v_a_2008_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1978_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1978_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2016_ = _args[0];
lean_object* v_a_2017_ = _args[1];
lean_object* v___y_2018_ = _args[2];
lean_object* v___x_2019_ = _args[3];
lean_object* v___x_2020_ = _args[4];
lean_object* v_mvarId_2021_ = _args[5];
lean_object* v___x_2022_ = _args[6];
lean_object* v_a_2023_ = _args[7];
lean_object* v___y_2024_ = _args[8];
lean_object* v___y_2025_ = _args[9];
lean_object* v___y_2026_ = _args[10];
lean_object* v___y_2027_ = _args[11];
lean_object* v___y_2028_ = _args[12];
lean_object* v___y_2029_ = _args[13];
lean_object* v___y_2030_ = _args[14];
lean_object* v___y_2031_ = _args[15];
lean_object* v___y_2032_ = _args[16];
lean_object* v___y_2033_ = _args[17];
lean_object* v___y_2034_ = _args[18];
_start:
{
uint8_t v___y_195971__boxed_2035_; uint8_t v___x_195972__boxed_2036_; uint8_t v___x_195973__boxed_2037_; lean_object* v_res_2038_; 
v___y_195971__boxed_2035_ = lean_unbox(v___y_2018_);
v___x_195972__boxed_2036_ = lean_unbox(v___x_2019_);
v___x_195973__boxed_2037_ = lean_unbox(v___x_2020_);
v_res_2038_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2016_, v_a_2017_, v___y_195971__boxed_2035_, v___x_195972__boxed_2036_, v___x_195973__boxed_2037_, v_mvarId_2021_, v___x_2022_, v_a_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
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
lean_dec_ref(v___x_2016_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2041_, lean_object* v___x_2042_, lean_object* v_generation_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v_mvarId_2041_);
v___x_2055_ = l_Lean_MVarId_getTag(v_mvarId_2041_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2042_, v_a_2056_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_n(v_a_2058_, 2);
lean_dec_ref(v___x_2057_);
v___x_2059_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2041_, v_a_2058_, v___y_2051_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; lean_object* v_toGoalState_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___x_2059_);
v___x_2060_ = lean_st_ref_get(v___y_2044_);
v_toGoalState_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_2060_, 1);
lean_dec(v_unused_2071_);
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_toGoalState_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = l_Lean_Expr_mvarId_x21(v_a_2058_);
lean_dec(v_a_2058_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_toGoalState_2061_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2067_, v_generation_2043_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_2058_);
lean_dec(v_generation_2043_);
v_a_2072_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2059_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2059_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_generation_2043_);
lean_dec(v_mvarId_2041_);
v_a_2080_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2057_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2057_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_generation_2043_);
lean_dec_ref(v___x_2042_);
lean_dec(v_mvarId_2041_);
v_a_2088_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2055_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2055_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2096_, lean_object* v___x_2097_, lean_object* v_generation_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2096_, v___x_2097_, v_generation_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2099_);
return v_res_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2118_ = l_Lean_mkConst(v___x_2117_, v___x_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2119_, lean_object* v_generation_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v_a_2133_; lean_object* v___y_2138_; lean_object* v___x_2148_; lean_object* v_mvarId_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2437_; 
lean_inc_ref(v_goal_2119_);
v___x_2131_ = lean_st_mk_ref(v_goal_2119_);
v___x_2148_ = lean_st_ref_get(v___x_2131_);
v_mvarId_2149_ = lean_ctor_get(v___x_2148_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; 
v_unused_2438_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2438_);
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2437_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_mvarId_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2437_;
goto v_resetjp_2150_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_st_ref_get(v___x_2131_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_a_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
v___jp_2137_:
{
if (lean_obj_tag(v___y_2138_) == 0)
{
lean_object* v_a_2139_; 
v_a_2139_ = lean_ctor_get(v___y_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___y_2138_);
v_a_2133_ = v_a_2139_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v___x_2131_);
v_a_2140_ = lean_ctor_get(v___y_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___y_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___y_2138_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___y_2138_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_MVarId_getType(v_mvarId_2149_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; uint8_t v___x_2155_; uint8_t v___x_2156_; lean_object* v___y_2158_; uint8_t v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = l_Lean_Expr_isForall(v_a_2154_);
v___x_2156_ = 1;
if (v___x_2155_ == 0)
{
uint8_t v___x_2198_; 
lean_del_object(v___x_2151_);
v___x_2198_ = l_Lean_Expr_isLet(v_a_2154_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
lean_dec(v_a_2154_);
lean_dec_ref(v___y_2126_);
lean_dec(v_generation_2120_);
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_goal_2119_);
v_a_2133_ = v___x_2199_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2200_; 
lean_dec_ref(v_goal_2119_);
v___x_2200_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2122_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; uint8_t v_zetaDelta_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v_zetaDelta_2202_ = lean_ctor_get_uint8(v_a_2201_, sizeof(void*)*11 + 19);
lean_dec(v_a_2201_);
if (v_zetaDelta_2202_ == 0)
{
lean_object* v___x_2203_; 
lean_dec(v_a_2154_);
v___x_2203_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; lean_object* v_mvarId_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = lean_st_ref_get(v___x_2131_);
v_mvarId_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_mvarId_2206_);
lean_dec(v___x_2205_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2207_, 0, v_a_2204_);
lean_closure_set(v___f_2207_, 1, v_generation_2120_);
v___x_2208_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2206_, v___f_2207_, v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v___y_2126_);
v___y_2138_ = v___x_2208_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
lean_dec(v_generation_2120_);
v_a_2209_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2203_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2203_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v_mvarId_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; 
v___x_2217_ = lean_st_ref_get(v___x_2131_);
v_mvarId_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc_n(v_mvarId_2218_, 2);
lean_dec(v___x_2217_);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2220_ = l_Lean_Meta_expandLet(v_a_2154_, v___x_2219_, v___x_2156_);
lean_dec(v_a_2154_);
v___f_2221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2221_, 0, v_mvarId_2218_);
lean_closure_set(v___f_2221_, 1, v___x_2220_);
lean_closure_set(v___f_2221_, 2, v_generation_2120_);
v___x_2222_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2218_, v___f_2221_, v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v___y_2126_);
v___y_2138_ = v___x_2222_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
lean_dec(v_generation_2120_);
v_a_2223_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2200_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2200_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; uint8_t v___y_2244_; lean_object* v_localInsts_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___x_2329_; 
lean_dec(v_generation_2120_);
lean_dec_ref(v_goal_2119_);
v___x_2231_ = l_Lean_Expr_bindingDomain_x21(v_a_2154_);
lean_inc_ref(v___x_2231_);
v___x_2329_ = l_Lean_Meta_isProp(v___x_2231_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___y_2332_; uint8_t v___x_2405_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2405_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2405_ == 0)
{
if (v___x_2155_ == 0)
{
lean_del_object(v___x_2151_);
v___y_2332_ = v___x_2155_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2406_; 
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
v___x_2406_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v___y_2126_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = lean_st_ref_get(v___x_2131_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 3);
lean_ctor_set(v___x_2151_, 1, v___x_2408_);
lean_ctor_set(v___x_2151_, 0, v_a_2407_);
v___x_2410_ = v___x_2151_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2407_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
v_a_2133_ = v___x_2410_;
goto v___jp_2132_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_del_object(v___x_2151_);
lean_dec(v___x_2131_);
v_a_2412_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2406_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2406_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
uint8_t v___x_2420_; 
lean_del_object(v___x_2151_);
v___x_2420_ = 0;
v___y_2332_ = v___x_2420_;
goto v___jp_2331_;
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v_mvarId_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2403_; 
v___x_2333_ = lean_st_ref_get(v___x_2131_);
v_mvarId_2334_ = lean_ctor_get(v___x_2333_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v___x_2333_, 0);
lean_dec(v_unused_2404_);
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2403_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_mvarId_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2403_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; 
lean_inc(v_mvarId_2334_);
v___x_2338_ = l_Lean_MVarId_getTag(v_mvarId_2334_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
lean_inc_ref(v___x_2231_);
v___x_2342_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2231_, v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_expr_2344_; lean_object* v_proof_x3f_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v_expr_2344_ = lean_ctor_get(v_a_2343_, 0);
lean_inc_ref_n(v_expr_2344_, 2);
v_proof_x3f_2345_ = lean_ctor_get(v_a_2343_, 1);
lean_inc(v_proof_x3f_2345_);
lean_dec(v_a_2343_);
v___x_2346_ = l_Lean_Expr_bindingName_x21(v_a_2154_);
lean_inc(v___x_2346_);
v___x_2347_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2346_, v_expr_2344_, v___x_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v_lctx_2349_; lean_object* v_localInstances_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v_lctx_2349_ = lean_ctor_get(v___y_2126_, 2);
v_localInstances_2350_ = lean_ctor_get(v___y_2126_, 3);
lean_inc_n(v_a_2341_, 2);
v___x_2351_ = l_Lean_mkFVar(v_a_2341_);
v___x_2352_ = l_Lean_Expr_bindingInfo_x21(v_a_2154_);
v___x_2353_ = 0;
lean_inc_ref_n(v_expr_2344_, 2);
lean_inc_ref(v_lctx_2349_);
v___x_2354_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2349_, v_a_2341_, v_a_2348_, v_expr_2344_, v___x_2352_, v___x_2353_);
v___x_2355_ = l_Lean_Meta_isClass_x3f(v_expr_2344_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = l_Lean_Expr_bindingBody_x21(v_a_2154_);
if (lean_obj_tag(v_a_2356_) == 1)
{
lean_object* v_val_2358_; lean_object* v___x_2360_; 
v_val_2358_ = lean_ctor_get(v_a_2356_, 0);
lean_inc(v_val_2358_);
lean_dec_ref(v_a_2356_);
lean_inc_ref(v___x_2351_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2351_);
lean_ctor_set(v___x_2336_, 0, v_val_2358_);
v___x_2360_ = v___x_2336_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_val_2358_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2351_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_localInstances_2350_);
v___x_2361_ = lean_array_push(v_localInstances_2350_, v___x_2360_);
lean_inc(v___x_2131_);
lean_inc_ref(v_expr_2344_);
v___y_2233_ = v_a_2341_;
v___y_2234_ = v___x_2357_;
v___y_2235_ = v_expr_2344_;
v___y_2236_ = v___y_2332_;
v___y_2237_ = v_mvarId_2334_;
v___y_2238_ = v___x_2346_;
v___y_2239_ = v___x_2351_;
v___y_2240_ = v_proof_x3f_2345_;
v___y_2241_ = v_expr_2344_;
v___y_2242_ = v___x_2354_;
v___y_2243_ = v_a_2339_;
v___y_2244_ = v___x_2352_;
v_localInsts_2245_ = v___x_2361_;
v___y_2246_ = v___x_2131_;
v___y_2247_ = v___y_2121_;
v___y_2248_ = v___y_2122_;
v___y_2249_ = v___y_2123_;
v___y_2250_ = v___y_2124_;
v___y_2251_ = v___y_2125_;
v___y_2252_ = v___y_2126_;
v___y_2253_ = v___y_2127_;
v___y_2254_ = v___y_2128_;
v___y_2255_ = v___y_2129_;
goto v___jp_2232_;
}
}
else
{
lean_inc_ref(v_localInstances_2350_);
lean_dec(v_a_2356_);
lean_del_object(v___x_2336_);
lean_inc(v___x_2131_);
lean_inc_ref(v_expr_2344_);
v___y_2233_ = v_a_2341_;
v___y_2234_ = v___x_2357_;
v___y_2235_ = v_expr_2344_;
v___y_2236_ = v___y_2332_;
v___y_2237_ = v_mvarId_2334_;
v___y_2238_ = v___x_2346_;
v___y_2239_ = v___x_2351_;
v___y_2240_ = v_proof_x3f_2345_;
v___y_2241_ = v_expr_2344_;
v___y_2242_ = v___x_2354_;
v___y_2243_ = v_a_2339_;
v___y_2244_ = v___x_2352_;
v_localInsts_2245_ = v_localInstances_2350_;
v___y_2246_ = v___x_2131_;
v___y_2247_ = v___y_2121_;
v___y_2248_ = v___y_2122_;
v___y_2249_ = v___y_2123_;
v___y_2250_ = v___y_2124_;
v___y_2251_ = v___y_2125_;
v___y_2252_ = v___y_2126_;
v___y_2253_ = v___y_2127_;
v___y_2254_ = v___y_2128_;
v___y_2255_ = v___y_2129_;
goto v___jp_2232_;
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2351_);
lean_dec(v___x_2346_);
lean_dec(v_proof_x3f_2345_);
lean_dec_ref(v_expr_2344_);
lean_dec(v_a_2341_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2363_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2355_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2355_);
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
lean_dec(v___x_2346_);
lean_dec(v_proof_x3f_2345_);
lean_dec_ref(v_expr_2344_);
lean_dec(v_a_2341_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2371_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2347_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2347_);
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
lean_dec(v_a_2341_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2379_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2342_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2342_);
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
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2387_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2340_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2340_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_del_object(v___x_2336_);
lean_dec(v_mvarId_2334_);
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2395_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2338_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2338_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___x_2231_);
lean_dec(v_a_2154_);
lean_del_object(v___x_2151_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
v_a_2421_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2329_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2329_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
v___jp_2232_:
{
if (lean_obj_tag(v___y_2240_) == 0)
{
uint8_t v___x_2256_; 
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___x_2231_);
v___x_2256_ = l_Lean_Expr_isArrow(v_a_2154_);
lean_dec(v_a_2154_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_expr_instantiate1(v___y_2234_, v___y_2239_);
lean_dec_ref(v___y_2234_);
v___y_2158_ = v___y_2233_;
v___y_2159_ = v___y_2236_;
v___y_2160_ = v___y_2237_;
v___y_2161_ = v___y_2254_;
v___y_2162_ = v___y_2247_;
v___y_2163_ = v___y_2242_;
v___y_2164_ = v___y_2252_;
v___y_2165_ = v___y_2246_;
v___y_2166_ = v___y_2250_;
v___y_2167_ = v___y_2253_;
v___y_2168_ = v___y_2239_;
v___y_2169_ = v___y_2249_;
v___y_2170_ = v___y_2251_;
v___y_2171_ = v_localInsts_2245_;
v___y_2172_ = v___y_2248_;
v___y_2173_ = v___y_2255_;
v___y_2174_ = v___y_2243_;
v___y_2175_ = v___x_2257_;
goto v___jp_2157_;
}
else
{
v___y_2158_ = v___y_2233_;
v___y_2159_ = v___y_2236_;
v___y_2160_ = v___y_2237_;
v___y_2161_ = v___y_2254_;
v___y_2162_ = v___y_2247_;
v___y_2163_ = v___y_2242_;
v___y_2164_ = v___y_2252_;
v___y_2165_ = v___y_2246_;
v___y_2166_ = v___y_2250_;
v___y_2167_ = v___y_2253_;
v___y_2168_ = v___y_2239_;
v___y_2169_ = v___y_2249_;
v___y_2170_ = v___y_2251_;
v___y_2171_ = v_localInsts_2245_;
v___y_2172_ = v___y_2248_;
v___y_2173_ = v___y_2255_;
v___y_2174_ = v___y_2243_;
v___y_2175_ = v___y_2234_;
goto v___jp_2157_;
}
}
else
{
lean_object* v_val_2258_; uint8_t v___x_2259_; 
v_val_2258_ = lean_ctor_get(v___y_2240_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v___y_2240_);
v___x_2259_ = l_Lean_Expr_isArrow(v_a_2154_);
lean_dec(v_a_2154_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_inc_ref(v___y_2234_);
lean_inc_ref_n(v___x_2231_, 2);
v___x_2260_ = l_Lean_mkLambda(v___y_2238_, v___y_2244_, v___x_2231_, v___y_2234_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2239_);
lean_inc(v_val_2258_);
v___x_2263_ = l_Lean_mkApp4(v___x_2262_, v___x_2231_, v___y_2241_, v_val_2258_, v___y_2239_);
v___x_2264_ = lean_expr_instantiate1(v___y_2234_, v___x_2263_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___y_2234_);
lean_inc_ref(v___x_2264_);
v___x_2265_ = l_Lean_Meta_getLevel(v___x_2264_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = 2;
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2242_, v_localInsts_2245_, v___x_2264_, v___x_2267_, v___y_2243_, v___x_2268_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = l_Lean_Expr_mvarId_x21(v_a_2270_);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_mk_empty_array_with_capacity(v___x_2272_);
v___x_2274_ = lean_array_push(v___x_2273_, v___y_2239_);
v___x_2275_ = 1;
v___x_2276_ = lean_box(v___x_2259_);
v___x_2277_ = lean_box(v___x_2156_);
v___x_2278_ = lean_box(v___x_2275_);
lean_inc(v___x_2271_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2279_, 0, v___x_2274_);
lean_closure_set(v___f_2279_, 1, v_a_2270_);
lean_closure_set(v___f_2279_, 2, v___x_2276_);
lean_closure_set(v___f_2279_, 3, v___x_2277_);
lean_closure_set(v___f_2279_, 4, v___x_2278_);
lean_closure_set(v___f_2279_, 5, v_a_2266_);
lean_closure_set(v___f_2279_, 6, v___x_2261_);
lean_closure_set(v___f_2279_, 7, v___x_2231_);
lean_closure_set(v___f_2279_, 8, v___y_2235_);
lean_closure_set(v___f_2279_, 9, v___x_2260_);
lean_closure_set(v___f_2279_, 10, v_val_2258_);
lean_closure_set(v___f_2279_, 11, v___y_2237_);
lean_closure_set(v___f_2279_, 12, v___x_2271_);
lean_closure_set(v___f_2279_, 13, v___y_2233_);
v___x_2280_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2271_, v___f_2279_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
v___y_2138_ = v___x_2280_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_a_2266_);
lean_dec_ref(v___x_2260_);
lean_dec(v_val_2258_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v___x_2131_);
v_a_2281_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2269_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2269_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v___x_2264_);
lean_dec_ref(v___x_2260_);
lean_dec(v_val_2258_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
lean_dec_ref(v_localInsts_2245_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v___x_2131_);
v_a_2289_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2265_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2265_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; 
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2238_);
lean_inc_ref(v___y_2234_);
v___x_2297_ = l_Lean_Meta_getLevel(v___y_2234_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = 2;
v___x_2300_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2234_);
v___x_2301_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2242_, v_localInsts_2245_, v___y_2234_, v___x_2299_, v___y_2243_, v___x_2300_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = l_Lean_Expr_mvarId_x21(v_a_2302_);
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
v___x_2306_ = lean_array_push(v___x_2305_, v___y_2239_);
v___x_2307_ = 1;
v___x_2308_ = lean_box(v___y_2236_);
v___x_2309_ = lean_box(v___x_2156_);
v___x_2310_ = lean_box(v___x_2307_);
lean_inc(v___x_2303_);
v___f_2311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2311_, 0, v___x_2306_);
lean_closure_set(v___f_2311_, 1, v_a_2302_);
lean_closure_set(v___f_2311_, 2, v___x_2308_);
lean_closure_set(v___f_2311_, 3, v___x_2309_);
lean_closure_set(v___f_2311_, 4, v___x_2310_);
lean_closure_set(v___f_2311_, 5, v_a_2298_);
lean_closure_set(v___f_2311_, 6, v___x_2231_);
lean_closure_set(v___f_2311_, 7, v___y_2235_);
lean_closure_set(v___f_2311_, 8, v___y_2234_);
lean_closure_set(v___f_2311_, 9, v_val_2258_);
lean_closure_set(v___f_2311_, 10, v___y_2237_);
lean_closure_set(v___f_2311_, 11, v___x_2303_);
lean_closure_set(v___f_2311_, 12, v___y_2233_);
v___x_2312_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2303_, v___f_2311_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
v___y_2138_ = v___x_2312_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2298_);
lean_dec(v_val_2258_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v___x_2131_);
v_a_2313_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2301_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2301_);
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
lean_dec(v_val_2258_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2246_);
lean_dec_ref(v_localInsts_2245_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v___x_2131_);
v_a_2321_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2297_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2297_);
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
}
}
v___jp_2157_:
{
uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = 2;
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2163_, v___y_2171_, v___y_2175_, v___x_2176_, v___y_2174_, v___x_2177_, v___y_2164_, v___y_2167_, v___y_2161_, v___y_2173_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___x_2189_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l_Lean_Expr_mvarId_x21(v_a_2179_);
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_mk_empty_array_with_capacity(v___x_2181_);
v___x_2183_ = lean_array_push(v___x_2182_, v___y_2168_);
v___x_2184_ = 1;
v___x_2185_ = lean_box(v___y_2159_);
v___x_2186_ = lean_box(v___x_2156_);
v___x_2187_ = lean_box(v___x_2184_);
lean_inc(v___x_2180_);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2188_, 0, v___x_2183_);
lean_closure_set(v___f_2188_, 1, v_a_2179_);
lean_closure_set(v___f_2188_, 2, v___x_2185_);
lean_closure_set(v___f_2188_, 3, v___x_2186_);
lean_closure_set(v___f_2188_, 4, v___x_2187_);
lean_closure_set(v___f_2188_, 5, v___y_2160_);
lean_closure_set(v___f_2188_, 6, v___x_2180_);
lean_closure_set(v___f_2188_, 7, v___y_2158_);
v___x_2189_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2180_, v___f_2188_, v___y_2165_, v___y_2162_, v___y_2172_, v___y_2169_, v___y_2166_, v___y_2170_, v___y_2164_, v___y_2167_, v___y_2161_, v___y_2173_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2165_);
v___y_2138_ = v___x_2189_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2160_);
lean_dec(v___y_2158_);
lean_dec(v___x_2131_);
v_a_2190_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2178_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2178_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2151_);
lean_dec(v___x_2131_);
lean_dec_ref(v___y_2126_);
lean_dec(v_generation_2120_);
lean_dec_ref(v_goal_2119_);
v_a_2429_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2153_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2153_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2439_, lean_object* v_generation_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2439_, v_generation_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2452_, lean_object* v_generation_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_mvarId_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; 
v_mvarId_2464_ = lean_ctor_get(v_goal_2452_, 1);
lean_inc(v_mvarId_2464_);
v___f_2465_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2465_, 0, v_goal_2452_);
lean_closure_set(v___f_2465_, 1, v_generation_2453_);
v___x_2466_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2464_, v___f_2465_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2475_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v_fst_2471_; lean_object* v___x_2473_; 
v_fst_2471_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_fst_2471_);
lean_dec(v_a_2467_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_fst_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_fst_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2466_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2466_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2484_, lean_object* v_generation_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2484_, v_generation_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2497_, lean_object* v_val_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2497_, v_val_2498_, v___y_2506_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2511_, lean_object* v_val_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2511_, v_val_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
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
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2550_, v_x_2551_, v_x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2554_, lean_object* v_x_2555_, size_t v_x_2556_, size_t v_x_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2555_, v_x_2556_, v_x_2557_, v_x_2558_, v_x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_){
_start:
{
size_t v_x_196998__boxed_2567_; size_t v_x_196999__boxed_2568_; lean_object* v_res_2569_; 
v_x_196998__boxed_2567_ = lean_unbox_usize(v_x_2563_);
lean_dec(v_x_2563_);
v_x_196999__boxed_2568_ = lean_unbox_usize(v_x_2564_);
lean_dec(v_x_2564_);
v_res_2569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2561_, v_x_2562_, v_x_196998__boxed_2567_, v_x_196999__boxed_2568_, v_x_2565_, v_x_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2570_, lean_object* v_n_2571_, lean_object* v_k_2572_, lean_object* v_v_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2571_, v_k_2572_, v_v_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2575_, size_t v_depth_2576_, lean_object* v_keys_2577_, lean_object* v_vals_2578_, lean_object* v_heq_2579_, lean_object* v_i_2580_, lean_object* v_entries_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2576_, v_keys_2577_, v_vals_2578_, v_i_2580_, v_entries_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2583_, lean_object* v_depth_2584_, lean_object* v_keys_2585_, lean_object* v_vals_2586_, lean_object* v_heq_2587_, lean_object* v_i_2588_, lean_object* v_entries_2589_){
_start:
{
size_t v_depth_boxed_2590_; lean_object* v_res_2591_; 
v_depth_boxed_2590_ = lean_unbox_usize(v_depth_2584_);
lean_dec(v_depth_2584_);
v_res_2591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2583_, v_depth_boxed_2590_, v_keys_2585_, v_vals_2586_, v_heq_2587_, v_i_2588_, v_entries_2589_);
lean_dec_ref(v_vals_2586_);
lean_dec_ref(v_keys_2585_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2593_, v_x_2594_, v_x_2595_, v_x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Expr_getAppFn(v_type_2598_);
if (lean_obj_tag(v___x_2601_) == 4)
{
lean_object* v_declName_2602_; lean_object* v___x_2603_; 
v_declName_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_declName_2602_);
lean_dec_ref(v___x_2601_);
v___x_2603_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2602_, v_a_2599_);
lean_dec(v_declName_2602_);
return v___x_2603_;
}
else
{
uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v___x_2601_);
v___x_2604_ = 0;
v___x_2605_ = lean_box(v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2607_, v_a_2608_);
lean_dec_ref(v_a_2608_);
lean_dec_ref(v_type_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2611_, v_a_2613_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_type_2623_);
return v_res_2634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
lean_ctor_set(v___x_2640_, 2, v___x_2639_);
lean_ctor_set(v___x_2640_, 3, v___x_2638_);
lean_ctor_set(v___x_2640_, 4, v___x_2638_);
lean_ctor_set(v___x_2640_, 5, v___x_2638_);
lean_ctor_set(v___x_2640_, 6, v___x_2638_);
lean_ctor_set(v___x_2640_, 7, v___x_2638_);
lean_ctor_set(v___x_2640_, 8, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_unsigned_to_nat(32u);
v___x_2642_ = lean_mk_empty_array_with_capacity(v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2644_ = ((size_t)5ULL);
v___x_2645_ = lean_unsigned_to_nat(0u);
v___x_2646_ = lean_unsigned_to_nat(32u);
v___x_2647_ = lean_mk_empty_array_with_capacity(v___x_2646_);
v___x_2648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2649_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v___x_2647_);
lean_ctor_set(v___x_2649_, 2, v___x_2645_);
lean_ctor_set(v___x_2649_, 3, v___x_2645_);
lean_ctor_set_usize(v___x_2649_, 4, v___x_2644_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2650_ = lean_box(1);
v___x_2651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
lean_ctor_set(v___x_2653_, 1, v___x_2651_);
lean_ctor_set(v___x_2653_, 2, v___x_2650_);
return v___x_2653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2656_ = l_Lean_stringToMessageData(v___x_2655_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2659_ = l_Lean_stringToMessageData(v___x_2658_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2674_ = l_Lean_stringToMessageData(v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2675_, lean_object* v_declHint_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v_env_2680_; uint8_t v___x_2681_; 
v___x_2679_ = lean_st_ref_get(v___y_2677_);
v_env_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc_ref(v_env_2680_);
lean_dec(v___x_2679_);
v___x_2681_ = l_Lean_Name_isAnonymous(v_declHint_2676_);
if (v___x_2681_ == 0)
{
uint8_t v_isExporting_2682_; 
v_isExporting_2682_ = lean_ctor_get_uint8(v_env_2680_, sizeof(void*)*8);
if (v_isExporting_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v_env_2680_);
lean_dec(v_declHint_2676_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_msg_2675_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
lean_inc_ref(v_env_2680_);
v___x_2684_ = l_Lean_Environment_setExporting(v_env_2680_, v___x_2681_);
lean_inc(v_declHint_2676_);
lean_inc_ref(v___x_2684_);
v___x_2685_ = l_Lean_Environment_contains(v___x_2684_, v_declHint_2676_, v_isExporting_2682_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v___x_2684_);
lean_dec_ref(v_env_2680_);
lean_dec(v_declHint_2676_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_msg_2675_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_c_2692_; lean_object* v___x_2693_; 
v___x_2687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2689_ = l_Lean_Options_empty;
v___x_2690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2684_);
lean_ctor_set(v___x_2690_, 1, v___x_2687_);
lean_ctor_set(v___x_2690_, 2, v___x_2688_);
lean_ctor_set(v___x_2690_, 3, v___x_2689_);
lean_inc(v_declHint_2676_);
v___x_2691_ = l_Lean_MessageData_ofConstName(v_declHint_2676_, v___x_2681_);
v_c_2692_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2692_, 0, v___x_2690_);
lean_ctor_set(v_c_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2680_, v_declHint_2676_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec_ref(v_env_2680_);
lean_dec(v_declHint_2676_);
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v_c_2692_);
v___x_2696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_note(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_msg_2675_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
else
{
lean_object* v_val_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2736_; 
v_val_2701_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2703_ = v___x_2693_;
v_isShared_2704_ = v_isSharedCheck_2736_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_val_2701_);
lean_dec(v___x_2693_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2736_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v_mod_2708_; uint8_t v___x_2709_; 
v___x_2705_ = lean_box(0);
v___x_2706_ = l_Lean_Environment_header(v_env_2680_);
lean_dec_ref(v_env_2680_);
v___x_2707_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2706_);
v_mod_2708_ = lean_array_get(v___x_2705_, v___x_2707_, v_val_2701_);
lean_dec(v_val_2701_);
lean_dec_ref(v___x_2707_);
v___x_2709_ = l_Lean_isPrivateName(v_declHint_2676_);
lean_dec(v_declHint_2676_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v_c_2692_);
v___x_2712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofName(v_mod_2708_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_MessageData_note(v___x_2717_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_msg_2675_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set_tag(v___x_2703_, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2719_);
v___x_2721_ = v___x_2703_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2723_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v_c_2692_);
v___x_2725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l_Lean_MessageData_ofName(v_mod_2708_);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = l_Lean_MessageData_note(v___x_2730_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_msg_2675_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set_tag(v___x_2703_, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2732_);
v___x_2734_ = v___x_2703_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2737_; 
lean_dec_ref(v_env_2680_);
lean_dec(v_declHint_2676_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_msg_2675_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2738_, lean_object* v_declHint_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2738_, v_declHint_2739_, v___y_2740_);
lean_dec(v___y_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2743_, lean_object* v_declHint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2758_; 
v___x_2748_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2743_, v_declHint_2744_, v___y_2746_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2753_ = l_Lean_unknownIdentifierMessageTag;
v___x_2754_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_a_2749_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2754_);
v___x_2756_ = v___x_2751_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2759_, lean_object* v_declHint_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2759_, v_declHint_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; lean_object* v_env_2770_; lean_object* v_options_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2769_ = lean_st_ref_get(v___y_2767_);
v_env_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_env_2770_);
lean_dec(v___x_2769_);
v_options_2771_ = lean_ctor_get(v___y_2766_, 2);
v___x_2772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2773_ = lean_unsigned_to_nat(32u);
v___x_2774_ = lean_mk_empty_array_with_capacity(v___x_2773_);
lean_dec_ref(v___x_2774_);
v___x_2775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2771_);
v___x_2776_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2776_, 0, v_env_2770_);
lean_ctor_set(v___x_2776_, 1, v___x_2772_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
lean_ctor_set(v___x_2776_, 3, v_options_2771_);
v___x_2777_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_msgData_2765_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_ref_2788_; lean_object* v___x_2789_; lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2798_; 
v_ref_2788_ = lean_ctor_get(v___y_2785_, 5);
v___x_2789_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2784_, v___y_2785_, v___y_2786_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2798_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_inc(v_ref_2788_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_ref_2788_);
lean_ctor_set(v___x_2794_, 1, v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 1);
lean_ctor_set(v___x_2792_, 0, v___x_2794_);
v___x_2796_ = v___x_2792_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2804_, lean_object* v_msg_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_fileName_2809_; lean_object* v_fileMap_2810_; lean_object* v_options_2811_; lean_object* v_currRecDepth_2812_; lean_object* v_maxRecDepth_2813_; lean_object* v_ref_2814_; lean_object* v_currNamespace_2815_; lean_object* v_openDecls_2816_; lean_object* v_initHeartbeats_2817_; lean_object* v_maxHeartbeats_2818_; lean_object* v_quotContext_2819_; lean_object* v_currMacroScope_2820_; uint8_t v_diag_2821_; lean_object* v_cancelTk_x3f_2822_; uint8_t v_suppressElabErrors_2823_; lean_object* v_inheritedTraceOptions_2824_; lean_object* v_ref_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_fileName_2809_ = lean_ctor_get(v___y_2806_, 0);
v_fileMap_2810_ = lean_ctor_get(v___y_2806_, 1);
v_options_2811_ = lean_ctor_get(v___y_2806_, 2);
v_currRecDepth_2812_ = lean_ctor_get(v___y_2806_, 3);
v_maxRecDepth_2813_ = lean_ctor_get(v___y_2806_, 4);
v_ref_2814_ = lean_ctor_get(v___y_2806_, 5);
v_currNamespace_2815_ = lean_ctor_get(v___y_2806_, 6);
v_openDecls_2816_ = lean_ctor_get(v___y_2806_, 7);
v_initHeartbeats_2817_ = lean_ctor_get(v___y_2806_, 8);
v_maxHeartbeats_2818_ = lean_ctor_get(v___y_2806_, 9);
v_quotContext_2819_ = lean_ctor_get(v___y_2806_, 10);
v_currMacroScope_2820_ = lean_ctor_get(v___y_2806_, 11);
v_diag_2821_ = lean_ctor_get_uint8(v___y_2806_, sizeof(void*)*14);
v_cancelTk_x3f_2822_ = lean_ctor_get(v___y_2806_, 12);
v_suppressElabErrors_2823_ = lean_ctor_get_uint8(v___y_2806_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2824_ = lean_ctor_get(v___y_2806_, 13);
v_ref_2825_ = l_Lean_replaceRef(v_ref_2804_, v_ref_2814_);
lean_inc_ref(v_inheritedTraceOptions_2824_);
lean_inc(v_cancelTk_x3f_2822_);
lean_inc(v_currMacroScope_2820_);
lean_inc(v_quotContext_2819_);
lean_inc(v_maxHeartbeats_2818_);
lean_inc(v_initHeartbeats_2817_);
lean_inc(v_openDecls_2816_);
lean_inc(v_currNamespace_2815_);
lean_inc(v_maxRecDepth_2813_);
lean_inc(v_currRecDepth_2812_);
lean_inc_ref(v_options_2811_);
lean_inc_ref(v_fileMap_2810_);
lean_inc_ref(v_fileName_2809_);
v___x_2826_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2826_, 0, v_fileName_2809_);
lean_ctor_set(v___x_2826_, 1, v_fileMap_2810_);
lean_ctor_set(v___x_2826_, 2, v_options_2811_);
lean_ctor_set(v___x_2826_, 3, v_currRecDepth_2812_);
lean_ctor_set(v___x_2826_, 4, v_maxRecDepth_2813_);
lean_ctor_set(v___x_2826_, 5, v_ref_2825_);
lean_ctor_set(v___x_2826_, 6, v_currNamespace_2815_);
lean_ctor_set(v___x_2826_, 7, v_openDecls_2816_);
lean_ctor_set(v___x_2826_, 8, v_initHeartbeats_2817_);
lean_ctor_set(v___x_2826_, 9, v_maxHeartbeats_2818_);
lean_ctor_set(v___x_2826_, 10, v_quotContext_2819_);
lean_ctor_set(v___x_2826_, 11, v_currMacroScope_2820_);
lean_ctor_set(v___x_2826_, 12, v_cancelTk_x3f_2822_);
lean_ctor_set(v___x_2826_, 13, v_inheritedTraceOptions_2824_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*14, v_diag_2821_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*14 + 1, v_suppressElabErrors_2823_);
v___x_2827_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2805_, v___x_2826_, v___y_2807_);
lean_dec_ref(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2828_, lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2828_, v_msg_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v_ref_2828_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2834_, lean_object* v_msg_2835_, lean_object* v_declHint_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v_a_2841_; lean_object* v___x_2842_; 
v___x_2840_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2835_, v_declHint_2836_, v___y_2837_, v___y_2838_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v___x_2842_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2834_, v_a_2841_, v___y_2837_, v___y_2838_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2843_, lean_object* v_msg_2844_, lean_object* v_declHint_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2843_, v_msg_2844_, v_declHint_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v_ref_2843_);
return v_res_2849_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2852_ = l_Lean_stringToMessageData(v___x_2851_);
return v___x_2852_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2855_ = l_Lean_stringToMessageData(v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2856_, lean_object* v_constName_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2861_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2862_ = 0;
lean_inc(v_constName_2857_);
v___x_2863_ = l_Lean_MessageData_ofConstName(v_constName_2857_, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2861_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2856_, v___x_2866_, v_constName_2857_, v___y_2858_, v___y_2859_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2868_, lean_object* v_constName_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2868_, v_constName_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_ref_2868_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_ref_2878_; lean_object* v___x_2879_; 
v_ref_2878_ = lean_ctor_get(v___y_2875_, 5);
v___x_2879_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2878_, v_constName_2874_, v___y_2875_, v___y_2876_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v_env_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; 
v___x_2889_ = lean_st_ref_get(v___y_2887_);
v_env_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_ref(v_env_2890_);
lean_dec(v___x_2889_);
v___x_2891_ = 0;
lean_inc(v_constName_2885_);
v___x_2892_ = l_Lean_Environment_find_x3f(v_env_2890_, v_constName_2885_, v___x_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2885_, v___y_2886_, v___y_2887_);
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_constName_2885_);
v_val_2894_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2892_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_val_2894_);
lean_dec(v___x_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set_tag(v___x_2896_, 0);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_val_2894_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Expr_getAppFn(v_type_2907_);
if (lean_obj_tag(v___x_2911_) == 4)
{
lean_object* v_declName_2912_; lean_object* v___x_2913_; 
v_declName_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_declName_2912_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2912_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2931_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2931_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2931_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
if (lean_obj_tag(v_a_2914_) == 5)
{
lean_object* v_val_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_val_2918_ = lean_ctor_get(v_a_2914_, 0);
lean_inc_ref(v_val_2918_);
lean_dec_ref(v_a_2914_);
v___x_2919_ = l_Lean_InductiveVal_numCtors(v_val_2918_);
lean_dec_ref(v_val_2918_);
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = lean_nat_dec_le(v___x_2919_, v___x_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(v___x_2921_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2922_);
v___x_2924_ = v___x_2916_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
lean_dec(v_a_2914_);
v___x_2926_ = 0;
v___x_2927_ = lean_box(v___x_2926_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2927_);
v___x_2929_ = v___x_2916_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2913_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2913_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v___x_2911_);
v___x_2940_ = 0;
v___x_2941_ = lean_box(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec_ref(v_type_2943_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2948_, lean_object* v_constName_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2949_, v___y_2950_, v___y_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_constName_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2954_, v_constName_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2960_, lean_object* v_ref_2961_, lean_object* v_constName_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2961_, v_constName_2962_, v___y_2963_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2967_, lean_object* v_ref_2968_, lean_object* v_constName_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2967_, v_ref_2968_, v_constName_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v_ref_2968_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2974_, lean_object* v_ref_2975_, lean_object* v_msg_2976_, lean_object* v_declHint_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2975_, v_msg_2976_, v_declHint_2977_, v___y_2978_, v___y_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v_declHint_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2982_, v_ref_2983_, v_msg_2984_, v_declHint_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v_ref_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2990_, lean_object* v_declHint_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2990_, v_declHint_2991_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2996_, lean_object* v_declHint_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2996_, v_declHint_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3002_, lean_object* v_ref_3003_, lean_object* v_msg_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3003_, v_msg_3004_, v___y_3005_, v___y_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_ref_3010_, lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3009_, v_ref_3010_, v_msg_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v_ref_3010_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3016_, lean_object* v_msg_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3022_, lean_object* v_msg_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3022_, v_msg_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3028_, lean_object* v_fvarId_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_toGoalState_3035_; lean_object* v_mvarId_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3072_; 
v_toGoalState_3035_ = lean_ctor_get(v_goal_3028_, 0);
v_mvarId_3036_ = lean_ctor_get(v_goal_3028_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_goal_3028_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3038_ = v_goal_3028_;
v_isShared_3039_ = v_isSharedCheck_3072_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_mvarId_3036_);
lean_inc(v_toGoalState_3035_);
lean_dec(v_goal_3028_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3072_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3036_, v_fvarId_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3063_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3063_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3063_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
if (lean_obj_tag(v_a_3041_) == 1)
{
lean_object* v_val_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3058_; 
v_val_3045_ = lean_ctor_get(v_a_3041_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_a_3041_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3047_ = v_a_3041_;
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_val_3045_);
lean_dec(v_a_3041_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v_val_3045_);
v___x_3050_ = v___x_3038_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_toGoalState_3035_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_val_3045_);
v___x_3050_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3050_);
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3052_);
v___x_3054_ = v___x_3043_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_dec(v_a_3041_);
lean_del_object(v___x_3038_);
lean_dec_ref(v_toGoalState_3035_);
v___x_3059_ = lean_box(0);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3059_);
v___x_3061_ = v___x_3043_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
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
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_del_object(v___x_3038_);
lean_dec_ref(v_toGoalState_3035_);
v_a_3064_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3040_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3040_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3073_, lean_object* v_fvarId_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3073_, v_fvarId_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3081_, lean_object* v_x_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3081_, v_x_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_a_3097_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3088_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3088_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3105_, lean_object* v_x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3105_, v_x_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3113_, lean_object* v_mvarId_3114_, lean_object* v_x_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3114_, v_x_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_mvarId_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3122_, v_mvarId_3123_, v_x_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3131_, lean_object* v_toGoalState_3132_, lean_object* v_goal_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
lean_inc(v_mvarId_3131_);
v___x_3139_ = l_Lean_MVarId_getType(v_mvarId_3131_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v___x_3141_ = l_Lean_Meta_isProp(v_a_3140_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3168_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3168_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3168_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_unbox(v_a_3142_);
lean_dec(v_a_3142_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_del_object(v___x_3144_);
lean_dec_ref(v_goal_3133_);
v___x_3147_ = l_Lean_MVarId_exfalso(v_mvarId_3131_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3156_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_toGoalState_3132_);
lean_ctor_set(v___x_3152_, 1, v_a_3148_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v_toGoalState_3132_);
v_a_3157_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3147_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3147_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v___x_3166_; 
lean_dec_ref(v_toGoalState_3132_);
lean_dec(v_mvarId_3131_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v_goal_3133_);
v___x_3166_ = v___x_3144_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_goal_3133_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v_goal_3133_);
lean_dec_ref(v_toGoalState_3132_);
lean_dec(v_mvarId_3131_);
v_a_3169_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3141_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3141_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_goal_3133_);
lean_dec_ref(v_toGoalState_3132_);
lean_dec(v_mvarId_3131_);
v_a_3177_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3139_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3139_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3185_, lean_object* v_toGoalState_3186_, lean_object* v_goal_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3185_, v_toGoalState_3186_, v_goal_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_toGoalState_3200_; lean_object* v_mvarId_3201_; lean_object* v___f_3202_; lean_object* v___x_3203_; 
v_toGoalState_3200_ = lean_ctor_get(v_goal_3194_, 0);
lean_inc_ref(v_toGoalState_3200_);
v_mvarId_3201_ = lean_ctor_get(v_goal_3194_, 1);
lean_inc_n(v_mvarId_3201_, 2);
v___f_3202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3202_, 0, v_mvarId_3201_);
lean_closure_set(v___f_3202_, 1, v_toGoalState_3200_);
lean_closure_set(v___f_3202_, 2, v_goal_3194_);
v___x_3203_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3201_, v___f_3202_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_mvarId_3217_; lean_object* v___x_3218_; 
v_mvarId_3217_ = lean_ctor_get(v_goal_3211_, 1);
lean_inc(v_mvarId_3217_);
lean_dec_ref(v_goal_3211_);
v___x_3218_ = l_Lean_MVarId_getDecl(v_mvarId_3217_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3228_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_lctx_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v_lctx_3223_ = lean_ctor_get(v_a_3219_, 1);
lean_inc_ref(v_lctx_3223_);
lean_dec(v_a_3219_);
v___x_3224_ = l_Lean_LocalContext_lastDecl(v_lctx_3223_);
lean_dec_ref(v_lctx_3223_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3224_);
v___x_3226_ = v___x_3221_;
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
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_a_3229_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3218_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3218_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
if (lean_obj_tag(v_a_3245_) == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = l_List_reverse___redArg(v_a_3246_);
return v___x_3247_;
}
else
{
lean_object* v_head_3248_; lean_object* v_tail_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3259_; 
v_head_3248_ = lean_ctor_get(v_a_3245_, 0);
v_tail_3249_ = lean_ctor_get(v_a_3245_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_a_3245_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3251_ = v_a_3245_;
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_tail_3249_);
lean_inc(v_head_3248_);
lean_dec(v_a_3245_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3259_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_toGoalState_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v_toGoalState_3253_ = lean_ctor_get(v_goal_3244_, 0);
lean_inc_ref(v_toGoalState_3253_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_toGoalState_3253_);
lean_ctor_set(v___x_3254_, 1, v_head_3248_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v_a_3246_);
lean_ctor_set(v___x_3251_, 0, v___x_3254_);
v___x_3256_ = v___x_3251_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_a_3246_);
v___x_3256_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
v_a_3245_ = v_tail_3249_;
v_a_3246_ = v___x_3256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3260_, v_a_3261_, v_a_3262_);
lean_dec_ref(v_goal_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3264_, lean_object* v_as_x27_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
if (lean_obj_tag(v_as_x27_3265_) == 0)
{
lean_object* v___x_3277_; 
lean_dec_ref(v_kp_3264_);
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v_b_3266_);
return v___x_3277_;
}
else
{
lean_object* v_head_3278_; lean_object* v_tail_3279_; lean_object* v___x_3280_; 
v_head_3278_ = lean_ctor_get(v_as_x27_3265_, 0);
lean_inc(v_head_3278_);
v_tail_3279_ = lean_ctor_get(v_as_x27_3265_, 1);
lean_inc(v_tail_3279_);
lean_dec_ref(v_as_x27_3265_);
lean_inc_ref(v_kp_3264_);
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
lean_inc(v___y_3267_);
v___x_3280_ = lean_apply_11(v_kp_3264_, v_head_3278_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, lean_box(0));
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3280_);
if (lean_obj_tag(v_a_3281_) == 0)
{
lean_object* v_fst_3282_; lean_object* v_snd_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3293_; 
v_fst_3282_ = lean_ctor_get(v_b_3266_, 0);
v_snd_3283_ = lean_ctor_get(v_b_3266_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_b_3266_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3285_ = v_b_3266_;
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_snd_3283_);
lean_inc(v_fst_3282_);
lean_dec(v_b_3266_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3293_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_seq_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v_seq_3287_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_seq_3287_);
lean_dec_ref(v_a_3281_);
v___x_3288_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3282_, v_seq_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_snd_3283_);
v___x_3290_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v_as_x27_3265_ = v_tail_3279_;
v_b_3266_ = v___x_3290_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3294_; lean_object* v_snd_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3305_; 
v_fst_3294_ = lean_ctor_get(v_b_3266_, 0);
v_snd_3295_ = lean_ctor_get(v_b_3266_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_b_3266_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3297_ = v_b_3266_;
v_isShared_3298_ = v_isSharedCheck_3305_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_snd_3295_);
lean_inc(v_fst_3294_);
lean_dec(v_b_3266_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3305_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_gs_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v_gs_3299_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_gs_3299_);
lean_dec_ref(v_a_3281_);
v___x_3300_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3295_, v_gs_3299_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3300_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_fst_3294_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
v_as_x27_3265_ = v_tail_3279_;
v_b_3266_ = v___x_3302_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v_tail_3279_);
lean_dec_ref(v_b_3266_);
lean_dec_ref(v_kp_3264_);
v_a_3306_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3280_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3280_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3314_, lean_object* v_as_x27_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3314_, v_as_x27_3315_, v_b_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3332_, lean_object* v_mvarId_3333_, lean_object* v_goal_3334_, lean_object* v_kp_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___x_3401_; 
lean_inc(v_fvarId_3332_);
v___x_3401_ = l_Lean_FVarId_getType___redArg(v_fvarId_3332_, v___y_3341_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
v___x_3403_ = lean_whnf(v_a_3402_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___x_3426_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref(v___x_3403_);
v___x_3426_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3404_, v___y_3337_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3466_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3466_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3466_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
lean_dec(v_a_3404_);
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v___x_3432_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3432_);
v___x_3434_ = v___x_3429_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
else
{
lean_object* v___x_3436_; 
lean_del_object(v___x_3429_);
v___x_3436_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3337_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; uint8_t v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref(v___x_3436_);
v___x_3438_ = lean_unbox(v_a_3437_);
lean_dec(v_a_3437_);
if (v___x_3438_ == 0)
{
v___y_3406_ = v___y_3336_;
v___y_3407_ = v___y_3337_;
v___y_3408_ = v___y_3338_;
v___y_3409_ = v___y_3339_;
v___y_3410_ = v___y_3340_;
v___y_3411_ = v___y_3341_;
v___y_3412_ = v___y_3342_;
v___y_3413_ = v___y_3343_;
v___y_3414_ = v___y_3344_;
goto v___jp_3405_;
}
else
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3404_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3449_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_unbox(v_a_3440_);
lean_dec(v_a_3440_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
lean_dec(v_a_3404_);
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v___x_3445_ = lean_box(0);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3445_);
v___x_3447_ = v___x_3442_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
else
{
lean_del_object(v___x_3442_);
v___y_3406_ = v___y_3336_;
v___y_3407_ = v___y_3337_;
v___y_3408_ = v___y_3338_;
v___y_3409_ = v___y_3339_;
v___y_3410_ = v___y_3340_;
v___y_3411_ = v___y_3341_;
v___y_3412_ = v___y_3342_;
v___y_3413_ = v___y_3343_;
v___y_3414_ = v___y_3344_;
goto v___jp_3405_;
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v_a_3404_);
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3450_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3439_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3439_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_a_3404_);
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3458_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3436_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3436_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_a_3404_);
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3467_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3426_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3426_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
v___jp_3405_:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_Expr_getAppFn(v_a_3404_);
lean_dec(v_a_3404_);
if (lean_obj_tag(v___x_3415_) == 4)
{
lean_object* v_declName_3416_; lean_object* v___x_3417_; 
v_declName_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_declName_3416_);
lean_dec_ref(v___x_3415_);
v___x_3417_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3416_, v___y_3408_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_dec_ref(v___x_3417_);
v___y_3347_ = v___y_3406_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3408_;
v___y_3350_ = v___y_3409_;
v___y_3351_ = v___y_3410_;
v___y_3352_ = v___y_3411_;
v___y_3353_ = v___y_3412_;
v___y_3354_ = v___y_3413_;
v___y_3355_ = v___y_3414_;
goto v___jp_3346_;
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_dec_ref(v___x_3415_);
v___y_3347_ = v___y_3406_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3408_;
v___y_3350_ = v___y_3409_;
v___y_3351_ = v___y_3410_;
v___y_3352_ = v___y_3411_;
v___y_3353_ = v___y_3412_;
v___y_3354_ = v___y_3413_;
v___y_3355_ = v___y_3414_;
goto v___jp_3346_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3475_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3403_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3403_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_kp_3335_);
lean_dec(v_mvarId_3333_);
lean_dec(v_fvarId_3332_);
v_a_3483_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3401_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3401_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
v___jp_3346_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = l_Lean_mkFVar(v_fvarId_3332_);
v___x_3357_ = l_Lean_Meta_Grind_cases(v_mvarId_3333_, v___x_3356_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = lean_box(0);
v___x_3360_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3334_, v_a_3358_, v___x_3359_);
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3363_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3335_, v___x_3360_, v___x_3362_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3384_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_fst_3368_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_a_3364_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_a_3364_);
v___x_3370_ = lean_array_get_size(v_snd_3369_);
v___x_3371_ = lean_nat_dec_eq(v___x_3370_, v___x_3361_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
lean_dec(v_fst_3368_);
v___x_3372_ = lean_array_to_list(v_snd_3369_);
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3374_);
v___x_3376_ = v___x_3366_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
lean_dec(v_snd_3369_);
v___x_3378_ = lean_array_to_list(v_fst_3368_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3380_);
v___x_3382_ = v___x_3366_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
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
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_a_3385_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3363_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3363_);
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
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_kp_3335_);
v_a_3393_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3357_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3357_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3491_, lean_object* v_mvarId_3492_, lean_object* v_goal_3493_, lean_object* v_kp_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3491_, v_mvarId_3492_, v_goal_3493_, v_kp_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v_goal_3493_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3506_, lean_object* v_fvarId_3507_, lean_object* v_kp_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_mvarId_3519_; lean_object* v___f_3520_; lean_object* v___x_3521_; 
v_mvarId_3519_ = lean_ctor_get(v_goal_3506_, 1);
lean_inc_n(v_mvarId_3519_, 2);
v___f_3520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3520_, 0, v_fvarId_3507_);
lean_closure_set(v___f_3520_, 1, v_mvarId_3519_);
lean_closure_set(v___f_3520_, 2, v_goal_3506_);
lean_closure_set(v___f_3520_, 3, v_kp_3508_);
v___x_3521_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3519_, v___f_3520_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3522_, lean_object* v_fvarId_3523_, lean_object* v_kp_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3522_, v_fvarId_3523_, v_kp_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3536_, lean_object* v_as_3537_, lean_object* v_as_x27_3538_, lean_object* v_b_3539_, lean_object* v_a_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3536_, v_as_x27_3538_, v_b_3539_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3552_, lean_object* v_as_3553_, lean_object* v_as_x27_3554_, lean_object* v_b_3555_, lean_object* v_a_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3552_, v_as_3553_, v_as_x27_3554_, v_b_3555_, v_a_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec(v_as_3553_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3568_, lean_object* v_fvarId_3569_, lean_object* v_generation_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = lean_st_mk_ref(v_goal_3568_);
v___x_3582_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3569_, v_generation_3570_, v___x_3581_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3591_; 
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v___x_3582_, 0);
lean_dec(v_unused_3592_);
v___x_3584_ = v___x_3582_;
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v___x_3582_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_st_ref_get(v___x_3581_);
v___x_3587_ = lean_st_ref_get(v___x_3581_);
lean_dec(v___x_3581_);
lean_dec(v___x_3587_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3589_ = v___x_3584_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3586_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec(v___x_3581_);
v_a_3593_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3582_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3582_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3601_, lean_object* v_fvarId_3602_, lean_object* v_generation_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3601_, v_fvarId_3602_, v_generation_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3617_, lean_object* v_goal_3618_, lean_object* v_kna_3619_, lean_object* v_kp_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_toGoalState_3631_; uint8_t v_inconsistent_3632_; 
v_toGoalState_3631_ = lean_ctor_get(v_goal_3618_, 0);
v_inconsistent_3632_ = lean_ctor_get_uint8(v_toGoalState_3631_, sizeof(void*)*17);
if (v_inconsistent_3632_ == 0)
{
lean_object* v_mvarId_3633_; lean_object* v___x_3634_; 
v_mvarId_3633_ = lean_ctor_get(v_goal_3618_, 1);
lean_inc(v_mvarId_3633_);
v___x_3634_ = l_Lean_MVarId_getType(v_mvarId_3633_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; uint8_t v___x_3636_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref(v___x_3634_);
v___x_3636_ = l_Lean_Expr_isFalse(v_a_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec_ref(v_kna_3619_);
lean_inc(v_generation_3617_);
v___x_3637_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3618_, v_generation_3617_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3637_);
switch(lean_obj_tag(v_a_3638_))
{
case 0:
{
lean_object* v_goal_3639_; lean_object* v___x_3640_; 
lean_dec(v_generation_3617_);
v_goal_3639_ = lean_ctor_get(v_a_3638_, 0);
lean_inc_ref(v_goal_3639_);
lean_dec_ref(v_a_3638_);
v___x_3640_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3639_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v_toGoalState_3642_; lean_object* v_mvarId_3643_; lean_object* v___x_3644_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
v_toGoalState_3642_ = lean_ctor_get(v_a_3641_, 0);
v_mvarId_3643_ = lean_ctor_get(v_a_3641_, 1);
lean_inc(v_mvarId_3643_);
v___x_3644_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3643_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
if (lean_obj_tag(v_a_3645_) == 1)
{
lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3654_; 
lean_inc_ref(v_toGoalState_3642_);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_a_3641_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; lean_object* v_unused_3656_; 
v_unused_3655_ = lean_ctor_get(v_a_3641_, 1);
lean_dec(v_unused_3655_);
v_unused_3656_ = lean_ctor_get(v_a_3641_, 0);
lean_dec(v_unused_3656_);
v___x_3647_ = v_a_3641_;
v_isShared_3648_ = v_isSharedCheck_3654_;
goto v_resetjp_3646_;
}
else
{
lean_dec(v_a_3641_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3654_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v_val_3649_; lean_object* v___x_3651_; 
v_val_3649_ = lean_ctor_get(v_a_3645_, 0);
lean_inc(v_val_3649_);
lean_dec_ref(v_a_3645_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 1, v_val_3649_);
v___x_3651_ = v___x_3647_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_toGoalState_3642_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_val_3649_);
v___x_3651_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; 
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3652_ = lean_apply_11(v_kp_3620_, v___x_3651_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3652_;
}
}
}
else
{
lean_object* v___x_3657_; 
lean_dec(v_a_3645_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3657_ = lean_apply_11(v_kp_3620_, v_a_3641_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3657_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_a_3641_);
lean_dec_ref(v_kp_3620_);
v_a_3658_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3644_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3644_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref(v_kp_3620_);
v_a_3666_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3640_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3640_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3674_; lean_object* v_goal_3675_; lean_object* v___x_3676_; 
v_fvarId_3674_ = lean_ctor_get(v_a_3638_, 0);
lean_inc_n(v_fvarId_3674_, 2);
v_goal_3675_ = lean_ctor_get(v_a_3638_, 1);
lean_inc_ref_n(v_goal_3675_, 2);
lean_dec_ref(v_a_3638_);
v___x_3676_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3675_, v_fvarId_3674_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
if (lean_obj_tag(v_a_3677_) == 1)
{
lean_object* v_val_3678_; lean_object* v___x_3679_; 
lean_dec_ref(v_goal_3675_);
lean_dec(v_fvarId_3674_);
lean_dec(v_generation_3617_);
v_val_3678_ = lean_ctor_get(v_a_3677_, 0);
lean_inc(v_val_3678_);
lean_dec_ref(v_a_3677_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3679_ = lean_apply_11(v_kp_3620_, v_val_3678_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3679_;
}
else
{
lean_object* v___x_3680_; 
lean_dec(v_a_3677_);
lean_inc_ref(v_kp_3620_);
lean_inc(v_fvarId_3674_);
lean_inc_ref(v_goal_3675_);
v___x_3680_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3675_, v_fvarId_3674_, v_kp_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3702_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3702_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3702_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
if (lean_obj_tag(v_a_3681_) == 1)
{
lean_object* v_val_3685_; lean_object* v___x_3687_; 
lean_dec_ref(v_goal_3675_);
lean_dec(v_fvarId_3674_);
lean_dec_ref(v_kp_3620_);
lean_dec(v_generation_3617_);
v_val_3685_ = lean_ctor_get(v_a_3681_, 0);
lean_inc(v_val_3685_);
lean_dec_ref(v_a_3681_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v_val_3685_);
v___x_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_val_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
else
{
lean_object* v_mvarId_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; 
lean_del_object(v___x_3683_);
lean_dec(v_a_3681_);
v_mvarId_3689_ = lean_ctor_get(v_goal_3675_, 1);
lean_inc(v_mvarId_3689_);
v___f_3690_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3690_, 0, v_goal_3675_);
lean_closure_set(v___f_3690_, 1, v_fvarId_3674_);
lean_closure_set(v___f_3690_, 2, v_generation_3617_);
v___x_3691_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3689_, v___f_3690_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref(v___x_3691_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3693_ = lean_apply_11(v_kp_3620_, v_a_3692_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3693_;
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v_kp_3620_);
v_a_3694_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3691_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3691_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_goal_3675_);
lean_dec(v_fvarId_3674_);
lean_dec_ref(v_kp_3620_);
lean_dec(v_generation_3617_);
v_a_3703_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3680_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3680_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref(v_goal_3675_);
lean_dec(v_fvarId_3674_);
lean_dec_ref(v_kp_3620_);
lean_dec(v_generation_3617_);
v_a_3711_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3676_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3676_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
case 2:
{
lean_object* v_goal_3719_; lean_object* v___x_3720_; 
lean_dec(v_generation_3617_);
v_goal_3719_ = lean_ctor_get(v_a_3638_, 0);
lean_inc_ref(v_goal_3719_);
lean_dec_ref(v_a_3638_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3720_ = lean_apply_11(v_kp_3620_, v_goal_3719_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3720_;
}
default: 
{
lean_object* v_fvarId_3721_; lean_object* v_goal_3722_; lean_object* v___x_3723_; 
lean_dec(v_generation_3617_);
v_fvarId_3721_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_fvarId_3721_);
v_goal_3722_ = lean_ctor_get(v_a_3638_, 1);
lean_inc_ref_n(v_goal_3722_, 2);
lean_dec_ref(v_a_3638_);
lean_inc_ref(v_kp_3620_);
v___x_3723_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3722_, v_fvarId_3721_, v_kp_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3733_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3733_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3733_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
if (lean_obj_tag(v_a_3724_) == 1)
{
lean_object* v_val_3728_; lean_object* v___x_3730_; 
lean_dec_ref(v_goal_3722_);
lean_dec_ref(v_kp_3620_);
v_val_3728_ = lean_ctor_get(v_a_3724_, 0);
lean_inc(v_val_3728_);
lean_dec_ref(v_a_3724_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v_val_3728_);
v___x_3730_ = v___x_3726_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_val_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
else
{
lean_object* v___x_3732_; 
lean_del_object(v___x_3726_);
lean_dec(v_a_3724_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3732_ = lean_apply_11(v_kp_3620_, v_goal_3722_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3732_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_goal_3722_);
lean_dec_ref(v_kp_3620_);
v_a_3734_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3723_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3723_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v_kp_3620_);
lean_dec(v_generation_3617_);
v_a_3742_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3637_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3637_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
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
else
{
lean_object* v___x_3750_; 
lean_dec_ref(v_kp_3620_);
lean_dec(v_generation_3617_);
lean_inc(v_a_3629_);
lean_inc_ref(v_a_3628_);
lean_inc(v_a_3627_);
lean_inc_ref(v_a_3626_);
lean_inc(v_a_3625_);
lean_inc_ref(v_a_3624_);
lean_inc(v_a_3623_);
lean_inc_ref(v_a_3622_);
lean_inc(v_a_3621_);
v___x_3750_ = lean_apply_11(v_kna_3619_, v_goal_3618_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, lean_box(0));
return v___x_3750_;
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v_kp_3620_);
lean_dec_ref(v_kna_3619_);
lean_dec_ref(v_goal_3618_);
lean_dec(v_generation_3617_);
v_a_3751_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3634_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3634_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec_ref(v_kp_3620_);
lean_dec_ref(v_kna_3619_);
lean_dec_ref(v_goal_3618_);
lean_dec(v_generation_3617_);
v___x_3759_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3761_, lean_object* v_goal_3762_, lean_object* v_kna_3763_, lean_object* v_kp_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Meta_Grind_Action_intro(v_generation_3761_, v_goal_3762_, v_kna_3763_, v_kp_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
return v_res_3775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_unsigned_to_nat(1000000u);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3777_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3792_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3805_, lean_object* v___f_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3820_ = lean_unsigned_to_nat(1000000u);
v___x_3821_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3821_, 0, v_generation_3805_);
v___x_3822_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3822_, 0, v___x_3820_);
lean_closure_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l_Lean_Meta_Grind_Action_andThen(v___x_3822_, v___f_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3824_, lean_object* v___f_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3824_, v___f_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3842_, lean_object* v_a_3843_, lean_object* v_kna_3844_, lean_object* v_kp_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v___f_3856_; lean_object* v___f_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___f_3856_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3857_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3857_, 0, v_generation_3842_);
lean_closure_set(v___f_3857_, 1, v___f_3856_);
v___x_3858_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3859_ = l_Lean_Meta_Grind_Action_andThen(v___x_3858_, v___f_3857_, v_a_3843_, v_kna_3844_, v_kp_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3860_, lean_object* v_a_3861_, lean_object* v_kna_3862_, lean_object* v_kp_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_Meta_Grind_Action_intros(v_generation_3860_, v_a_3861_, v_kna_3862_, v_kp_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
return v_res_3874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3884_ = l_Lean_mkConst(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3885_, lean_object* v_prop_3886_, lean_object* v_proof_3887_, lean_object* v_generation_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_st_mk_ref(v_goal_3885_);
lean_inc(v___y_3897_);
lean_inc_ref(v___y_3896_);
lean_inc(v___y_3895_);
lean_inc_ref(v___y_3894_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc(v___y_3889_);
lean_inc(v___x_3899_);
lean_inc_ref(v_prop_3886_);
v___x_3900_ = lean_grind_preprocess(v_prop_3886_, v___x_3899_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v_expr_3902_; lean_object* v___x_3903_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref(v___x_3900_);
v_expr_3902_ = lean_ctor_get(v_a_3901_, 0);
lean_inc_ref(v_expr_3902_);
v___x_3903_ = l_Lean_Meta_Simp_Result_getProof(v_a_3901_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3902_);
v___x_3906_ = l_Lean_mkApp4(v___x_3905_, v_prop_3886_, v_expr_3902_, v_a_3904_, v_proof_3887_);
v___x_3907_ = l_Lean_Meta_Grind_add(v_expr_3902_, v___x_3906_, v_generation_3888_, v___x_3899_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3916_; 
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v___x_3907_, 0);
lean_dec(v_unused_3917_);
v___x_3909_ = v___x_3907_;
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v___x_3907_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3916_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3911_ = lean_st_ref_get(v___x_3899_);
v___x_3912_ = lean_st_ref_get(v___x_3899_);
lean_dec(v___x_3899_);
lean_dec(v___x_3912_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3911_);
v___x_3914_ = v___x_3909_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3911_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v___x_3899_);
v_a_3918_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3907_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3907_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v_expr_3902_);
lean_dec(v___x_3899_);
lean_dec(v_generation_3888_);
lean_dec_ref(v_proof_3887_);
lean_dec_ref(v_prop_3886_);
v_a_3926_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3903_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3903_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v___x_3899_);
lean_dec(v_generation_3888_);
lean_dec_ref(v_proof_3887_);
lean_dec_ref(v_prop_3886_);
v_a_3934_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3900_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3900_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3942_, lean_object* v_prop_3943_, lean_object* v_proof_3944_, lean_object* v_generation_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3942_, v_prop_3943_, v_proof_3944_, v_generation_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3957_, lean_object* v___f_3958_, lean_object* v_kp_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3957_, v___f_3958_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___x_3970_);
lean_inc(v___y_3968_);
lean_inc_ref(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
lean_inc(v___y_3964_);
lean_inc_ref(v___y_3963_);
lean_inc(v___y_3962_);
lean_inc_ref(v___y_3961_);
lean_inc(v___y_3960_);
v___x_3972_ = lean_apply_11(v_kp_3959_, v_a_3971_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, lean_box(0));
return v___x_3972_;
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v_kp_3959_);
v_a_3973_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3970_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3970_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3981_, lean_object* v___f_3982_, lean_object* v_kp_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3981_, v___f_3982_, v_kp_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3995_, lean_object* v_prop_3996_, lean_object* v_generation_3997_, lean_object* v_goal_3998_, lean_object* v_kna_3999_, lean_object* v_kp_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3996_, v_a_4002_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; uint8_t v___x_4013_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref(v___x_4011_);
v___x_4013_ = lean_unbox(v_a_4012_);
lean_dec(v_a_4012_);
if (v___x_4013_ == 0)
{
lean_object* v_mvarId_4014_; lean_object* v___f_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; 
lean_dec_ref(v_kna_3999_);
v_mvarId_4014_ = lean_ctor_get(v_goal_3998_, 1);
lean_inc_n(v_mvarId_4014_, 2);
v___f_4015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4015_, 0, v_goal_3998_);
lean_closure_set(v___f_4015_, 1, v_prop_3996_);
lean_closure_set(v___f_4015_, 2, v_proof_3995_);
lean_closure_set(v___f_4015_, 3, v_generation_3997_);
v___f_4016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4016_, 0, v_mvarId_4014_);
lean_closure_set(v___f_4016_, 1, v___f_4015_);
lean_closure_set(v___f_4016_, 2, v_kp_4000_);
v___x_4017_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4014_, v___f_4016_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4017_;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4019_ = l_Lean_Core_mkFreshUserName(v___x_4018_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v_toGoalState_4021_; lean_object* v_mvarId_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4040_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4019_);
v_toGoalState_4021_ = lean_ctor_get(v_goal_3998_, 0);
v_mvarId_4022_ = lean_ctor_get(v_goal_3998_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_goal_3998_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4024_ = v_goal_3998_;
v_isShared_4025_ = v_isSharedCheck_4040_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_mvarId_4022_);
lean_inc(v_toGoalState_4021_);
lean_dec(v_goal_3998_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4040_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_MVarId_assert(v_mvarId_4022_, v_a_4020_, v_prop_3996_, v_proof_3995_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4026_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 1, v_a_4027_);
v___x_4029_ = v___x_4024_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_toGoalState_4021_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_a_4027_);
v___x_4029_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_Grind_Action_intros(v_generation_3997_, v___x_4029_, v_kna_3999_, v_kp_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4030_;
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_del_object(v___x_4024_);
lean_dec_ref(v_toGoalState_4021_);
lean_dec_ref(v_kp_4000_);
lean_dec_ref(v_kna_3999_);
lean_dec(v_generation_3997_);
v_a_4032_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4026_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4026_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v_kp_4000_);
lean_dec_ref(v_kna_3999_);
lean_dec_ref(v_goal_3998_);
lean_dec(v_generation_3997_);
lean_dec_ref(v_prop_3996_);
lean_dec_ref(v_proof_3995_);
v_a_4041_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4019_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4019_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v_kp_4000_);
lean_dec_ref(v_kna_3999_);
lean_dec_ref(v_goal_3998_);
lean_dec(v_generation_3997_);
lean_dec_ref(v_prop_3996_);
lean_dec_ref(v_proof_3995_);
v_a_4049_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4011_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4011_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4057_, lean_object* v_prop_4058_, lean_object* v_generation_4059_, lean_object* v_goal_4060_, lean_object* v_kna_4061_, lean_object* v_kp_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4057_, v_prop_4058_, v_generation_4059_, v_goal_4060_, v_kna_4061_, v_kp_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(lean_object* v_splitSource_4074_, lean_object* v_x_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_simp_4086_; lean_object* v_simpMethods_4087_; lean_object* v_config_4088_; lean_object* v_anchorRefs_x3f_4089_; uint8_t v_cheapCases_4090_; uint8_t v_reportMVarIssue_4091_; lean_object* v_symPrios_4092_; lean_object* v_extensions_4093_; uint8_t v_debug_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_simp_4086_ = lean_ctor_get(v___y_4077_, 0);
v_simpMethods_4087_ = lean_ctor_get(v___y_4077_, 1);
v_config_4088_ = lean_ctor_get(v___y_4077_, 2);
v_anchorRefs_x3f_4089_ = lean_ctor_get(v___y_4077_, 3);
v_cheapCases_4090_ = lean_ctor_get_uint8(v___y_4077_, sizeof(void*)*7);
v_reportMVarIssue_4091_ = lean_ctor_get_uint8(v___y_4077_, sizeof(void*)*7 + 1);
v_symPrios_4092_ = lean_ctor_get(v___y_4077_, 5);
v_extensions_4093_ = lean_ctor_get(v___y_4077_, 6);
v_debug_4094_ = lean_ctor_get_uint8(v___y_4077_, sizeof(void*)*7 + 2);
lean_inc_ref(v_extensions_4093_);
lean_inc_ref(v_symPrios_4092_);
lean_inc(v_anchorRefs_x3f_4089_);
lean_inc_ref(v_config_4088_);
lean_inc_ref(v_simpMethods_4087_);
lean_inc_ref(v_simp_4086_);
v___x_4095_ = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(v___x_4095_, 0, v_simp_4086_);
lean_ctor_set(v___x_4095_, 1, v_simpMethods_4087_);
lean_ctor_set(v___x_4095_, 2, v_config_4088_);
lean_ctor_set(v___x_4095_, 3, v_anchorRefs_x3f_4089_);
lean_ctor_set(v___x_4095_, 4, v_splitSource_4074_);
lean_ctor_set(v___x_4095_, 5, v_symPrios_4092_);
lean_ctor_set(v___x_4095_, 6, v_extensions_4093_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*7, v_cheapCases_4090_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*7 + 1, v_reportMVarIssue_4091_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*7 + 2, v_debug_4094_);
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4083_);
lean_inc(v___y_4082_);
lean_inc_ref(v___y_4081_);
lean_inc(v___y_4080_);
lean_inc_ref(v___y_4079_);
lean_inc(v___y_4078_);
lean_inc(v___y_4076_);
v___x_4096_ = lean_apply_10(v_x_4075_, v___y_4076_, v___x_4095_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, lean_box(0));
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg___boxed(lean_object* v_splitSource_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4097_, v_x_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0(lean_object* v_00_u03b1_4110_, lean_object* v_splitSource_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4111_, v_x_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___boxed(lean_object* v_00_u03b1_4124_, lean_object* v_splitSource_4125_, lean_object* v_x_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0(v_00_u03b1_4124_, v_splitSource_4125_, v_x_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4138_, lean_object* v_kna_4139_, lean_object* v_kp_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_toGoalState_4151_; uint8_t v_inconsistent_4152_; 
v_toGoalState_4151_ = lean_ctor_get(v_goal_4138_, 0);
lean_inc_ref(v_toGoalState_4151_);
v_inconsistent_4152_ = lean_ctor_get_uint8(v_toGoalState_4151_, sizeof(void*)*17);
if (v_inconsistent_4152_ == 0)
{
lean_object* v_mvarId_4153_; lean_object* v_nextDeclIdx_4154_; lean_object* v_enodeMap_4155_; lean_object* v_exprs_4156_; lean_object* v_parents_4157_; lean_object* v_congrTable_4158_; lean_object* v_appMap_4159_; lean_object* v_indicesFound_4160_; lean_object* v_newFacts_4161_; lean_object* v_nextIdx_4162_; lean_object* v_newRawFacts_4163_; lean_object* v_facts_4164_; lean_object* v_extThms_4165_; lean_object* v_ematch_4166_; lean_object* v_inj_4167_; lean_object* v_split_4168_; lean_object* v_clean_4169_; lean_object* v_sstates_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4197_; 
v_mvarId_4153_ = lean_ctor_get(v_goal_4138_, 1);
v_nextDeclIdx_4154_ = lean_ctor_get(v_toGoalState_4151_, 0);
v_enodeMap_4155_ = lean_ctor_get(v_toGoalState_4151_, 1);
v_exprs_4156_ = lean_ctor_get(v_toGoalState_4151_, 2);
v_parents_4157_ = lean_ctor_get(v_toGoalState_4151_, 3);
v_congrTable_4158_ = lean_ctor_get(v_toGoalState_4151_, 4);
v_appMap_4159_ = lean_ctor_get(v_toGoalState_4151_, 5);
v_indicesFound_4160_ = lean_ctor_get(v_toGoalState_4151_, 6);
v_newFacts_4161_ = lean_ctor_get(v_toGoalState_4151_, 7);
v_nextIdx_4162_ = lean_ctor_get(v_toGoalState_4151_, 8);
v_newRawFacts_4163_ = lean_ctor_get(v_toGoalState_4151_, 9);
v_facts_4164_ = lean_ctor_get(v_toGoalState_4151_, 10);
v_extThms_4165_ = lean_ctor_get(v_toGoalState_4151_, 11);
v_ematch_4166_ = lean_ctor_get(v_toGoalState_4151_, 12);
v_inj_4167_ = lean_ctor_get(v_toGoalState_4151_, 13);
v_split_4168_ = lean_ctor_get(v_toGoalState_4151_, 14);
v_clean_4169_ = lean_ctor_get(v_toGoalState_4151_, 15);
v_sstates_4170_ = lean_ctor_get(v_toGoalState_4151_, 16);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_toGoalState_4151_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4172_ = v_toGoalState_4151_;
v_isShared_4173_ = v_isSharedCheck_4197_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_sstates_4170_);
lean_inc(v_clean_4169_);
lean_inc(v_split_4168_);
lean_inc(v_inj_4167_);
lean_inc(v_ematch_4166_);
lean_inc(v_extThms_4165_);
lean_inc(v_facts_4164_);
lean_inc(v_newRawFacts_4163_);
lean_inc(v_nextIdx_4162_);
lean_inc(v_newFacts_4161_);
lean_inc(v_indicesFound_4160_);
lean_inc(v_appMap_4159_);
lean_inc(v_congrTable_4158_);
lean_inc(v_parents_4157_);
lean_inc(v_exprs_4156_);
lean_inc(v_enodeMap_4155_);
lean_inc(v_nextDeclIdx_4154_);
lean_dec(v_toGoalState_4151_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4197_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4163_);
if (lean_obj_tag(v___x_4174_) == 1)
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4193_; 
lean_inc(v_mvarId_4153_);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_goal_4138_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; lean_object* v_unused_4195_; 
v_unused_4194_ = lean_ctor_get(v_goal_4138_, 1);
lean_dec(v_unused_4194_);
v_unused_4195_ = lean_ctor_get(v_goal_4138_, 0);
lean_dec(v_unused_4195_);
v___x_4176_ = v_goal_4138_;
v_isShared_4177_ = v_isSharedCheck_4193_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v_goal_4138_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4193_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_val_4178_; lean_object* v_fst_4179_; lean_object* v_snd_4180_; lean_object* v_proof_4181_; lean_object* v_prop_4182_; lean_object* v_generation_4183_; lean_object* v_splitSource_4184_; lean_object* v___x_4186_; 
v_val_4178_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_val_4178_);
lean_dec_ref(v___x_4174_);
v_fst_4179_ = lean_ctor_get(v_val_4178_, 0);
lean_inc(v_fst_4179_);
v_snd_4180_ = lean_ctor_get(v_val_4178_, 1);
lean_inc(v_snd_4180_);
lean_dec(v_val_4178_);
v_proof_4181_ = lean_ctor_get(v_fst_4179_, 0);
lean_inc_ref(v_proof_4181_);
v_prop_4182_ = lean_ctor_get(v_fst_4179_, 1);
lean_inc_ref(v_prop_4182_);
v_generation_4183_ = lean_ctor_get(v_fst_4179_, 2);
lean_inc(v_generation_4183_);
v_splitSource_4184_ = lean_ctor_get(v_fst_4179_, 3);
lean_inc(v_splitSource_4184_);
lean_dec(v_fst_4179_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 9, v_snd_4180_);
v___x_4186_ = v___x_4172_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_nextDeclIdx_4154_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_enodeMap_4155_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_exprs_4156_);
lean_ctor_set(v_reuseFailAlloc_4192_, 3, v_parents_4157_);
lean_ctor_set(v_reuseFailAlloc_4192_, 4, v_congrTable_4158_);
lean_ctor_set(v_reuseFailAlloc_4192_, 5, v_appMap_4159_);
lean_ctor_set(v_reuseFailAlloc_4192_, 6, v_indicesFound_4160_);
lean_ctor_set(v_reuseFailAlloc_4192_, 7, v_newFacts_4161_);
lean_ctor_set(v_reuseFailAlloc_4192_, 8, v_nextIdx_4162_);
lean_ctor_set(v_reuseFailAlloc_4192_, 9, v_snd_4180_);
lean_ctor_set(v_reuseFailAlloc_4192_, 10, v_facts_4164_);
lean_ctor_set(v_reuseFailAlloc_4192_, 11, v_extThms_4165_);
lean_ctor_set(v_reuseFailAlloc_4192_, 12, v_ematch_4166_);
lean_ctor_set(v_reuseFailAlloc_4192_, 13, v_inj_4167_);
lean_ctor_set(v_reuseFailAlloc_4192_, 14, v_split_4168_);
lean_ctor_set(v_reuseFailAlloc_4192_, 15, v_clean_4169_);
lean_ctor_set(v_reuseFailAlloc_4192_, 16, v_sstates_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4192_, sizeof(void*)*17, v_inconsistent_4152_);
v___x_4186_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v_goal_4188_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4186_);
v_goal_4188_ = v___x_4176_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4186_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v_mvarId_4153_);
v_goal_4188_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed), 16, 6);
lean_closure_set(v___x_4189_, 0, v_proof_4181_);
lean_closure_set(v___x_4189_, 1, v_prop_4182_);
lean_closure_set(v___x_4189_, 2, v_generation_4183_);
lean_closure_set(v___x_4189_, 3, v_goal_4188_);
lean_closure_set(v___x_4189_, 4, v_kna_4139_);
lean_closure_set(v___x_4189_, 5, v_kp_4140_);
v___x_4190_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4184_, v___x_4189_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4190_;
}
}
}
}
else
{
lean_object* v___x_4196_; 
lean_dec(v___x_4174_);
lean_del_object(v___x_4172_);
lean_dec_ref(v_sstates_4170_);
lean_dec_ref(v_clean_4169_);
lean_dec_ref(v_split_4168_);
lean_dec_ref(v_inj_4167_);
lean_dec_ref(v_ematch_4166_);
lean_dec_ref(v_extThms_4165_);
lean_dec_ref(v_facts_4164_);
lean_dec(v_nextIdx_4162_);
lean_dec_ref(v_newFacts_4161_);
lean_dec_ref(v_indicesFound_4160_);
lean_dec_ref(v_appMap_4159_);
lean_dec_ref(v_congrTable_4158_);
lean_dec_ref(v_parents_4157_);
lean_dec_ref(v_exprs_4156_);
lean_dec_ref(v_enodeMap_4155_);
lean_dec(v_nextDeclIdx_4154_);
lean_dec_ref(v_kp_4140_);
lean_inc(v_a_4149_);
lean_inc_ref(v_a_4148_);
lean_inc(v_a_4147_);
lean_inc_ref(v_a_4146_);
lean_inc(v_a_4145_);
lean_inc_ref(v_a_4144_);
lean_inc(v_a_4143_);
lean_inc_ref(v_a_4142_);
lean_inc(v_a_4141_);
v___x_4196_ = lean_apply_11(v_kna_4139_, v_goal_4138_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, lean_box(0));
return v___x_4196_;
}
}
}
else
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_dec_ref(v_toGoalState_4151_);
lean_dec_ref(v_kp_4140_);
lean_dec_ref(v_kna_4139_);
lean_dec_ref(v_goal_4138_);
v___x_4198_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4200_, lean_object* v_kna_4201_, lean_object* v_kp_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4200_, v_kna_4201_, v_kp_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4214_, lean_object* v_kp_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = lean_unsigned_to_nat(1000000u);
v___x_4227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4228_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4226_, v___x_4227_, v_a_4214_, v_kp_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4229_, lean_object* v_kp_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4229_, v_kp_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4242_, lean_object* v_kna_4243_, lean_object* v_kp_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4242_, v_kp_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4256_, lean_object* v_kna_4257_, lean_object* v_kp_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4256_, v_kna_4257_, v_kp_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec_ref(v_kna_4257_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4270_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4285_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4298_, lean_object* v___f_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Meta_Grind_Action_andThen(v_a_4298_, v___f_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4314_, lean_object* v___f_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4314_, v___f_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4342_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4342_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4342_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___f_4337_; lean_object* v___f_4338_; lean_object* v___x_4340_; 
v___f_4337_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4338_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4338_, 0, v_a_4333_);
lean_closure_set(v___f_4338_, 1, v___f_4337_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___f_4338_);
v___x_4340_ = v___x_4335_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___f_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
else
{
return v___x_4332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4344_;
}
}
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult_default);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
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
