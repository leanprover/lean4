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
size_t v_x_37006__boxed_407_; size_t v_x_37007__boxed_408_; lean_object* v_res_409_; 
v_x_37006__boxed_407_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_x_37007__boxed_408_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_res_409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_402_, v_x_37006__boxed_407_, v_x_37007__boxed_408_, v_x_405_, v_x_406_);
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
size_t v_x_37211__boxed_457_; uint8_t v_res_458_; lean_object* v_r_459_; 
v_x_37211__boxed_457_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_res_458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_454_, v_x_37211__boxed_457_, v_x_456_);
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
lean_object* v_es_525_; lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v_j_530_; lean_object* v___x_531_; 
v_es_525_ = lean_ctor_get(v_x_522_, 0);
v___x_526_ = lean_box(2);
v___x_527_ = ((size_t)5ULL);
v___x_528_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_529_ = lean_usize_land(v_x_523_, v___x_528_);
v_j_530_ = lean_usize_to_nat(v___x_529_);
v___x_531_ = lean_array_get_borrowed(v___x_526_, v_es_525_, v_j_530_);
lean_dec(v_j_530_);
switch(lean_obj_tag(v___x_531_))
{
case 0:
{
lean_object* v_key_532_; lean_object* v_val_533_; uint8_t v___x_534_; 
v_key_532_ = lean_ctor_get(v___x_531_, 0);
v_val_533_ = lean_ctor_get(v___x_531_, 1);
v___x_534_ = lean_name_eq(v_x_524_, v_key_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
lean_inc(v_val_533_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_val_533_);
return v___x_536_;
}
}
case 1:
{
lean_object* v_node_537_; size_t v___x_538_; 
v_node_537_ = lean_ctor_get(v___x_531_, 0);
v___x_538_ = lean_usize_shift_right(v_x_523_, v___x_527_);
v_x_522_ = v_node_537_;
v_x_523_ = v___x_538_;
goto _start;
}
default: 
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
}
}
else
{
lean_object* v_ks_541_; lean_object* v_vs_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_ks_541_ = lean_ctor_get(v_x_522_, 0);
v_vs_542_ = lean_ctor_get(v_x_522_, 1);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_541_, v_vs_542_, v___x_543_, v_x_524_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
size_t v_x_37342__boxed_548_; lean_object* v_res_549_; 
v_x_37342__boxed_548_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_545_, v_x_37342__boxed_548_, v_x_547_);
lean_dec(v_x_547_);
lean_dec_ref(v_x_545_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint64_t v___y_553_; 
if (lean_obj_tag(v_x_551_) == 0)
{
uint64_t v___x_556_; 
v___x_556_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_553_ = v___x_556_;
goto v___jp_552_;
}
else
{
uint64_t v_hash_557_; 
v_hash_557_ = lean_ctor_get_uint64(v_x_551_, sizeof(void*)*2);
v___y_553_ = v_hash_557_;
goto v___jp_552_;
}
v___jp_552_:
{
size_t v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_uint64_to_usize(v___y_553_);
v___x_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_550_, v___x_554_, v_x_551_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec_ref(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_564_, lean_object* v_type_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_name_578_; lean_object* v___y_579_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v_name_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___x_731_; 
v___x_731_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_568_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_792_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_792_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_792_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_792_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
uint8_t v_clean_757_; 
v_clean_757_ = lean_ctor_get_uint8(v_a_732_, sizeof(void*)*12 + 16);
lean_dec(v_a_732_);
if (v_clean_757_ == 0)
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_564_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_761_; 
lean_dec_ref(v_type_565_);
lean_dec(v_name_564_);
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_758_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v_val_759_);
v___x_761_ = v___x_734_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_val_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
uint8_t v___x_763_; 
lean_dec(v___x_758_);
v___x_763_ = l_Lean_Name_hasMacroScopes(v_name_564_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_del_object(v___x_734_);
lean_dec_ref(v_type_565_);
v___x_764_ = l_Lean_Core_mkFreshUserName(v_name_564_, v_a_574_, v_a_575_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc(v_name_564_);
v___x_765_ = lean_erase_macro_scopes(v_name_564_);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_767_ = lean_name_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_769_ = lean_name_eq(v___x_765_, v___x_768_);
lean_dec(v___x_765_);
if (v___x_769_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_type_565_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v_name_564_);
v___x_771_ = v___x_734_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_name_564_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_del_object(v___x_734_);
goto v___jp_736_;
}
}
else
{
lean_dec(v___x_765_);
lean_del_object(v___x_734_);
goto v___jp_736_;
}
}
}
}
else
{
uint8_t v___x_773_; 
lean_del_object(v___x_734_);
v___x_773_ = l_Lean_Name_hasMacroScopes(v_name_564_);
if (v___x_773_ == 0)
{
v_name_706_ = v_name_564_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
v___y_711_ = v_a_570_;
v___y_712_ = v_a_571_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
goto v___jp_705_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_774_ = lean_erase_macro_scopes(v_name_564_);
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_789_ = lean_name_eq(v___x_774_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_791_ = lean_name_eq(v___x_774_, v___x_790_);
if (v___x_791_ == 0)
{
v_name_706_ = v___x_774_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
v___y_711_ = v_a_570_;
v___y_712_ = v_a_571_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
goto v___jp_705_;
}
else
{
goto v___jp_775_;
}
}
else
{
goto v___jp_775_;
}
v___jp_775_:
{
lean_object* v___x_776_; 
lean_inc_ref(v_type_565_);
v___x_776_ = l_Lean_Meta_isProp(v_type_565_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; uint8_t v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = lean_unbox(v_a_777_);
lean_dec(v_a_777_);
if (v___x_778_ == 0)
{
v_name_706_ = v___x_774_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
v___y_711_ = v_a_570_;
v___y_712_ = v_a_571_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
goto v___jp_705_;
}
else
{
lean_object* v___x_779_; 
lean_dec(v___x_774_);
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_706_ = v___x_779_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
v___y_711_ = v_a_570_;
v___y_712_ = v_a_571_;
v___y_713_ = v_a_572_;
v___y_714_ = v_a_573_;
v___y_715_ = v_a_574_;
v___y_716_ = v_a_575_;
goto v___jp_705_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v___x_774_);
lean_dec_ref(v_type_565_);
v_a_780_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_776_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_776_);
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
}
}
}
v___jp_736_:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_isProp(v_type_565_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_748_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_748_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v___x_742_; 
v___x_742_ = lean_unbox(v_a_738_);
lean_dec(v_a_738_);
if (v___x_742_ == 0)
{
lean_object* v___x_744_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_name_564_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_name_564_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_740_);
lean_dec(v_name_564_);
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_747_ = l_Lean_Core_mkFreshUserName(v___x_746_, v_a_574_, v_a_575_);
return v___x_747_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_name_564_);
v_a_749_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_737_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_737_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_type_565_);
lean_dec(v_name_564_);
v_a_793_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_731_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_731_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
v___jp_577_:
{
lean_object* v___x_580_; lean_object* v_toGoalState_581_; lean_object* v_clean_582_; lean_object* v_mvarId_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_628_; 
v___x_580_ = lean_st_ref_take(v___y_579_);
v_toGoalState_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_ref(v_toGoalState_581_);
v_clean_582_ = lean_ctor_get(v_toGoalState_581_, 15);
lean_inc_ref(v_clean_582_);
v_mvarId_583_ = lean_ctor_get(v___x_580_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_629_);
v___x_585_ = v___x_580_;
v_isShared_586_ = v_isSharedCheck_628_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_mvarId_583_);
lean_dec(v___x_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_628_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_nextDeclIdx_587_; lean_object* v_enodeMap_588_; lean_object* v_exprs_589_; lean_object* v_parents_590_; lean_object* v_congrTable_591_; lean_object* v_appMap_592_; lean_object* v_indicesFound_593_; lean_object* v_newFacts_594_; uint8_t v_inconsistent_595_; lean_object* v_nextIdx_596_; lean_object* v_newRawFacts_597_; lean_object* v_facts_598_; lean_object* v_extThms_599_; lean_object* v_ematch_600_; lean_object* v_inj_601_; lean_object* v_split_602_; lean_object* v_sstates_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_626_; 
v_nextDeclIdx_587_ = lean_ctor_get(v_toGoalState_581_, 0);
v_enodeMap_588_ = lean_ctor_get(v_toGoalState_581_, 1);
v_exprs_589_ = lean_ctor_get(v_toGoalState_581_, 2);
v_parents_590_ = lean_ctor_get(v_toGoalState_581_, 3);
v_congrTable_591_ = lean_ctor_get(v_toGoalState_581_, 4);
v_appMap_592_ = lean_ctor_get(v_toGoalState_581_, 5);
v_indicesFound_593_ = lean_ctor_get(v_toGoalState_581_, 6);
v_newFacts_594_ = lean_ctor_get(v_toGoalState_581_, 7);
v_inconsistent_595_ = lean_ctor_get_uint8(v_toGoalState_581_, sizeof(void*)*17);
v_nextIdx_596_ = lean_ctor_get(v_toGoalState_581_, 8);
v_newRawFacts_597_ = lean_ctor_get(v_toGoalState_581_, 9);
v_facts_598_ = lean_ctor_get(v_toGoalState_581_, 10);
v_extThms_599_ = lean_ctor_get(v_toGoalState_581_, 11);
v_ematch_600_ = lean_ctor_get(v_toGoalState_581_, 12);
v_inj_601_ = lean_ctor_get(v_toGoalState_581_, 13);
v_split_602_ = lean_ctor_get(v_toGoalState_581_, 14);
v_sstates_603_ = lean_ctor_get(v_toGoalState_581_, 16);
v_isSharedCheck_626_ = !lean_is_exclusive(v_toGoalState_581_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_toGoalState_581_, 15);
lean_dec(v_unused_627_);
v___x_605_ = v_toGoalState_581_;
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_sstates_603_);
lean_inc(v_split_602_);
lean_inc(v_inj_601_);
lean_inc(v_ematch_600_);
lean_inc(v_extThms_599_);
lean_inc(v_facts_598_);
lean_inc(v_newRawFacts_597_);
lean_inc(v_nextIdx_596_);
lean_inc(v_newFacts_594_);
lean_inc(v_indicesFound_593_);
lean_inc(v_appMap_592_);
lean_inc(v_congrTable_591_);
lean_inc(v_parents_590_);
lean_inc(v_exprs_589_);
lean_inc(v_enodeMap_588_);
lean_inc(v_nextDeclIdx_587_);
lean_dec(v_toGoalState_581_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_used_607_; lean_object* v_next_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_625_; 
v_used_607_ = lean_ctor_get(v_clean_582_, 0);
v_next_608_ = lean_ctor_get(v_clean_582_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_clean_582_);
if (v_isSharedCheck_625_ == 0)
{
v___x_610_ = v_clean_582_;
v_isShared_611_ = v_isSharedCheck_625_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_next_608_);
lean_inc(v_used_607_);
lean_dec(v_clean_582_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_625_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_612_ = lean_box(0);
lean_inc(v_name_578_);
v___x_613_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_607_, v_name_578_, v___x_612_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_613_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_next_608_);
v___x_615_ = v_reuseFailAlloc_624_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 15, v___x_615_);
v___x_617_ = v___x_605_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_nextDeclIdx_587_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_enodeMap_588_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_exprs_589_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_parents_590_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_congrTable_591_);
lean_ctor_set(v_reuseFailAlloc_623_, 5, v_appMap_592_);
lean_ctor_set(v_reuseFailAlloc_623_, 6, v_indicesFound_593_);
lean_ctor_set(v_reuseFailAlloc_623_, 7, v_newFacts_594_);
lean_ctor_set(v_reuseFailAlloc_623_, 8, v_nextIdx_596_);
lean_ctor_set(v_reuseFailAlloc_623_, 9, v_newRawFacts_597_);
lean_ctor_set(v_reuseFailAlloc_623_, 10, v_facts_598_);
lean_ctor_set(v_reuseFailAlloc_623_, 11, v_extThms_599_);
lean_ctor_set(v_reuseFailAlloc_623_, 12, v_ematch_600_);
lean_ctor_set(v_reuseFailAlloc_623_, 13, v_inj_601_);
lean_ctor_set(v_reuseFailAlloc_623_, 14, v_split_602_);
lean_ctor_set(v_reuseFailAlloc_623_, 15, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_623_, 16, v_sstates_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*17, v_inconsistent_595_);
v___x_617_ = v_reuseFailAlloc_623_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_617_);
v___x_619_ = v___x_585_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_mvarId_583_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_st_ref_set(v___y_579_, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_name_578_);
return v___x_621_;
}
}
}
}
}
}
}
v___jp_630_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_636_);
lean_ctor_set(v___x_644_, 1, v___y_643_);
lean_inc(v___y_639_);
v___x_645_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_639_, v___x_644_, v___y_633_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v_toGoalState_648_; lean_object* v_clean_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v_mvarId_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_695_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_st_ref_take(v___y_633_);
v_toGoalState_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_toGoalState_648_);
v_clean_649_ = lean_ctor_get(v_toGoalState_648_, 15);
lean_inc_ref(v_clean_649_);
v_fst_650_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v_a_646_, 1);
lean_inc(v_snd_651_);
lean_dec(v_a_646_);
v_mvarId_652_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_647_, 0);
lean_dec(v_unused_696_);
v___x_654_ = v___x_647_;
v_isShared_655_ = v_isSharedCheck_695_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_mvarId_652_);
lean_dec(v___x_647_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_695_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_nextDeclIdx_656_; lean_object* v_enodeMap_657_; lean_object* v_exprs_658_; lean_object* v_parents_659_; lean_object* v_congrTable_660_; lean_object* v_appMap_661_; lean_object* v_indicesFound_662_; lean_object* v_newFacts_663_; uint8_t v_inconsistent_664_; lean_object* v_nextIdx_665_; lean_object* v_newRawFacts_666_; lean_object* v_facts_667_; lean_object* v_extThms_668_; lean_object* v_ematch_669_; lean_object* v_inj_670_; lean_object* v_split_671_; lean_object* v_sstates_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_693_; 
v_nextDeclIdx_656_ = lean_ctor_get(v_toGoalState_648_, 0);
v_enodeMap_657_ = lean_ctor_get(v_toGoalState_648_, 1);
v_exprs_658_ = lean_ctor_get(v_toGoalState_648_, 2);
v_parents_659_ = lean_ctor_get(v_toGoalState_648_, 3);
v_congrTable_660_ = lean_ctor_get(v_toGoalState_648_, 4);
v_appMap_661_ = lean_ctor_get(v_toGoalState_648_, 5);
v_indicesFound_662_ = lean_ctor_get(v_toGoalState_648_, 6);
v_newFacts_663_ = lean_ctor_get(v_toGoalState_648_, 7);
v_inconsistent_664_ = lean_ctor_get_uint8(v_toGoalState_648_, sizeof(void*)*17);
v_nextIdx_665_ = lean_ctor_get(v_toGoalState_648_, 8);
v_newRawFacts_666_ = lean_ctor_get(v_toGoalState_648_, 9);
v_facts_667_ = lean_ctor_get(v_toGoalState_648_, 10);
v_extThms_668_ = lean_ctor_get(v_toGoalState_648_, 11);
v_ematch_669_ = lean_ctor_get(v_toGoalState_648_, 12);
v_inj_670_ = lean_ctor_get(v_toGoalState_648_, 13);
v_split_671_ = lean_ctor_get(v_toGoalState_648_, 14);
v_sstates_672_ = lean_ctor_get(v_toGoalState_648_, 16);
v_isSharedCheck_693_ = !lean_is_exclusive(v_toGoalState_648_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_toGoalState_648_, 15);
lean_dec(v_unused_694_);
v___x_674_ = v_toGoalState_648_;
v_isShared_675_ = v_isSharedCheck_693_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_sstates_672_);
lean_inc(v_split_671_);
lean_inc(v_inj_670_);
lean_inc(v_ematch_669_);
lean_inc(v_extThms_668_);
lean_inc(v_facts_667_);
lean_inc(v_newRawFacts_666_);
lean_inc(v_nextIdx_665_);
lean_inc(v_newFacts_663_);
lean_inc(v_indicesFound_662_);
lean_inc(v_appMap_661_);
lean_inc(v_congrTable_660_);
lean_inc(v_parents_659_);
lean_inc(v_exprs_658_);
lean_inc(v_enodeMap_657_);
lean_inc(v_nextDeclIdx_656_);
lean_dec(v_toGoalState_648_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_693_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_used_676_; lean_object* v_next_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_692_; 
v_used_676_ = lean_ctor_get(v_clean_649_, 0);
v_next_677_ = lean_ctor_get(v_clean_649_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_clean_649_);
if (v_isSharedCheck_692_ == 0)
{
v___x_679_ = v_clean_649_;
v_isShared_680_ = v_isSharedCheck_692_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_next_677_);
lean_inc(v_used_676_);
lean_dec(v_clean_649_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_692_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_677_, v___y_639_, v_snd_651_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_used_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_691_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_685_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 15, v___x_683_);
v___x_685_ = v___x_674_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_nextDeclIdx_656_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_enodeMap_657_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_exprs_658_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_parents_659_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_congrTable_660_);
lean_ctor_set(v_reuseFailAlloc_690_, 5, v_appMap_661_);
lean_ctor_set(v_reuseFailAlloc_690_, 6, v_indicesFound_662_);
lean_ctor_set(v_reuseFailAlloc_690_, 7, v_newFacts_663_);
lean_ctor_set(v_reuseFailAlloc_690_, 8, v_nextIdx_665_);
lean_ctor_set(v_reuseFailAlloc_690_, 9, v_newRawFacts_666_);
lean_ctor_set(v_reuseFailAlloc_690_, 10, v_facts_667_);
lean_ctor_set(v_reuseFailAlloc_690_, 11, v_extThms_668_);
lean_ctor_set(v_reuseFailAlloc_690_, 12, v_ematch_669_);
lean_ctor_set(v_reuseFailAlloc_690_, 13, v_inj_670_);
lean_ctor_set(v_reuseFailAlloc_690_, 14, v_split_671_);
lean_ctor_set(v_reuseFailAlloc_690_, 15, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 16, v_sstates_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_690_, sizeof(void*)*17, v_inconsistent_664_);
v___x_685_ = v_reuseFailAlloc_690_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_685_);
v___x_687_ = v___x_654_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_mvarId_652_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
v___x_688_ = lean_st_ref_set(v___y_633_, v___x_687_);
v_name_578_ = v_fst_650_;
v___y_579_ = v___y_633_;
goto v___jp_577_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v___y_639_);
v_a_697_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_645_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_645_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
v___jp_705_:
{
lean_object* v___x_717_; lean_object* v_toGoalState_718_; lean_object* v_clean_719_; lean_object* v_used_720_; uint8_t v___x_721_; 
v___x_717_ = lean_st_ref_get(v___y_707_);
v_toGoalState_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_ref(v_toGoalState_718_);
lean_dec(v___x_717_);
v_clean_719_ = lean_ctor_get(v_toGoalState_718_, 15);
lean_inc_ref(v_clean_719_);
lean_dec_ref(v_toGoalState_718_);
v_used_720_ = lean_ctor_get(v_clean_719_, 0);
lean_inc_ref(v_used_720_);
lean_dec_ref(v_clean_719_);
v___x_721_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_720_, v_name_706_);
lean_dec_ref(v_used_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_type_565_);
v_name_578_ = v_name_706_;
v___y_579_ = v___y_707_;
goto v___jp_577_;
}
else
{
lean_object* v___x_722_; 
lean_inc(v_name_706_);
v___x_722_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_706_, v_type_565_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v_toGoalState_725_; lean_object* v_clean_726_; lean_object* v_next_727_; lean_object* v___x_728_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_722_);
v___x_724_ = lean_st_ref_get(v___y_707_);
v_toGoalState_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_toGoalState_725_);
lean_dec(v___x_724_);
v_clean_726_ = lean_ctor_get(v_toGoalState_725_, 15);
lean_inc_ref(v_clean_726_);
lean_dec_ref(v_toGoalState_725_);
v_next_727_ = lean_ctor_get(v_clean_726_, 1);
lean_inc_ref(v_next_727_);
lean_dec_ref(v_clean_726_);
v___x_728_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_727_, v_a_723_);
lean_dec_ref(v_next_727_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref(v___x_728_);
v___y_631_ = v___y_714_;
v___y_632_ = v___y_716_;
v___y_633_ = v___y_707_;
v___y_634_ = v___y_709_;
v___y_635_ = v___y_711_;
v___y_636_ = v_name_706_;
v___y_637_ = v___y_708_;
v___y_638_ = v___y_715_;
v___y_639_ = v_a_723_;
v___y_640_ = v___y_713_;
v___y_641_ = v___y_712_;
v___y_642_ = v___y_710_;
v___y_643_ = v_val_729_;
goto v___jp_630_;
}
else
{
lean_object* v___x_730_; 
lean_dec(v___x_728_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___y_631_ = v___y_714_;
v___y_632_ = v___y_716_;
v___y_633_ = v___y_707_;
v___y_634_ = v___y_709_;
v___y_635_ = v___y_711_;
v___y_636_ = v_name_706_;
v___y_637_ = v___y_708_;
v___y_638_ = v___y_715_;
v___y_639_ = v_a_723_;
v___y_640_ = v___y_713_;
v___y_641_ = v___y_712_;
v___y_642_ = v___y_710_;
v___y_643_ = v___x_730_;
goto v___jp_630_;
}
}
else
{
lean_dec(v_name_706_);
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_801_, lean_object* v_type_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_801_, v_type_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec(v_a_803_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_816_, v_x_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_824_, v_x_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec_ref(v_x_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_829_, lean_object* v_b_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_829_, v_b_830_, v___y_831_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_843_, v_b_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_861_, v_x_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec_ref(v_x_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, size_t v_x_867_, size_t v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_866_, v_x_867_, v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
size_t v_x_37838__boxed_878_; size_t v_x_37839__boxed_879_; lean_object* v_res_880_; 
v_x_37838__boxed_878_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_x_37839__boxed_879_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_res_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_872_, v_x_873_, v_x_37838__boxed_878_, v_x_37839__boxed_879_, v_x_876_, v_x_877_);
return v_res_880_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, size_t v_x_883_, lean_object* v_x_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_882_, v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
size_t v_x_37855__boxed_890_; uint8_t v_res_891_; lean_object* v_r_892_; 
v_x_37855__boxed_890_ = lean_unbox_usize(v_x_888_);
lean_dec(v_x_888_);
v_res_891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_886_, v_x_887_, v_x_37855__boxed_890_, v_x_889_);
lean_dec(v_x_889_);
lean_dec_ref(v_x_887_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_893_, lean_object* v_x_894_, size_t v_x_895_, lean_object* v_x_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_894_, v_x_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_37866__boxed_902_; lean_object* v_res_903_; 
v_x_37866__boxed_902_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_903_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_898_, v_x_899_, v_x_37866__boxed_902_, v_x_901_);
lean_dec(v_x_901_);
lean_dec_ref(v_x_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_904_, lean_object* v_n_905_, lean_object* v_k_906_, lean_object* v_v_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_905_, v_k_906_, v_v_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_909_, size_t v_depth_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_heq_913_, lean_object* v_i_914_, lean_object* v_entries_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_910_, v_keys_911_, v_vals_912_, v_i_914_, v_entries_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_917_, lean_object* v_depth_918_, lean_object* v_keys_919_, lean_object* v_vals_920_, lean_object* v_heq_921_, lean_object* v_i_922_, lean_object* v_entries_923_){
_start:
{
size_t v_depth_boxed_924_; lean_object* v_res_925_; 
v_depth_boxed_924_ = lean_unbox_usize(v_depth_918_);
lean_dec(v_depth_918_);
v_res_925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_917_, v_depth_boxed_924_, v_keys_919_, v_vals_920_, v_heq_921_, v_i_922_, v_entries_923_);
lean_dec_ref(v_vals_920_);
lean_dec_ref(v_keys_919_);
return v_res_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_926_, lean_object* v_keys_927_, lean_object* v_vals_928_, lean_object* v_heq_929_, lean_object* v_i_930_, lean_object* v_k_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_927_, v_i_930_, v_k_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_933_, lean_object* v_keys_934_, lean_object* v_vals_935_, lean_object* v_heq_936_, lean_object* v_i_937_, lean_object* v_k_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_933_, v_keys_934_, v_vals_935_, v_heq_936_, v_i_937_, v_k_938_);
lean_dec(v_k_938_);
lean_dec_ref(v_vals_935_);
lean_dec_ref(v_keys_934_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_heq_944_, lean_object* v_i_945_, lean_object* v_k_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_942_, v_vals_943_, v_i_945_, v_k_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_948_, lean_object* v_keys_949_, lean_object* v_vals_950_, lean_object* v_heq_951_, lean_object* v_i_952_, lean_object* v_k_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_948_, v_keys_949_, v_vals_950_, v_heq_951_, v_i_952_, v_k_953_);
lean_dec(v_k_953_);
lean_dec_ref(v_vals_950_);
lean_dec_ref(v_keys_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_956_, v_x_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v_env_968_; lean_object* v___x_969_; lean_object* v_mctx_970_; lean_object* v_lctx_971_; lean_object* v_options_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_967_ = lean_st_ref_get(v___y_965_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_969_ = lean_st_ref_get(v___y_963_);
v_mctx_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_mctx_970_);
lean_dec(v___x_969_);
v_lctx_971_ = lean_ctor_get(v___y_962_, 2);
v_options_972_ = lean_ctor_get(v___y_964_, 2);
lean_inc_ref(v_options_972_);
lean_inc_ref(v_lctx_971_);
v___x_973_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_973_, 0, v_env_968_);
lean_ctor_set(v___x_973_, 1, v_mctx_970_);
lean_ctor_set(v___x_973_, 2, v_lctx_971_);
lean_ctor_set(v___x_973_, 3, v_options_972_);
v___x_974_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_msgData_961_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_ref_989_; lean_object* v___x_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_ref_989_ = lean_ctor_get(v___y_986_, 5);
v___x_990_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_ref_989_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_ref_989_);
lean_ctor_set(v___x_995_, 1, v_a_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___x_1076_; lean_object* v_mvarId_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_st_ref_get(v_a_1010_);
v_mvarId_1077_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_mvarId_1077_);
lean_dec(v___x_1076_);
v___x_1078_ = l_Lean_MVarId_getType(v_mvarId_1077_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v___x_1078_);
switch(lean_obj_tag(v_a_1079_))
{
case 7:
{
lean_object* v_binderName_1080_; lean_object* v_binderType_1081_; 
v_binderName_1080_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_binderName_1080_);
v_binderType_1081_ = lean_ctor_get(v_a_1079_, 1);
lean_inc_ref(v_binderType_1081_);
lean_dec_ref(v_a_1079_);
v_fst_1022_ = v_binderName_1080_;
v_snd_1023_ = v_binderType_1081_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
v___y_1028_ = v_a_1014_;
v___y_1029_ = v_a_1015_;
v___y_1030_ = v_a_1016_;
v___y_1031_ = v_a_1017_;
v___y_1032_ = v_a_1018_;
v___y_1033_ = v_a_1019_;
goto v___jp_1021_;
}
case 8:
{
lean_object* v_declName_1082_; lean_object* v_type_1083_; 
v_declName_1082_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_declName_1082_);
v_type_1083_ = lean_ctor_get(v_a_1079_, 1);
lean_inc_ref(v_type_1083_);
lean_dec_ref(v_a_1079_);
v_fst_1022_ = v_declName_1082_;
v_snd_1023_ = v_type_1083_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
v___y_1028_ = v_a_1014_;
v___y_1029_ = v_a_1015_;
v___y_1030_ = v_a_1016_;
v___y_1031_ = v_a_1017_;
v___y_1032_ = v_a_1018_;
v___y_1033_ = v_a_1019_;
goto v___jp_1021_;
}
default: 
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_a_1079_);
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1085_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1084_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
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
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
v_a_1094_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1078_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1078_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
v___jp_1021_:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1022_, v_snd_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v_mvarId_1037_; lean_object* v___x_1038_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = lean_st_ref_get(v___y_1024_);
v_mvarId_1037_ = lean_ctor_get(v___x_1036_, 1);
lean_inc(v_mvarId_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = l_Lean_MVarId_intro(v_mvarId_1037_, v_a_1035_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1059_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1059_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1059_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_fst_1043_; lean_object* v_snd_1044_; lean_object* v___x_1045_; lean_object* v_toGoalState_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
v_fst_1043_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_fst_1043_);
v_snd_1044_ = lean_ctor_get(v_a_1039_, 1);
lean_inc(v_snd_1044_);
lean_dec(v_a_1039_);
v___x_1045_ = lean_st_ref_take(v___y_1024_);
v_toGoalState_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1045_, 1);
lean_dec(v_unused_1058_);
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_toGoalState_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_snd_1044_);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_toGoalState_1046_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_snd_1044_);
v___x_1051_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_st_ref_set(v___y_1024_, v___x_1051_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_fst_1043_);
v___x_1054_ = v___x_1041_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_fst_1043_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1038_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1038_);
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
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1034_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1034_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec(v_a_1102_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1114_, lean_object* v_msg_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1115_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1128_, v_msg_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
lean_inc(v___y_1143_);
v___x_1154_ = lean_apply_11(v_x_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, lean_box(0));
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v___y_1156_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___f_1181_; lean_object* v___x_1182_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc(v___y_1170_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1181_, 0, v_x_1169_);
lean_closure_set(v___f_1181_, 1, v___y_1170_);
lean_closure_set(v___f_1181_, 2, v___y_1171_);
lean_closure_set(v___f_1181_, 3, v___y_1172_);
lean_closure_set(v___f_1181_, 4, v___y_1173_);
lean_closure_set(v___f_1181_, 5, v___y_1174_);
lean_closure_set(v___f_1181_, 6, v___y_1175_);
v___x_1182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1168_, v___f_1181_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1182_) == 0)
{
return v___x_1182_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec(v___y_1193_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1205_, lean_object* v_mvarId_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1206_, v_x_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_mvarId_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1220_, v_mvarId_1221_, v_x_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
v___x_1246_ = lean_apply_10(v_x_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___f_1271_; lean_object* v___x_1272_; 
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1261_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1271_, 0, v_x_1260_);
lean_closure_set(v___f_1271_, 1, v___y_1261_);
lean_closure_set(v___f_1271_, 2, v___y_1262_);
lean_closure_set(v___f_1271_, 3, v___y_1263_);
lean_closure_set(v___f_1271_, 4, v___y_1264_);
lean_closure_set(v___f_1271_, 5, v___y_1265_);
v___x_1272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1259_, v___f_1271_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
return v___x_1272_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1281_, v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1294_, lean_object* v_mvarId_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_mvarId_1309_, lean_object* v_x_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1308_, v_mvarId_1309_, v_x_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1322_, lean_object* v_generation_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
lean_inc(v_a_1322_);
v___x_1335_ = l_Lean_FVarId_getDecl___redArg(v_a_1322_, v___y_1330_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
v___x_1337_ = l_Lean_LocalDecl_type(v_a_1336_);
lean_dec(v_a_1336_);
lean_inc_ref(v___x_1337_);
v___x_1338_ = l_Lean_Meta_isProp(v___x_1337_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; uint8_t v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = lean_unbox(v_a_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v___x_1337_);
lean_inc(v_a_1322_);
v___x_1341_ = l_Lean_FVarId_getDecl___redArg(v_a_1322_, v___y_1330_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_unbox(v_a_1339_);
lean_dec(v_a_1339_);
v___x_1344_ = l_Lean_LocalDecl_value(v_a_1342_, v___x_1343_);
lean_dec(v_a_1342_);
v___x_1345_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1344_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
lean_inc(v_a_1322_);
v___x_1347_ = l_Lean_mkFVar(v_a_1322_);
v___x_1348_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1347_, v___y_1329_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1348_);
lean_inc(v_a_1346_);
v___x_1350_ = l_Lean_Meta_Simp_Result_getProof(v_a_1346_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_expr_1352_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v_expr_1352_ = lean_ctor_get(v_a_1346_, 0);
lean_inc_ref(v_expr_1352_);
lean_dec(v_a_1346_);
v___x_1353_ = l_Lean_Meta_Grind_addNewEq(v_a_1349_, v_expr_1352_, v_a_1351_, v_generation_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1353_, 0);
lean_dec(v_unused_1363_);
v___x_1355_ = v___x_1353_;
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v___x_1353_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = lean_st_ref_get(v___y_1324_);
v___x_1358_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1322_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1322_);
v_a_1364_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1353_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1353_);
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
lean_dec(v_a_1349_);
lean_dec(v_a_1346_);
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1372_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1350_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1350_);
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
lean_dec(v_a_1346_);
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1380_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1348_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1348_);
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
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1388_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1345_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1345_);
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
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_a_1339_);
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1396_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1341_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1341_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_a_1339_);
lean_dec(v_generation_1323_);
v___x_1404_ = lean_st_ref_get(v___y_1324_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1337_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1405_, v___x_1337_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_mvarId_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v_mvarId_1408_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_mvarId_1408_);
lean_dec(v___x_1404_);
v___x_1409_ = l_Lean_mkFVar(v_a_1322_);
v___x_1410_ = l_Lean_MVarId_assert(v_mvarId_1408_, v_a_1407_, v___x_1337_, v___x_1409_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1429_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1429_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1429_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v_toGoalState_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v___x_1415_ = lean_st_ref_get(v___y_1324_);
v_toGoalState_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1415_, 1);
lean_dec(v_unused_1428_);
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_toGoalState_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_a_1411_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_toGoalState_1416_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1411_);
v___x_1421_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1422_);
v___x_1424_ = v___x_1413_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1410_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1410_);
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
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v___x_1404_);
lean_dec_ref(v___x_1337_);
lean_dec(v_a_1322_);
v_a_1438_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1406_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1406_);
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
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v___x_1337_);
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1446_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1338_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1338_);
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
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_generation_1323_);
lean_dec(v_a_1322_);
v_a_1454_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1335_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1335_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1462_, lean_object* v_generation_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1462_, v_generation_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v_ks_1480_; lean_object* v_vs_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1505_; 
v_ks_1480_ = lean_ctor_get(v_x_1476_, 0);
v_vs_1481_ = lean_ctor_get(v_x_1476_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_x_1476_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1483_ = v_x_1476_;
v_isShared_1484_ = v_isSharedCheck_1505_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_vs_1481_);
lean_inc(v_ks_1480_);
lean_dec(v_x_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1505_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = lean_array_get_size(v_ks_1480_);
v___x_1486_ = lean_nat_dec_lt(v_x_1477_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec(v_x_1477_);
v___x_1487_ = lean_array_push(v_ks_1480_, v_x_1478_);
v___x_1488_ = lean_array_push(v_vs_1481_, v_x_1479_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1488_);
lean_ctor_set(v___x_1483_, 0, v___x_1487_);
v___x_1490_ = v___x_1483_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_object* v_k_x27_1492_; uint8_t v___x_1493_; 
v_k_x27_1492_ = lean_array_fget_borrowed(v_ks_1480_, v_x_1477_);
v___x_1493_ = l_Lean_instBEqMVarId_beq(v_x_1478_, v_k_x27_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1495_; 
if (v_isShared_1484_ == 0)
{
v___x_1495_ = v___x_1483_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_ks_1480_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_vs_1481_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v_x_1477_, v___x_1496_);
lean_dec(v_x_1477_);
v_x_1476_ = v___x_1495_;
v_x_1477_ = v___x_1497_;
goto _start;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = lean_array_fset(v_ks_1480_, v_x_1477_, v_x_1478_);
v___x_1501_ = lean_array_fset(v_vs_1481_, v_x_1477_, v_x_1479_);
lean_dec(v_x_1477_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1501_);
lean_ctor_set(v___x_1483_, 0, v___x_1500_);
v___x_1503_ = v___x_1483_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1506_, lean_object* v_k_1507_, lean_object* v_v_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1506_, v___x_1509_, v_k_1507_, v_v_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1511_, size_t v_x_1512_, size_t v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_es_1516_; size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; lean_object* v_j_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_es_1516_ = lean_ctor_get(v_x_1511_, 0);
v___x_1517_ = ((size_t)5ULL);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_1520_ = lean_usize_land(v_x_1512_, v___x_1519_);
v_j_1521_ = lean_usize_to_nat(v___x_1520_);
v___x_1522_ = lean_array_get_size(v_es_1516_);
v___x_1523_ = lean_nat_dec_lt(v_j_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec(v_j_1521_);
lean_dec(v_x_1515_);
lean_dec(v_x_1514_);
return v_x_1511_;
}
else
{
lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1560_; 
lean_inc_ref(v_es_1516_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_x_1511_, 0);
lean_dec(v_unused_1561_);
v___x_1525_ = v_x_1511_;
v_isShared_1526_ = v_isSharedCheck_1560_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v_x_1511_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1560_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_v_1527_; lean_object* v___x_1528_; lean_object* v_xs_x27_1529_; lean_object* v___y_1531_; 
v_v_1527_ = lean_array_fget(v_es_1516_, v_j_1521_);
v___x_1528_ = lean_box(0);
v_xs_x27_1529_ = lean_array_fset(v_es_1516_, v_j_1521_, v___x_1528_);
switch(lean_obj_tag(v_v_1527_))
{
case 0:
{
lean_object* v_key_1536_; lean_object* v_val_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1547_; 
v_key_1536_ = lean_ctor_get(v_v_1527_, 0);
v_val_1537_ = lean_ctor_get(v_v_1527_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_v_1527_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1539_ = v_v_1527_;
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_val_1537_);
lean_inc(v_key_1536_);
lean_dec(v_v_1527_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_Lean_instBEqMVarId_beq(v_x_1514_, v_key_1536_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_del_object(v___x_1539_);
v___x_1542_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1536_, v_val_1537_, v_x_1514_, v_x_1515_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
v___y_1531_ = v___x_1543_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_val_1537_);
lean_dec(v_key_1536_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v_x_1515_);
lean_ctor_set(v___x_1539_, 0, v_x_1514_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_x_1514_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_x_1515_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v___y_1531_ = v___x_1545_;
goto v___jp_1530_;
}
}
}
}
case 1:
{
lean_object* v_node_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_node_1548_ = lean_ctor_get(v_v_1527_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_v_1527_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v_v_1527_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_node_1548_);
lean_dec(v_v_1527_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1552_ = lean_usize_shift_right(v_x_1512_, v___x_1517_);
v___x_1553_ = lean_usize_add(v_x_1513_, v___x_1518_);
v___x_1554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1548_, v___x_1552_, v___x_1553_, v_x_1514_, v_x_1515_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1554_);
v___x_1556_ = v___x_1550_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
v___y_1531_ = v___x_1556_;
goto v___jp_1530_;
}
}
}
default: 
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_x_1514_);
lean_ctor_set(v___x_1559_, 1, v_x_1515_);
v___y_1531_ = v___x_1559_;
goto v___jp_1530_;
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_array_fset(v_xs_x27_1529_, v_j_1521_, v___y_1531_);
lean_dec(v_j_1521_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1532_);
v___x_1534_ = v___x_1525_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
else
{
lean_object* v_ks_1562_; lean_object* v_vs_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1583_; 
v_ks_1562_ = lean_ctor_get(v_x_1511_, 0);
v_vs_1563_ = lean_ctor_get(v_x_1511_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1565_ = v_x_1511_;
v_isShared_1566_ = v_isSharedCheck_1583_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_vs_1563_);
lean_inc(v_ks_1562_);
lean_dec(v_x_1511_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1583_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_ks_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_vs_1563_);
v___x_1568_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v_newNode_1569_; uint8_t v___y_1571_; size_t v___x_1577_; uint8_t v___x_1578_; 
v_newNode_1569_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1568_, v_x_1514_, v_x_1515_);
v___x_1577_ = ((size_t)7ULL);
v___x_1578_ = lean_usize_dec_le(v___x_1577_, v_x_1513_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1569_);
v___x_1580_ = lean_unsigned_to_nat(4u);
v___x_1581_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
lean_dec(v___x_1579_);
v___y_1571_ = v___x_1581_;
goto v___jp_1570_;
}
else
{
v___y_1571_ = v___x_1578_;
goto v___jp_1570_;
}
v___jp_1570_:
{
if (v___y_1571_ == 0)
{
lean_object* v_ks_1572_; lean_object* v_vs_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_ks_1572_ = lean_ctor_get(v_newNode_1569_, 0);
lean_inc_ref(v_ks_1572_);
v_vs_1573_ = lean_ctor_get(v_newNode_1569_, 1);
lean_inc_ref(v_vs_1573_);
lean_dec_ref(v_newNode_1569_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2);
v___x_1576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1513_, v_ks_1572_, v_vs_1573_, v___x_1574_, v___x_1575_);
lean_dec_ref(v_vs_1573_);
lean_dec_ref(v_ks_1572_);
return v___x_1576_;
}
else
{
return v_newNode_1569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1584_, lean_object* v_keys_1585_, lean_object* v_vals_1586_, lean_object* v_i_1587_, lean_object* v_entries_1588_){
_start:
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_array_get_size(v_keys_1585_);
v___x_1590_ = lean_nat_dec_lt(v_i_1587_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec(v_i_1587_);
return v_entries_1588_;
}
else
{
lean_object* v_k_1591_; lean_object* v_v_1592_; uint64_t v___x_1593_; size_t v_h_1594_; size_t v___x_1595_; lean_object* v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; size_t v___x_1599_; size_t v_h_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_k_1591_ = lean_array_fget_borrowed(v_keys_1585_, v_i_1587_);
v_v_1592_ = lean_array_fget_borrowed(v_vals_1586_, v_i_1587_);
v___x_1593_ = l_Lean_instHashableMVarId_hash(v_k_1591_);
v_h_1594_ = lean_uint64_to_usize(v___x_1593_);
v___x_1595_ = ((size_t)5ULL);
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_sub(v_depth_1584_, v___x_1597_);
v___x_1599_ = lean_usize_mul(v___x_1595_, v___x_1598_);
v_h_1600_ = lean_usize_shift_right(v_h_1594_, v___x_1599_);
v___x_1601_ = lean_nat_add(v_i_1587_, v___x_1596_);
lean_dec(v_i_1587_);
lean_inc(v_v_1592_);
lean_inc(v_k_1591_);
v___x_1602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1588_, v_h_1600_, v_depth_1584_, v_k_1591_, v_v_1592_);
v_i_1587_ = v___x_1601_;
v_entries_1588_ = v___x_1602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1604_, lean_object* v_keys_1605_, lean_object* v_vals_1606_, lean_object* v_i_1607_, lean_object* v_entries_1608_){
_start:
{
size_t v_depth_boxed_1609_; lean_object* v_res_1610_; 
v_depth_boxed_1609_ = lean_unbox_usize(v_depth_1604_);
lean_dec(v_depth_1604_);
v_res_1610_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1609_, v_keys_1605_, v_vals_1606_, v_i_1607_, v_entries_1608_);
lean_dec_ref(v_vals_1606_);
lean_dec_ref(v_keys_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
size_t v_x_195298__boxed_1616_; size_t v_x_195299__boxed_1617_; lean_object* v_res_1618_; 
v_x_195298__boxed_1616_ = lean_unbox_usize(v_x_1612_);
lean_dec(v_x_1612_);
v_x_195299__boxed_1617_ = lean_unbox_usize(v_x_1613_);
lean_dec(v_x_1613_);
v_res_1618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1611_, v_x_195298__boxed_1616_, v_x_195299__boxed_1617_, v_x_1614_, v_x_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
uint64_t v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = l_Lean_instHashableMVarId_hash(v_x_1620_);
v___x_1623_ = lean_uint64_to_usize(v___x_1622_);
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1619_, v___x_1623_, v___x_1624_, v_x_1620_, v_x_1621_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1626_, lean_object* v_val_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v_mctx_1631_; lean_object* v_cache_1632_; lean_object* v_zetaDeltaFVarIds_1633_; lean_object* v_postponed_1634_; lean_object* v_diag_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1663_; 
v___x_1630_ = lean_st_ref_take(v___y_1628_);
v_mctx_1631_ = lean_ctor_get(v___x_1630_, 0);
v_cache_1632_ = lean_ctor_get(v___x_1630_, 1);
v_zetaDeltaFVarIds_1633_ = lean_ctor_get(v___x_1630_, 2);
v_postponed_1634_ = lean_ctor_get(v___x_1630_, 3);
v_diag_1635_ = lean_ctor_get(v___x_1630_, 4);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1637_ = v___x_1630_;
v_isShared_1638_ = v_isSharedCheck_1663_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_diag_1635_);
lean_inc(v_postponed_1634_);
lean_inc(v_zetaDeltaFVarIds_1633_);
lean_inc(v_cache_1632_);
lean_inc(v_mctx_1631_);
lean_dec(v___x_1630_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1663_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_depth_1639_; lean_object* v_levelAssignDepth_1640_; lean_object* v_lmvarCounter_1641_; lean_object* v_mvarCounter_1642_; lean_object* v_lDecls_1643_; lean_object* v_decls_1644_; lean_object* v_userNames_1645_; lean_object* v_lAssignment_1646_; lean_object* v_eAssignment_1647_; lean_object* v_dAssignment_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1662_; 
v_depth_1639_ = lean_ctor_get(v_mctx_1631_, 0);
v_levelAssignDepth_1640_ = lean_ctor_get(v_mctx_1631_, 1);
v_lmvarCounter_1641_ = lean_ctor_get(v_mctx_1631_, 2);
v_mvarCounter_1642_ = lean_ctor_get(v_mctx_1631_, 3);
v_lDecls_1643_ = lean_ctor_get(v_mctx_1631_, 4);
v_decls_1644_ = lean_ctor_get(v_mctx_1631_, 5);
v_userNames_1645_ = lean_ctor_get(v_mctx_1631_, 6);
v_lAssignment_1646_ = lean_ctor_get(v_mctx_1631_, 7);
v_eAssignment_1647_ = lean_ctor_get(v_mctx_1631_, 8);
v_dAssignment_1648_ = lean_ctor_get(v_mctx_1631_, 9);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_mctx_1631_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1650_ = v_mctx_1631_;
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_dAssignment_1648_);
lean_inc(v_eAssignment_1647_);
lean_inc(v_lAssignment_1646_);
lean_inc(v_userNames_1645_);
lean_inc(v_decls_1644_);
lean_inc(v_lDecls_1643_);
lean_inc(v_mvarCounter_1642_);
lean_inc(v_lmvarCounter_1641_);
lean_inc(v_levelAssignDepth_1640_);
lean_inc(v_depth_1639_);
lean_dec(v_mctx_1631_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1662_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1647_, v_mvarId_1626_, v_val_1627_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 8, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_depth_1639_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_levelAssignDepth_1640_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_lmvarCounter_1641_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_mvarCounter_1642_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_lDecls_1643_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v_decls_1644_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_userNames_1645_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_lAssignment_1646_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1661_, 9, v_dAssignment_1648_);
v___x_1654_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1654_);
v___x_1656_ = v___x_1637_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_cache_1632_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_zetaDeltaFVarIds_1633_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_postponed_1634_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_diag_1635_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_st_ref_set(v___y_1628_, v___x_1656_);
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1664_, lean_object* v_val_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1664_, v_val_1665_, v___y_1666_);
lean_dec(v___y_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v_ngen_1672_; lean_object* v_namePrefix_1673_; lean_object* v_idx_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1703_; 
v___x_1671_ = lean_st_ref_get(v___y_1669_);
v_ngen_1672_ = lean_ctor_get(v___x_1671_, 2);
lean_inc_ref(v_ngen_1672_);
lean_dec(v___x_1671_);
v_namePrefix_1673_ = lean_ctor_get(v_ngen_1672_, 0);
v_idx_1674_ = lean_ctor_get(v_ngen_1672_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_ngen_1672_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1676_ = v_ngen_1672_;
v_isShared_1677_ = v_isSharedCheck_1703_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_idx_1674_);
lean_inc(v_namePrefix_1673_);
lean_dec(v_ngen_1672_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1703_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v_env_1679_; lean_object* v_nextMacroScope_1680_; lean_object* v_auxDeclNGen_1681_; lean_object* v_traceState_1682_; lean_object* v_cache_1683_; lean_object* v_messages_1684_; lean_object* v_infoState_1685_; lean_object* v_snapshotTasks_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1701_; 
v___x_1678_ = lean_st_ref_take(v___y_1669_);
v_env_1679_ = lean_ctor_get(v___x_1678_, 0);
v_nextMacroScope_1680_ = lean_ctor_get(v___x_1678_, 1);
v_auxDeclNGen_1681_ = lean_ctor_get(v___x_1678_, 3);
v_traceState_1682_ = lean_ctor_get(v___x_1678_, 4);
v_cache_1683_ = lean_ctor_get(v___x_1678_, 5);
v_messages_1684_ = lean_ctor_get(v___x_1678_, 6);
v_infoState_1685_ = lean_ctor_get(v___x_1678_, 7);
v_snapshotTasks_1686_ = lean_ctor_get(v___x_1678_, 8);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1678_, 2);
lean_dec(v_unused_1702_);
v___x_1688_ = v___x_1678_;
v_isShared_1689_ = v_isSharedCheck_1701_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_snapshotTasks_1686_);
lean_inc(v_infoState_1685_);
lean_inc(v_messages_1684_);
lean_inc(v_cache_1683_);
lean_inc(v_traceState_1682_);
lean_inc(v_auxDeclNGen_1681_);
lean_inc(v_nextMacroScope_1680_);
lean_inc(v_env_1679_);
lean_dec(v___x_1678_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1701_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_r_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_inc(v_idx_1674_);
lean_inc(v_namePrefix_1673_);
v_r_1690_ = l_Lean_Name_num___override(v_namePrefix_1673_, v_idx_1674_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_add(v_idx_1674_, v___x_1691_);
lean_dec(v_idx_1674_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1692_);
v___x_1694_ = v___x_1676_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_namePrefix_1673_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 2, v___x_1694_);
v___x_1696_ = v___x_1688_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_env_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_nextMacroScope_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_auxDeclNGen_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_traceState_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_cache_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_messages_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_infoState_1685_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v_snapshotTasks_1686_);
v___x_1696_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_st_ref_set(v___y_1669_, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_r_1690_);
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1704_);
lean_dec(v___y_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v___x_1718_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1716_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1744_, lean_object* v_a_1745_, uint8_t v___y_1746_, uint8_t v___x_1747_, uint8_t v___x_1748_, lean_object* v_a_1749_, lean_object* v___x_1750_, lean_object* v_expr_1751_, lean_object* v___x_1752_, lean_object* v_val_1753_, lean_object* v_mvarId_1754_, lean_object* v___x_1755_, lean_object* v_a_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Meta_mkLambdaFVars(v___x_1744_, v_a_1745_, v___y_1746_, v___x_1747_, v___y_1746_, v___x_1747_, v___x_1748_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1749_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_mkConst(v___x_1770_, v___x_1772_);
v___x_1774_ = lean_unsigned_to_nat(5u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_1776_ = lean_array_push(v___x_1775_, v___x_1750_);
v___x_1777_ = lean_array_push(v___x_1776_, v_expr_1751_);
v___x_1778_ = lean_array_push(v___x_1777_, v___x_1752_);
v___x_1779_ = lean_array_push(v___x_1778_, v_val_1753_);
v___x_1780_ = lean_array_push(v___x_1779_, v_a_1769_);
v___x_1781_ = l_Lean_mkAppN(v___x_1773_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1754_, v___x_1781_, v___y_1764_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1800_; 
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1782_, 0);
lean_dec(v_unused_1801_);
v___x_1784_ = v___x_1782_;
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v___x_1782_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v_toGoalState_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1798_; 
v___x_1786_ = lean_st_ref_get(v___y_1757_);
v_toGoalState_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v___x_1786_, 1);
lean_dec(v_unused_1799_);
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_toGoalState_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1755_);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_toGoalState_1787_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1755_);
v___x_1792_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1756_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1793_);
v___x_1795_ = v___x_1784_;
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
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1756_);
lean_dec(v___x_1755_);
v_a_1802_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1782_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1782_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1756_);
lean_dec(v___x_1755_);
lean_dec(v_mvarId_1754_);
lean_dec_ref(v_val_1753_);
lean_dec_ref(v___x_1752_);
lean_dec_ref(v_expr_1751_);
lean_dec_ref(v___x_1750_);
lean_dec(v_a_1749_);
v_a_1810_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1768_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1768_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1818_ = _args[0];
lean_object* v_a_1819_ = _args[1];
lean_object* v___y_1820_ = _args[2];
lean_object* v___x_1821_ = _args[3];
lean_object* v___x_1822_ = _args[4];
lean_object* v_a_1823_ = _args[5];
lean_object* v___x_1824_ = _args[6];
lean_object* v_expr_1825_ = _args[7];
lean_object* v___x_1826_ = _args[8];
lean_object* v_val_1827_ = _args[9];
lean_object* v_mvarId_1828_ = _args[10];
lean_object* v___x_1829_ = _args[11];
lean_object* v_a_1830_ = _args[12];
lean_object* v___y_1831_ = _args[13];
lean_object* v___y_1832_ = _args[14];
lean_object* v___y_1833_ = _args[15];
lean_object* v___y_1834_ = _args[16];
lean_object* v___y_1835_ = _args[17];
lean_object* v___y_1836_ = _args[18];
lean_object* v___y_1837_ = _args[19];
lean_object* v___y_1838_ = _args[20];
lean_object* v___y_1839_ = _args[21];
lean_object* v___y_1840_ = _args[22];
lean_object* v___y_1841_ = _args[23];
_start:
{
uint8_t v___y_195625__boxed_1842_; uint8_t v___x_195626__boxed_1843_; uint8_t v___x_195627__boxed_1844_; lean_object* v_res_1845_; 
v___y_195625__boxed_1842_ = lean_unbox(v___y_1820_);
v___x_195626__boxed_1843_ = lean_unbox(v___x_1821_);
v___x_195627__boxed_1844_ = lean_unbox(v___x_1822_);
v_res_1845_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1818_, v_a_1819_, v___y_195625__boxed_1842_, v___x_195626__boxed_1843_, v___x_195627__boxed_1844_, v_a_1823_, v___x_1824_, v_expr_1825_, v___x_1826_, v_val_1827_, v_mvarId_1828_, v___x_1829_, v_a_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___x_1818_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1851_, lean_object* v_a_1852_, uint8_t v___x_1853_, uint8_t v___x_1854_, uint8_t v___x_1855_, lean_object* v_a_1856_, lean_object* v___x_1857_, lean_object* v___x_1858_, lean_object* v_expr_1859_, lean_object* v___x_1860_, lean_object* v_val_1861_, lean_object* v_mvarId_1862_, lean_object* v___x_1863_, lean_object* v_a_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_mkLambdaFVars(v___x_1851_, v_a_1852_, v___x_1853_, v___x_1854_, v___x_1853_, v___x_1854_, v___x_1855_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1856_);
lean_ctor_set(v___x_1879_, 1, v___x_1857_);
v___x_1880_ = l_Lean_mkConst(v___x_1878_, v___x_1879_);
v___x_1881_ = lean_unsigned_to_nat(5u);
v___x_1882_ = lean_mk_empty_array_with_capacity(v___x_1881_);
v___x_1883_ = lean_array_push(v___x_1882_, v___x_1858_);
v___x_1884_ = lean_array_push(v___x_1883_, v_expr_1859_);
v___x_1885_ = lean_array_push(v___x_1884_, v___x_1860_);
v___x_1886_ = lean_array_push(v___x_1885_, v_val_1861_);
v___x_1887_ = lean_array_push(v___x_1886_, v_a_1877_);
v___x_1888_ = l_Lean_mkAppN(v___x_1880_, v___x_1887_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1862_, v___x_1888_, v___y_1872_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1907_; 
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1908_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1907_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1907_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_toGoalState_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1905_; 
v___x_1893_ = lean_st_ref_get(v___y_1865_);
v_toGoalState_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___x_1893_, 1);
lean_dec(v_unused_1906_);
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_toGoalState_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1863_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_toGoalState_1894_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1863_);
v___x_1899_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1864_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1900_);
v___x_1902_ = v___x_1891_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1864_);
lean_dec(v___x_1863_);
v_a_1909_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1889_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1889_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1864_);
lean_dec(v___x_1863_);
lean_dec(v_mvarId_1862_);
lean_dec_ref(v_val_1861_);
lean_dec_ref(v___x_1860_);
lean_dec_ref(v_expr_1859_);
lean_dec_ref(v___x_1858_);
lean_dec(v___x_1857_);
lean_dec(v_a_1856_);
v_a_1917_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1876_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1876_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1925_ = _args[0];
lean_object* v_a_1926_ = _args[1];
lean_object* v___x_1927_ = _args[2];
lean_object* v___x_1928_ = _args[3];
lean_object* v___x_1929_ = _args[4];
lean_object* v_a_1930_ = _args[5];
lean_object* v___x_1931_ = _args[6];
lean_object* v___x_1932_ = _args[7];
lean_object* v_expr_1933_ = _args[8];
lean_object* v___x_1934_ = _args[9];
lean_object* v_val_1935_ = _args[10];
lean_object* v_mvarId_1936_ = _args[11];
lean_object* v___x_1937_ = _args[12];
lean_object* v_a_1938_ = _args[13];
lean_object* v___y_1939_ = _args[14];
lean_object* v___y_1940_ = _args[15];
lean_object* v___y_1941_ = _args[16];
lean_object* v___y_1942_ = _args[17];
lean_object* v___y_1943_ = _args[18];
lean_object* v___y_1944_ = _args[19];
lean_object* v___y_1945_ = _args[20];
lean_object* v___y_1946_ = _args[21];
lean_object* v___y_1947_ = _args[22];
lean_object* v___y_1948_ = _args[23];
lean_object* v___y_1949_ = _args[24];
_start:
{
uint8_t v___x_195807__boxed_1950_; uint8_t v___x_195808__boxed_1951_; uint8_t v___x_195809__boxed_1952_; lean_object* v_res_1953_; 
v___x_195807__boxed_1950_ = lean_unbox(v___x_1927_);
v___x_195808__boxed_1951_ = lean_unbox(v___x_1928_);
v___x_195809__boxed_1952_ = lean_unbox(v___x_1929_);
v_res_1953_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1925_, v_a_1926_, v___x_195807__boxed_1950_, v___x_195808__boxed_1951_, v___x_195809__boxed_1952_, v_a_1930_, v___x_1931_, v___x_1932_, v_expr_1933_, v___x_1934_, v_val_1935_, v_mvarId_1936_, v___x_1937_, v_a_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___x_1925_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1954_, lean_object* v_a_1955_, uint8_t v___y_1956_, uint8_t v___x_1957_, uint8_t v___x_1958_, lean_object* v_mvarId_1959_, lean_object* v___x_1960_, lean_object* v_a_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_mkLambdaFVars(v___x_1954_, v_a_1955_, v___y_1956_, v___x_1957_, v___y_1956_, v___x_1957_, v___x_1958_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v___x_1975_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1959_, v_a_1974_, v___y_1969_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1993_; 
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_1994_);
v___x_1977_ = v___x_1975_;
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v___x_1975_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v_toGoalState_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v___x_1979_ = lean_st_ref_get(v___y_1962_);
v_toGoalState_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v___x_1979_, 1);
lean_dec(v_unused_1992_);
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_toGoalState_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___x_1960_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_toGoalState_1980_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1960_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1961_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1986_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v_a_1961_);
lean_dec(v___x_1960_);
v_a_1995_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1975_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1975_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_a_1961_);
lean_dec(v___x_1960_);
lean_dec(v_mvarId_1959_);
v_a_2003_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1973_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1973_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2011_ = _args[0];
lean_object* v_a_2012_ = _args[1];
lean_object* v___y_2013_ = _args[2];
lean_object* v___x_2014_ = _args[3];
lean_object* v___x_2015_ = _args[4];
lean_object* v_mvarId_2016_ = _args[5];
lean_object* v___x_2017_ = _args[6];
lean_object* v_a_2018_ = _args[7];
lean_object* v___y_2019_ = _args[8];
lean_object* v___y_2020_ = _args[9];
lean_object* v___y_2021_ = _args[10];
lean_object* v___y_2022_ = _args[11];
lean_object* v___y_2023_ = _args[12];
lean_object* v___y_2024_ = _args[13];
lean_object* v___y_2025_ = _args[14];
lean_object* v___y_2026_ = _args[15];
lean_object* v___y_2027_ = _args[16];
lean_object* v___y_2028_ = _args[17];
lean_object* v___y_2029_ = _args[18];
_start:
{
uint8_t v___y_195978__boxed_2030_; uint8_t v___x_195979__boxed_2031_; uint8_t v___x_195980__boxed_2032_; lean_object* v_res_2033_; 
v___y_195978__boxed_2030_ = lean_unbox(v___y_2013_);
v___x_195979__boxed_2031_ = lean_unbox(v___x_2014_);
v___x_195980__boxed_2032_ = lean_unbox(v___x_2015_);
v_res_2033_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2011_, v_a_2012_, v___y_195978__boxed_2030_, v___x_195979__boxed_2031_, v___x_195980__boxed_2032_, v_mvarId_2016_, v___x_2017_, v_a_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
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
lean_dec_ref(v___x_2011_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2036_, lean_object* v___x_2037_, lean_object* v_generation_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v_mvarId_2036_);
v___x_2050_ = l_Lean_MVarId_getTag(v_mvarId_2036_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2037_, v_a_2051_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_n(v_a_2053_, 2);
lean_dec_ref(v___x_2052_);
v___x_2054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2036_, v_a_2053_, v___y_2046_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; lean_object* v_toGoalState_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v___x_2054_);
v___x_2055_ = lean_st_ref_get(v___y_2039_);
v_toGoalState_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2055_, 1);
lean_dec(v_unused_2066_);
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_toGoalState_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = l_Lean_Expr_mvarId_x21(v_a_2053_);
lean_dec(v_a_2053_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_toGoalState_2056_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; 
v___x_2063_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2062_, v_generation_2038_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_a_2053_);
lean_dec(v_generation_2038_);
v_a_2067_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2054_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2054_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_generation_2038_);
lean_dec(v_mvarId_2036_);
v_a_2075_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2052_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2052_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_generation_2038_);
lean_dec_ref(v___x_2037_);
lean_dec(v_mvarId_2036_);
v_a_2083_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2050_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2050_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2091_, lean_object* v___x_2092_, lean_object* v_generation_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2091_, v___x_2092_, v_generation_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v___y_2094_);
return v_res_2105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2113_ = l_Lean_mkConst(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2114_, lean_object* v_generation_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v_a_2128_; lean_object* v___y_2133_; lean_object* v___x_2143_; lean_object* v_mvarId_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2432_; 
lean_inc_ref(v_goal_2114_);
v___x_2126_ = lean_st_mk_ref(v_goal_2114_);
v___x_2143_ = lean_st_ref_get(v___x_2126_);
v_mvarId_2144_ = lean_ctor_get(v___x_2143_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2143_, 0);
lean_dec(v_unused_2433_);
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2432_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_mvarId_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2432_;
goto v_resetjp_2145_;
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_st_ref_get(v___x_2126_);
lean_dec(v___x_2126_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
v___jp_2132_:
{
if (lean_obj_tag(v___y_2133_) == 0)
{
lean_object* v_a_2134_; 
v_a_2134_ = lean_ctor_get(v___y_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___y_2133_);
v_a_2128_ = v_a_2134_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v___x_2126_);
v_a_2135_ = lean_ctor_get(v___y_2133_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___y_2133_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___y_2133_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___y_2133_);
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
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
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
v_resetjp_2145_:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_MVarId_getType(v_mvarId_2144_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; uint8_t v___x_2150_; uint8_t v___x_2151_; uint8_t v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = l_Lean_Expr_isForall(v_a_2149_);
v___x_2151_ = 1;
if (v___x_2150_ == 0)
{
uint8_t v___x_2193_; 
lean_del_object(v___x_2146_);
v___x_2193_ = l_Lean_Expr_isLet(v_a_2149_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v_a_2149_);
lean_dec_ref(v___y_2121_);
lean_dec(v_generation_2115_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_goal_2114_);
v_a_2128_ = v___x_2194_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v_goal_2114_);
v___x_2195_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2117_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; uint8_t v_zetaDelta_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v_zetaDelta_2197_ = lean_ctor_get_uint8(v_a_2196_, sizeof(void*)*12 + 19);
lean_dec(v_a_2196_);
if (v_zetaDelta_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_a_2149_);
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v_mvarId_2201_; lean_object* v___f_2202_; lean_object* v___x_2203_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = lean_st_ref_get(v___x_2126_);
v_mvarId_2201_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_mvarId_2201_);
lean_dec(v___x_2200_);
v___f_2202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2202_, 0, v_a_2199_);
lean_closure_set(v___f_2202_, 1, v_generation_2115_);
v___x_2203_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2201_, v___f_2202_, v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v___y_2121_);
v___y_2133_ = v___x_2203_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
lean_dec(v_generation_2115_);
v_a_2204_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2198_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2198_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v___x_2212_; lean_object* v_mvarId_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___f_2216_; lean_object* v___x_2217_; 
v___x_2212_ = lean_st_ref_get(v___x_2126_);
v_mvarId_2213_ = lean_ctor_get(v___x_2212_, 1);
lean_inc_n(v_mvarId_2213_, 2);
lean_dec(v___x_2212_);
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2215_ = l_Lean_Meta_expandLet(v_a_2149_, v___x_2214_, v___x_2151_);
lean_dec(v_a_2149_);
v___f_2216_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2216_, 0, v_mvarId_2213_);
lean_closure_set(v___f_2216_, 1, v___x_2215_);
lean_closure_set(v___f_2216_, 2, v_generation_2115_);
v___x_2217_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2213_, v___f_2216_, v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v___y_2121_);
v___y_2133_ = v___x_2217_;
goto v___jp_2132_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
lean_dec(v_generation_2115_);
v_a_2218_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2195_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2195_);
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
}
else
{
lean_object* v___x_2226_; lean_object* v___y_2228_; uint8_t v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; uint8_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v_localInsts_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___x_2324_; 
lean_dec(v_generation_2115_);
lean_dec_ref(v_goal_2114_);
v___x_2226_ = l_Lean_Expr_bindingDomain_x21(v_a_2149_);
lean_inc_ref(v___x_2226_);
v___x_2324_ = l_Lean_Meta_isProp(v___x_2226_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___y_2327_; uint8_t v___x_2400_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v___x_2324_);
v___x_2400_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2400_ == 0)
{
if (v___x_2150_ == 0)
{
lean_del_object(v___x_2146_);
v___y_2327_ = v___x_2150_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
v___x_2401_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v___y_2121_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2401_);
v___x_2403_ = lean_st_ref_get(v___x_2126_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 3);
lean_ctor_set(v___x_2146_, 1, v___x_2403_);
lean_ctor_set(v___x_2146_, 0, v_a_2402_);
v___x_2405_ = v___x_2146_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2402_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
v_a_2128_ = v___x_2405_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_del_object(v___x_2146_);
lean_dec(v___x_2126_);
v_a_2407_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2401_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2401_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
uint8_t v___x_2415_; 
lean_del_object(v___x_2146_);
v___x_2415_ = 0;
v___y_2327_ = v___x_2415_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v_mvarId_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2398_; 
v___x_2328_ = lean_st_ref_get(v___x_2126_);
v_mvarId_2329_ = lean_ctor_get(v___x_2328_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2328_, 0);
lean_dec(v_unused_2399_);
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2398_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_mvarId_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2398_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
lean_inc(v_mvarId_2329_);
v___x_2333_ = l_Lean_MVarId_getTag(v_mvarId_2329_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
lean_inc_ref(v___x_2226_);
v___x_2337_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2226_, v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_expr_2339_; lean_object* v_proof_x3f_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v_expr_2339_ = lean_ctor_get(v_a_2338_, 0);
lean_inc_ref_n(v_expr_2339_, 2);
v_proof_x3f_2340_ = lean_ctor_get(v_a_2338_, 1);
lean_inc(v_proof_x3f_2340_);
lean_dec(v_a_2338_);
v___x_2341_ = l_Lean_Expr_bindingName_x21(v_a_2149_);
lean_inc(v___x_2341_);
v___x_2342_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2341_, v_expr_2339_, v___x_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_lctx_2344_; lean_object* v_localInstances_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v_lctx_2344_ = lean_ctor_get(v___y_2121_, 2);
v_localInstances_2345_ = lean_ctor_get(v___y_2121_, 3);
lean_inc_n(v_a_2336_, 2);
v___x_2346_ = l_Lean_mkFVar(v_a_2336_);
v___x_2347_ = l_Lean_Expr_bindingInfo_x21(v_a_2149_);
v___x_2348_ = 0;
lean_inc_ref_n(v_expr_2339_, 2);
lean_inc_ref(v_lctx_2344_);
v___x_2349_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2344_, v_a_2336_, v_a_2343_, v_expr_2339_, v___x_2347_, v___x_2348_);
v___x_2350_ = l_Lean_Meta_isClass_x3f(v_expr_2339_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = l_Lean_Expr_bindingBody_x21(v_a_2149_);
if (lean_obj_tag(v_a_2351_) == 1)
{
lean_object* v_val_2353_; lean_object* v___x_2355_; 
v_val_2353_ = lean_ctor_get(v_a_2351_, 0);
lean_inc(v_val_2353_);
lean_dec_ref(v_a_2351_);
lean_inc_ref(v___x_2346_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2346_);
lean_ctor_set(v___x_2331_, 0, v_val_2353_);
v___x_2355_ = v___x_2331_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_val_2353_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2346_);
v___x_2355_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
lean_inc_ref(v_localInstances_2345_);
v___x_2356_ = lean_array_push(v_localInstances_2345_, v___x_2355_);
lean_inc(v___x_2126_);
lean_inc_ref(v_expr_2339_);
v___y_2228_ = v_expr_2339_;
v___y_2229_ = v___y_2327_;
v___y_2230_ = v___x_2352_;
v___y_2231_ = v_mvarId_2329_;
v___y_2232_ = v_a_2336_;
v___y_2233_ = v___x_2341_;
v___y_2234_ = v_proof_x3f_2340_;
v___y_2235_ = v_expr_2339_;
v___y_2236_ = v_a_2334_;
v___y_2237_ = v___x_2347_;
v___y_2238_ = v___x_2346_;
v___y_2239_ = v___x_2349_;
v_localInsts_2240_ = v___x_2356_;
v___y_2241_ = v___x_2126_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
v___y_2245_ = v___y_2119_;
v___y_2246_ = v___y_2120_;
v___y_2247_ = v___y_2121_;
v___y_2248_ = v___y_2122_;
v___y_2249_ = v___y_2123_;
v___y_2250_ = v___y_2124_;
goto v___jp_2227_;
}
}
else
{
lean_inc_ref(v_localInstances_2345_);
lean_dec(v_a_2351_);
lean_del_object(v___x_2331_);
lean_inc(v___x_2126_);
lean_inc_ref(v_expr_2339_);
v___y_2228_ = v_expr_2339_;
v___y_2229_ = v___y_2327_;
v___y_2230_ = v___x_2352_;
v___y_2231_ = v_mvarId_2329_;
v___y_2232_ = v_a_2336_;
v___y_2233_ = v___x_2341_;
v___y_2234_ = v_proof_x3f_2340_;
v___y_2235_ = v_expr_2339_;
v___y_2236_ = v_a_2334_;
v___y_2237_ = v___x_2347_;
v___y_2238_ = v___x_2346_;
v___y_2239_ = v___x_2349_;
v_localInsts_2240_ = v_localInstances_2345_;
v___y_2241_ = v___x_2126_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
v___y_2245_ = v___y_2119_;
v___y_2246_ = v___y_2120_;
v___y_2247_ = v___y_2121_;
v___y_2248_ = v___y_2122_;
v___y_2249_ = v___y_2123_;
v___y_2250_ = v___y_2124_;
goto v___jp_2227_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2341_);
lean_dec(v_proof_x3f_2340_);
lean_dec_ref(v_expr_2339_);
lean_dec(v_a_2336_);
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_mvarId_2329_);
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2358_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2350_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2350_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___x_2341_);
lean_dec(v_proof_x3f_2340_);
lean_dec_ref(v_expr_2339_);
lean_dec(v_a_2336_);
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_mvarId_2329_);
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2366_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2342_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2342_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_a_2336_);
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_mvarId_2329_);
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2374_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2337_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2337_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_a_2334_);
lean_del_object(v___x_2331_);
lean_dec(v_mvarId_2329_);
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2382_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2335_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2335_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_del_object(v___x_2331_);
lean_dec(v_mvarId_2329_);
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2390_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2333_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2333_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v___x_2226_);
lean_dec(v_a_2149_);
lean_del_object(v___x_2146_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
v_a_2416_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2324_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2324_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
v___jp_2227_:
{
if (lean_obj_tag(v___y_2234_) == 0)
{
uint8_t v___x_2251_; 
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2226_);
v___x_2251_ = l_Lean_Expr_isArrow(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_expr_instantiate1(v___y_2230_, v___y_2238_);
lean_dec_ref(v___y_2230_);
v___y_2153_ = v___y_2229_;
v___y_2154_ = v___y_2231_;
v___y_2155_ = v___y_2232_;
v___y_2156_ = v___y_2241_;
v___y_2157_ = v___y_2248_;
v___y_2158_ = v___y_2243_;
v___y_2159_ = v___y_2249_;
v___y_2160_ = v___y_2246_;
v___y_2161_ = v___y_2238_;
v___y_2162_ = v___y_2239_;
v___y_2163_ = v___y_2242_;
v___y_2164_ = v___y_2250_;
v___y_2165_ = v_localInsts_2240_;
v___y_2166_ = v___y_2236_;
v___y_2167_ = v___y_2244_;
v___y_2168_ = v___y_2245_;
v___y_2169_ = v___y_2247_;
v___y_2170_ = v___x_2252_;
goto v___jp_2152_;
}
else
{
v___y_2153_ = v___y_2229_;
v___y_2154_ = v___y_2231_;
v___y_2155_ = v___y_2232_;
v___y_2156_ = v___y_2241_;
v___y_2157_ = v___y_2248_;
v___y_2158_ = v___y_2243_;
v___y_2159_ = v___y_2249_;
v___y_2160_ = v___y_2246_;
v___y_2161_ = v___y_2238_;
v___y_2162_ = v___y_2239_;
v___y_2163_ = v___y_2242_;
v___y_2164_ = v___y_2250_;
v___y_2165_ = v_localInsts_2240_;
v___y_2166_ = v___y_2236_;
v___y_2167_ = v___y_2244_;
v___y_2168_ = v___y_2245_;
v___y_2169_ = v___y_2247_;
v___y_2170_ = v___y_2230_;
goto v___jp_2152_;
}
}
else
{
lean_object* v_val_2253_; uint8_t v___x_2254_; 
v_val_2253_ = lean_ctor_get(v___y_2234_, 0);
lean_inc(v_val_2253_);
lean_dec_ref(v___y_2234_);
v___x_2254_ = l_Lean_Expr_isArrow(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_inc_ref(v___y_2230_);
lean_inc_ref_n(v___x_2226_, 2);
v___x_2255_ = l_Lean_mkLambda(v___y_2233_, v___y_2237_, v___x_2226_, v___y_2230_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2238_);
lean_inc(v_val_2253_);
v___x_2258_ = l_Lean_mkApp4(v___x_2257_, v___x_2226_, v___y_2235_, v_val_2253_, v___y_2238_);
v___x_2259_ = lean_expr_instantiate1(v___y_2230_, v___x_2258_);
lean_dec_ref(v___x_2258_);
lean_dec_ref(v___y_2230_);
lean_inc_ref(v___x_2259_);
v___x_2260_ = l_Lean_Meta_getLevel(v___x_2259_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = 2;
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2239_, v_localInsts_2240_, v___x_2259_, v___x_2262_, v___y_2236_, v___x_2263_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = l_Lean_Expr_mvarId_x21(v_a_2265_);
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_mk_empty_array_with_capacity(v___x_2267_);
v___x_2269_ = lean_array_push(v___x_2268_, v___y_2238_);
v___x_2270_ = 1;
v___x_2271_ = lean_box(v___x_2254_);
v___x_2272_ = lean_box(v___x_2151_);
v___x_2273_ = lean_box(v___x_2270_);
lean_inc(v___x_2266_);
v___f_2274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2274_, 0, v___x_2269_);
lean_closure_set(v___f_2274_, 1, v_a_2265_);
lean_closure_set(v___f_2274_, 2, v___x_2271_);
lean_closure_set(v___f_2274_, 3, v___x_2272_);
lean_closure_set(v___f_2274_, 4, v___x_2273_);
lean_closure_set(v___f_2274_, 5, v_a_2261_);
lean_closure_set(v___f_2274_, 6, v___x_2256_);
lean_closure_set(v___f_2274_, 7, v___x_2226_);
lean_closure_set(v___f_2274_, 8, v___y_2228_);
lean_closure_set(v___f_2274_, 9, v___x_2255_);
lean_closure_set(v___f_2274_, 10, v_val_2253_);
lean_closure_set(v___f_2274_, 11, v___y_2231_);
lean_closure_set(v___f_2274_, 12, v___x_2266_);
lean_closure_set(v___f_2274_, 13, v___y_2232_);
v___x_2275_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2266_, v___f_2274_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
v___y_2133_ = v___x_2275_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_a_2261_);
lean_dec_ref(v___x_2255_);
lean_dec(v_val_2253_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2226_);
lean_dec(v___x_2126_);
v_a_2276_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2264_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2264_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2255_);
lean_dec(v_val_2253_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
lean_dec_ref(v_localInsts_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2236_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2226_);
lean_dec(v___x_2126_);
v_a_2284_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2260_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2260_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v___x_2292_; 
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2233_);
lean_inc_ref(v___y_2230_);
v___x_2292_ = l_Lean_Meta_getLevel(v___y_2230_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
v___x_2294_ = 2;
v___x_2295_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2230_);
v___x_2296_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2239_, v_localInsts_2240_, v___y_2230_, v___x_2294_, v___y_2236_, v___x_2295_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2296_);
v___x_2298_ = l_Lean_Expr_mvarId_x21(v_a_2297_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_array_push(v___x_2300_, v___y_2238_);
v___x_2302_ = 1;
v___x_2303_ = lean_box(v___y_2229_);
v___x_2304_ = lean_box(v___x_2151_);
v___x_2305_ = lean_box(v___x_2302_);
lean_inc(v___x_2298_);
v___f_2306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2306_, 0, v___x_2301_);
lean_closure_set(v___f_2306_, 1, v_a_2297_);
lean_closure_set(v___f_2306_, 2, v___x_2303_);
lean_closure_set(v___f_2306_, 3, v___x_2304_);
lean_closure_set(v___f_2306_, 4, v___x_2305_);
lean_closure_set(v___f_2306_, 5, v_a_2293_);
lean_closure_set(v___f_2306_, 6, v___x_2226_);
lean_closure_set(v___f_2306_, 7, v___y_2228_);
lean_closure_set(v___f_2306_, 8, v___y_2230_);
lean_closure_set(v___f_2306_, 9, v_val_2253_);
lean_closure_set(v___f_2306_, 10, v___y_2231_);
lean_closure_set(v___f_2306_, 11, v___x_2298_);
lean_closure_set(v___f_2306_, 12, v___y_2232_);
v___x_2307_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2298_, v___f_2306_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
v___y_2133_ = v___x_2307_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2293_);
lean_dec(v_val_2253_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2226_);
lean_dec(v___x_2126_);
v_a_2308_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2296_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2296_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_val_2253_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2241_);
lean_dec_ref(v_localInsts_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2236_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2226_);
lean_dec(v___x_2126_);
v_a_2316_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2292_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2292_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
}
v___jp_2152_:
{
uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = 2;
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2162_, v___y_2165_, v___y_2170_, v___x_2171_, v___y_2166_, v___x_2172_, v___y_2169_, v___y_2157_, v___y_2159_, v___y_2164_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_Lean_Expr_mvarId_x21(v_a_2174_);
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_mk_empty_array_with_capacity(v___x_2176_);
v___x_2178_ = lean_array_push(v___x_2177_, v___y_2161_);
v___x_2179_ = 1;
v___x_2180_ = lean_box(v___y_2153_);
v___x_2181_ = lean_box(v___x_2151_);
v___x_2182_ = lean_box(v___x_2179_);
lean_inc(v___x_2175_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2183_, 0, v___x_2178_);
lean_closure_set(v___f_2183_, 1, v_a_2174_);
lean_closure_set(v___f_2183_, 2, v___x_2180_);
lean_closure_set(v___f_2183_, 3, v___x_2181_);
lean_closure_set(v___f_2183_, 4, v___x_2182_);
lean_closure_set(v___f_2183_, 5, v___y_2154_);
lean_closure_set(v___f_2183_, 6, v___x_2175_);
lean_closure_set(v___f_2183_, 7, v___y_2155_);
v___x_2184_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2175_, v___f_2183_, v___y_2156_, v___y_2163_, v___y_2158_, v___y_2167_, v___y_2168_, v___y_2160_, v___y_2169_, v___y_2157_, v___y_2159_, v___y_2164_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2156_);
v___y_2133_ = v___x_2184_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___y_2169_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___x_2126_);
v_a_2185_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2173_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2173_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_del_object(v___x_2146_);
lean_dec(v___x_2126_);
lean_dec_ref(v___y_2121_);
lean_dec(v_generation_2115_);
lean_dec_ref(v_goal_2114_);
v_a_2424_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2148_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2148_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2434_, lean_object* v_generation_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2434_, v_generation_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2447_, lean_object* v_generation_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_mvarId_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v_mvarId_2459_ = lean_ctor_get(v_goal_2447_, 1);
lean_inc(v_mvarId_2459_);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2460_, 0, v_goal_2447_);
lean_closure_set(v___f_2460_, 1, v_generation_2448_);
v___x_2461_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2459_, v___f_2460_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2470_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_fst_2466_; lean_object* v___x_2468_; 
v_fst_2466_ = lean_ctor_get(v_a_2462_, 0);
lean_inc(v_fst_2466_);
lean_dec(v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_fst_2466_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_fst_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2461_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2461_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2479_, lean_object* v_generation_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2479_, v_generation_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2492_, lean_object* v_val_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2492_, v_val_2493_, v___y_2501_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2506_, lean_object* v_val_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2506_, v_val_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec(v___y_2508_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec(v___y_2532_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2545_, v_x_2546_, v_x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2549_, lean_object* v_x_2550_, size_t v_x_2551_, size_t v_x_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2550_, v_x_2551_, v_x_2552_, v_x_2553_, v_x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_){
_start:
{
size_t v_x_197005__boxed_2562_; size_t v_x_197006__boxed_2563_; lean_object* v_res_2564_; 
v_x_197005__boxed_2562_ = lean_unbox_usize(v_x_2558_);
lean_dec(v_x_2558_);
v_x_197006__boxed_2563_ = lean_unbox_usize(v_x_2559_);
lean_dec(v_x_2559_);
v_res_2564_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2556_, v_x_2557_, v_x_197005__boxed_2562_, v_x_197006__boxed_2563_, v_x_2560_, v_x_2561_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2565_, lean_object* v_n_2566_, lean_object* v_k_2567_, lean_object* v_v_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2566_, v_k_2567_, v_v_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2570_, size_t v_depth_2571_, lean_object* v_keys_2572_, lean_object* v_vals_2573_, lean_object* v_heq_2574_, lean_object* v_i_2575_, lean_object* v_entries_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2571_, v_keys_2572_, v_vals_2573_, v_i_2575_, v_entries_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2578_, lean_object* v_depth_2579_, lean_object* v_keys_2580_, lean_object* v_vals_2581_, lean_object* v_heq_2582_, lean_object* v_i_2583_, lean_object* v_entries_2584_){
_start:
{
size_t v_depth_boxed_2585_; lean_object* v_res_2586_; 
v_depth_boxed_2585_ = lean_unbox_usize(v_depth_2579_);
lean_dec(v_depth_2579_);
v_res_2586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2578_, v_depth_boxed_2585_, v_keys_2580_, v_vals_2581_, v_heq_2582_, v_i_2583_, v_entries_2584_);
lean_dec_ref(v_vals_2581_);
lean_dec_ref(v_keys_2580_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2587_, lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2588_, v_x_2589_, v_x_2590_, v_x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_Expr_getAppFn(v_type_2593_);
if (lean_obj_tag(v___x_2596_) == 4)
{
lean_object* v_declName_2597_; lean_object* v___x_2598_; 
v_declName_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_declName_2597_);
lean_dec_ref(v___x_2596_);
v___x_2598_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2597_, v_a_2594_);
lean_dec(v_declName_2597_);
return v___x_2598_;
}
else
{
uint8_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___x_2596_);
v___x_2599_ = 0;
v___x_2600_ = lean_box(v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2602_, v_a_2603_);
lean_dec_ref(v_a_2603_);
lean_dec_ref(v_type_2602_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2606_, v_a_2608_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_type_2618_);
return v_res_2629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
lean_ctor_set(v___x_2635_, 2, v___x_2634_);
lean_ctor_set(v___x_2635_, 3, v___x_2634_);
lean_ctor_set(v___x_2635_, 4, v___x_2633_);
lean_ctor_set(v___x_2635_, 5, v___x_2633_);
lean_ctor_set(v___x_2635_, 6, v___x_2633_);
lean_ctor_set(v___x_2635_, 7, v___x_2633_);
lean_ctor_set(v___x_2635_, 8, v___x_2633_);
lean_ctor_set(v___x_2635_, 9, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_unsigned_to_nat(32u);
v___x_2637_ = lean_mk_empty_array_with_capacity(v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2639_ = ((size_t)5ULL);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = lean_unsigned_to_nat(32u);
v___x_2642_ = lean_mk_empty_array_with_capacity(v___x_2641_);
v___x_2643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2644_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v___x_2642_);
lean_ctor_set(v___x_2644_, 2, v___x_2640_);
lean_ctor_set(v___x_2644_, 3, v___x_2640_);
lean_ctor_set_usize(v___x_2644_, 4, v___x_2639_);
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = lean_box(1);
v___x_2646_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___x_2646_);
lean_ctor_set(v___x_2648_, 2, v___x_2645_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2666_ = l_Lean_stringToMessageData(v___x_2665_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2669_ = l_Lean_stringToMessageData(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2670_, lean_object* v_declHint_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; lean_object* v_env_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_st_ref_get(v___y_2672_);
v_env_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2674_);
v___x_2676_ = l_Lean_Name_isAnonymous(v_declHint_2671_);
if (v___x_2676_ == 0)
{
uint8_t v_isExporting_2677_; 
v_isExporting_2677_ = lean_ctor_get_uint8(v_env_2675_, sizeof(void*)*8);
if (v_isExporting_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_msg_2670_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
lean_inc_ref(v_env_2675_);
v___x_2679_ = l_Lean_Environment_setExporting(v_env_2675_, v___x_2676_);
lean_inc(v_declHint_2671_);
lean_inc_ref(v___x_2679_);
v___x_2680_ = l_Lean_Environment_contains(v___x_2679_, v_declHint_2671_, v_isExporting_2677_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref(v___x_2679_);
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_msg_2670_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v_c_2687_; lean_object* v___x_2688_; 
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2684_ = l_Lean_Options_empty;
v___x_2685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2679_);
lean_ctor_set(v___x_2685_, 1, v___x_2682_);
lean_ctor_set(v___x_2685_, 2, v___x_2683_);
lean_ctor_set(v___x_2685_, 3, v___x_2684_);
lean_inc(v_declHint_2671_);
v___x_2686_ = l_Lean_MessageData_ofConstName(v_declHint_2671_, v___x_2676_);
v_c_2687_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2687_, 0, v___x_2685_);
lean_ctor_set(v_c_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2675_, v_declHint_2671_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2689_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_c_2687_);
v___x_2691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_MessageData_note(v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_msg_2670_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
else
{
lean_object* v_val_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2731_; 
v_val_2696_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2698_ = v___x_2688_;
v_isShared_2699_ = v_isSharedCheck_2731_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_val_2696_);
lean_dec(v___x_2688_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2731_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v_mod_2703_; uint8_t v___x_2704_; 
v___x_2700_ = lean_box(0);
v___x_2701_ = l_Lean_Environment_header(v_env_2675_);
lean_dec_ref(v_env_2675_);
v___x_2702_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2701_);
v_mod_2703_ = lean_array_get(v___x_2700_, v___x_2702_, v_val_2696_);
lean_dec(v_val_2696_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = l_Lean_isPrivateName(v_declHint_2671_);
lean_dec(v_declHint_2671_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v_c_2687_);
v___x_2707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_MessageData_ofName(v_mod_2703_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = l_Lean_MessageData_note(v___x_2712_);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_msg_2670_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2714_);
v___x_2716_ = v___x_2698_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_c_2687_);
v___x_2720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_MessageData_ofName(v_mod_2703_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_MessageData_note(v___x_2725_);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_msg_2670_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2727_);
v___x_2729_ = v___x_2698_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2732_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_msg_2670_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2733_, v_declHint_2734_, v___y_2735_);
lean_dec(v___y_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2738_, lean_object* v_declHint_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2753_; 
v___x_2743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2738_, v_declHint_2739_, v___y_2741_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2748_ = l_Lean_unknownIdentifierMessageTag;
v___x_2749_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_a_2744_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2749_);
v___x_2751_ = v___x_2746_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2754_, lean_object* v_declHint_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2754_, v_declHint_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v_env_2765_; lean_object* v_options_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2764_ = lean_st_ref_get(v___y_2762_);
v_env_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc_ref(v_env_2765_);
lean_dec(v___x_2764_);
v_options_2766_ = lean_ctor_get(v___y_2761_, 2);
v___x_2767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2768_ = lean_unsigned_to_nat(32u);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2768_);
lean_dec_ref(v___x_2769_);
v___x_2770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2766_);
v___x_2771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2771_, 0, v_env_2765_);
lean_ctor_set(v___x_2771_, 1, v___x_2767_);
lean_ctor_set(v___x_2771_, 2, v___x_2770_);
lean_ctor_set(v___x_2771_, 3, v_options_2766_);
v___x_2772_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_msgData_2760_);
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_ref_2783_; lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2793_; 
v_ref_2783_ = lean_ctor_get(v___y_2780_, 5);
v___x_2784_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2779_, v___y_2780_, v___y_2781_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2793_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2793_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_inc(v_ref_2783_);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v_ref_2783_);
lean_ctor_set(v___x_2789_, 1, v_a_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 1);
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2791_ = v___x_2787_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2799_, lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_fileName_2804_; lean_object* v_fileMap_2805_; lean_object* v_options_2806_; lean_object* v_currRecDepth_2807_; lean_object* v_maxRecDepth_2808_; lean_object* v_ref_2809_; lean_object* v_currNamespace_2810_; lean_object* v_openDecls_2811_; lean_object* v_initHeartbeats_2812_; lean_object* v_maxHeartbeats_2813_; lean_object* v_quotContext_2814_; lean_object* v_currMacroScope_2815_; uint8_t v_diag_2816_; lean_object* v_cancelTk_x3f_2817_; uint8_t v_suppressElabErrors_2818_; lean_object* v_inheritedTraceOptions_2819_; lean_object* v_ref_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_fileName_2804_ = lean_ctor_get(v___y_2801_, 0);
v_fileMap_2805_ = lean_ctor_get(v___y_2801_, 1);
v_options_2806_ = lean_ctor_get(v___y_2801_, 2);
v_currRecDepth_2807_ = lean_ctor_get(v___y_2801_, 3);
v_maxRecDepth_2808_ = lean_ctor_get(v___y_2801_, 4);
v_ref_2809_ = lean_ctor_get(v___y_2801_, 5);
v_currNamespace_2810_ = lean_ctor_get(v___y_2801_, 6);
v_openDecls_2811_ = lean_ctor_get(v___y_2801_, 7);
v_initHeartbeats_2812_ = lean_ctor_get(v___y_2801_, 8);
v_maxHeartbeats_2813_ = lean_ctor_get(v___y_2801_, 9);
v_quotContext_2814_ = lean_ctor_get(v___y_2801_, 10);
v_currMacroScope_2815_ = lean_ctor_get(v___y_2801_, 11);
v_diag_2816_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14);
v_cancelTk_x3f_2817_ = lean_ctor_get(v___y_2801_, 12);
v_suppressElabErrors_2818_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2819_ = lean_ctor_get(v___y_2801_, 13);
v_ref_2820_ = l_Lean_replaceRef(v_ref_2799_, v_ref_2809_);
lean_inc_ref(v_inheritedTraceOptions_2819_);
lean_inc(v_cancelTk_x3f_2817_);
lean_inc(v_currMacroScope_2815_);
lean_inc(v_quotContext_2814_);
lean_inc(v_maxHeartbeats_2813_);
lean_inc(v_initHeartbeats_2812_);
lean_inc(v_openDecls_2811_);
lean_inc(v_currNamespace_2810_);
lean_inc(v_maxRecDepth_2808_);
lean_inc(v_currRecDepth_2807_);
lean_inc_ref(v_options_2806_);
lean_inc_ref(v_fileMap_2805_);
lean_inc_ref(v_fileName_2804_);
v___x_2821_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2821_, 0, v_fileName_2804_);
lean_ctor_set(v___x_2821_, 1, v_fileMap_2805_);
lean_ctor_set(v___x_2821_, 2, v_options_2806_);
lean_ctor_set(v___x_2821_, 3, v_currRecDepth_2807_);
lean_ctor_set(v___x_2821_, 4, v_maxRecDepth_2808_);
lean_ctor_set(v___x_2821_, 5, v_ref_2820_);
lean_ctor_set(v___x_2821_, 6, v_currNamespace_2810_);
lean_ctor_set(v___x_2821_, 7, v_openDecls_2811_);
lean_ctor_set(v___x_2821_, 8, v_initHeartbeats_2812_);
lean_ctor_set(v___x_2821_, 9, v_maxHeartbeats_2813_);
lean_ctor_set(v___x_2821_, 10, v_quotContext_2814_);
lean_ctor_set(v___x_2821_, 11, v_currMacroScope_2815_);
lean_ctor_set(v___x_2821_, 12, v_cancelTk_x3f_2817_);
lean_ctor_set(v___x_2821_, 13, v_inheritedTraceOptions_2819_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*14, v_diag_2816_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*14 + 1, v_suppressElabErrors_2818_);
v___x_2822_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2800_, v___x_2821_, v___y_2802_);
lean_dec_ref(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2823_, lean_object* v_msg_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2823_, v_msg_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v_ref_2823_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2829_, lean_object* v_msg_2830_, lean_object* v_declHint_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v_a_2836_; lean_object* v___x_2837_; 
v___x_2835_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2830_, v_declHint_2831_, v___y_2832_, v___y_2833_);
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2829_, v_a_2836_, v___y_2832_, v___y_2833_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2838_, lean_object* v_msg_2839_, lean_object* v_declHint_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2838_, v_msg_2839_, v_declHint_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v_ref_2838_);
return v_res_2844_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2847_ = l_Lean_stringToMessageData(v___x_2846_);
return v___x_2847_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2850_ = l_Lean_stringToMessageData(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2851_, lean_object* v_constName_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2856_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2857_ = 0;
lean_inc(v_constName_2852_);
v___x_2858_ = l_Lean_MessageData_ofConstName(v_constName_2852_, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2856_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2851_, v___x_2861_, v_constName_2852_, v___y_2853_, v___y_2854_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2863_, lean_object* v_constName_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2863_, v_constName_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v_ref_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_ref_2873_; lean_object* v___x_2874_; 
v_ref_2873_ = lean_ctor_get(v___y_2870_, 5);
v___x_2874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2873_, v_constName_2869_, v___y_2870_, v___y_2871_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_env_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2884_ = lean_st_ref_get(v___y_2882_);
v_env_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_env_2885_);
lean_dec(v___x_2884_);
v___x_2886_ = 0;
lean_inc(v_constName_2880_);
v___x_2887_ = l_Lean_Environment_find_x3f(v_env_2885_, v_constName_2880_, v___x_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2880_, v___y_2881_, v___y_2882_);
return v___x_2888_;
}
else
{
lean_object* v_val_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_constName_2880_);
v_val_2889_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2887_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_val_2889_);
lean_dec(v___x_2887_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 0);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_val_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Expr_getAppFn(v_type_2902_);
if (lean_obj_tag(v___x_2906_) == 4)
{
lean_object* v_declName_2907_; lean_object* v___x_2908_; 
v_declName_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_declName_2907_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2907_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2926_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2926_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2926_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
if (lean_obj_tag(v_a_2909_) == 5)
{
lean_object* v_val_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
v_val_2913_ = lean_ctor_get(v_a_2909_, 0);
lean_inc_ref(v_val_2913_);
lean_dec_ref(v_a_2909_);
v___x_2914_ = l_Lean_InductiveVal_numCtors(v_val_2913_);
lean_dec_ref(v_val_2913_);
v___x_2915_ = lean_unsigned_to_nat(1u);
v___x_2916_ = lean_nat_dec_le(v___x_2914_, v___x_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(v___x_2916_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2917_);
v___x_2919_ = v___x_2911_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
else
{
uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
lean_dec(v_a_2909_);
v___x_2921_ = 0;
v___x_2922_ = lean_box(v___x_2921_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2922_);
v___x_2924_ = v___x_2911_;
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
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2908_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2908_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec_ref(v___x_2906_);
v___x_2935_ = 0;
v___x_2936_ = lean_box(v___x_2935_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec_ref(v_type_2938_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2943_, lean_object* v_constName_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_constName_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2949_, v_constName_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2955_, lean_object* v_ref_2956_, lean_object* v_constName_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2956_, v_constName_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v_constName_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2962_, v_ref_2963_, v_constName_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_ref_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2969_, lean_object* v_ref_2970_, lean_object* v_msg_2971_, lean_object* v_declHint_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2970_, v_msg_2971_, v_declHint_2972_, v___y_2973_, v___y_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_ref_2978_, lean_object* v_msg_2979_, lean_object* v_declHint_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2977_, v_ref_2978_, v_msg_2979_, v_declHint_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v_ref_2978_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2985_, lean_object* v_declHint_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2985_, v_declHint_2986_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2991_, lean_object* v_declHint_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2991_, v_declHint_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2997_, lean_object* v_ref_2998_, lean_object* v_msg_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2998_, v_msg_2999_, v___y_3000_, v___y_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_ref_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3004_, v_ref_3005_, v_msg_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v_ref_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3012_, v___y_3013_, v___y_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3017_, lean_object* v_msg_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3017_, v_msg_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3023_, lean_object* v_fvarId_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_toGoalState_3030_; lean_object* v_mvarId_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3067_; 
v_toGoalState_3030_ = lean_ctor_get(v_goal_3023_, 0);
v_mvarId_3031_ = lean_ctor_get(v_goal_3023_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_goal_3023_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3033_ = v_goal_3023_;
v_isShared_3034_ = v_isSharedCheck_3067_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_mvarId_3031_);
lean_inc(v_toGoalState_3030_);
lean_dec(v_goal_3023_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3067_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3031_, v_fvarId_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3058_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3058_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3058_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
if (lean_obj_tag(v_a_3036_) == 1)
{
lean_object* v_val_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3053_; 
v_val_3040_ = lean_ctor_get(v_a_3036_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3042_ = v_a_3036_;
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_val_3040_);
lean_dec(v_a_3036_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v_val_3040_);
v___x_3045_ = v___x_3033_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_toGoalState_3030_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_val_3040_);
v___x_3045_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3045_);
v___x_3047_ = v___x_3042_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3049_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3047_);
v___x_3049_ = v___x_3038_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_dec(v_a_3036_);
lean_del_object(v___x_3033_);
lean_dec_ref(v_toGoalState_3030_);
v___x_3054_ = lean_box(0);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3054_);
v___x_3056_ = v___x_3038_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_del_object(v___x_3033_);
lean_dec_ref(v_toGoalState_3030_);
v_a_3059_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3035_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3035_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3068_, lean_object* v_fvarId_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3068_, v_fvarId_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3076_, v_x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3092_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3083_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3083_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3100_, v_x_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3108_, lean_object* v_mvarId_3109_, lean_object* v_x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3109_, v_x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3117_, lean_object* v_mvarId_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3117_, v_mvarId_3118_, v_x_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3126_, lean_object* v_toGoalState_3127_, lean_object* v_goal_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; 
lean_inc(v_mvarId_3126_);
v___x_3134_ = l_Lean_MVarId_getType(v_mvarId_3126_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v___x_3136_ = l_Lean_Meta_isProp(v_a_3135_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3163_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3163_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3163_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_unbox(v_a_3137_);
lean_dec(v_a_3137_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_del_object(v___x_3139_);
lean_dec_ref(v_goal_3128_);
v___x_3142_ = l_Lean_MVarId_exfalso(v_mvarId_3126_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3151_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_toGoalState_3127_);
lean_ctor_set(v___x_3147_, 1, v_a_3143_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3147_);
v___x_3149_ = v___x_3145_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_toGoalState_3127_);
v_a_3152_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3142_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3142_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v___x_3161_; 
lean_dec_ref(v_toGoalState_3127_);
lean_dec(v_mvarId_3126_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v_goal_3128_);
v___x_3161_ = v___x_3139_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_goal_3128_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_goal_3128_);
lean_dec_ref(v_toGoalState_3127_);
lean_dec(v_mvarId_3126_);
v_a_3164_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3136_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3136_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v_goal_3128_);
lean_dec_ref(v_toGoalState_3127_);
lean_dec(v_mvarId_3126_);
v_a_3172_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3134_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3134_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3180_, lean_object* v_toGoalState_3181_, lean_object* v_goal_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3180_, v_toGoalState_3181_, v_goal_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_toGoalState_3195_; lean_object* v_mvarId_3196_; lean_object* v___f_3197_; lean_object* v___x_3198_; 
v_toGoalState_3195_ = lean_ctor_get(v_goal_3189_, 0);
lean_inc_ref(v_toGoalState_3195_);
v_mvarId_3196_ = lean_ctor_get(v_goal_3189_, 1);
lean_inc_n(v_mvarId_3196_, 2);
v___f_3197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3197_, 0, v_mvarId_3196_);
lean_closure_set(v___f_3197_, 1, v_toGoalState_3195_);
lean_closure_set(v___f_3197_, 2, v_goal_3189_);
v___x_3198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3196_, v___f_3197_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_mvarId_3212_; lean_object* v___x_3213_; 
v_mvarId_3212_ = lean_ctor_get(v_goal_3206_, 1);
lean_inc(v_mvarId_3212_);
lean_dec_ref(v_goal_3206_);
v___x_3213_ = l_Lean_MVarId_getDecl(v_mvarId_3212_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3223_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3223_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3223_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v_lctx_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v_lctx_3218_ = lean_ctor_get(v_a_3214_, 1);
lean_inc_ref(v_lctx_3218_);
lean_dec(v_a_3214_);
v___x_3219_ = l_Lean_LocalContext_lastDecl(v_lctx_3218_);
lean_dec_ref(v_lctx_3218_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3219_);
v___x_3221_ = v___x_3216_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
v_a_3224_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3213_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3213_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
if (lean_obj_tag(v_a_3240_) == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = l_List_reverse___redArg(v_a_3241_);
return v___x_3242_;
}
else
{
lean_object* v_head_3243_; lean_object* v_tail_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3254_; 
v_head_3243_ = lean_ctor_get(v_a_3240_, 0);
v_tail_3244_ = lean_ctor_get(v_a_3240_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3246_ = v_a_3240_;
v_isShared_3247_ = v_isSharedCheck_3254_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_tail_3244_);
lean_inc(v_head_3243_);
lean_dec(v_a_3240_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3254_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_toGoalState_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v_toGoalState_3248_ = lean_ctor_get(v_goal_3239_, 0);
lean_inc_ref(v_toGoalState_3248_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_toGoalState_3248_);
lean_ctor_set(v___x_3249_, 1, v_head_3243_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 1, v_a_3241_);
lean_ctor_set(v___x_3246_, 0, v___x_3249_);
v___x_3251_ = v___x_3246_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_a_3241_);
v___x_3251_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
v_a_3240_ = v_tail_3244_;
v_a_3241_ = v___x_3251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3255_, v_a_3256_, v_a_3257_);
lean_dec_ref(v_goal_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3259_, lean_object* v_as_x27_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
if (lean_obj_tag(v_as_x27_3260_) == 0)
{
lean_object* v___x_3272_; 
lean_dec_ref(v_kp_3259_);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_b_3261_);
return v___x_3272_;
}
else
{
lean_object* v_head_3273_; lean_object* v_tail_3274_; lean_object* v___x_3275_; 
v_head_3273_ = lean_ctor_get(v_as_x27_3260_, 0);
v_tail_3274_ = lean_ctor_get(v_as_x27_3260_, 1);
lean_inc_ref(v_kp_3259_);
lean_inc(v___y_3270_);
lean_inc_ref(v___y_3269_);
lean_inc(v___y_3268_);
lean_inc_ref(v___y_3267_);
lean_inc(v___y_3266_);
lean_inc_ref(v___y_3265_);
lean_inc(v___y_3264_);
lean_inc_ref(v___y_3263_);
lean_inc(v___y_3262_);
lean_inc(v_head_3273_);
v___x_3275_ = lean_apply_11(v_kp_3259_, v_head_3273_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, lean_box(0));
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref(v___x_3275_);
if (lean_obj_tag(v_a_3276_) == 0)
{
lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3288_; 
v_fst_3277_ = lean_ctor_get(v_b_3261_, 0);
v_snd_3278_ = lean_ctor_get(v_b_3261_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_b_3261_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3280_ = v_b_3261_;
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_snd_3278_);
lean_inc(v_fst_3277_);
lean_dec(v_b_3261_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v_seq_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v_seq_3282_ = lean_ctor_get(v_a_3276_, 0);
lean_inc(v_seq_3282_);
lean_dec_ref(v_a_3276_);
v___x_3283_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3277_, v_seq_3282_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3283_);
v___x_3285_ = v___x_3280_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_snd_3278_);
v___x_3285_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
v_as_x27_3260_ = v_tail_3274_;
v_b_3261_ = v___x_3285_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3289_; lean_object* v_snd_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3300_; 
v_fst_3289_ = lean_ctor_get(v_b_3261_, 0);
v_snd_3290_ = lean_ctor_get(v_b_3261_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_b_3261_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3292_ = v_b_3261_;
v_isShared_3293_ = v_isSharedCheck_3300_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_snd_3290_);
lean_inc(v_fst_3289_);
lean_dec(v_b_3261_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3300_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_gs_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v_gs_3294_ = lean_ctor_get(v_a_3276_, 0);
lean_inc(v_gs_3294_);
lean_dec_ref(v_a_3276_);
v___x_3295_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3290_, v_gs_3294_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v___x_3295_);
v___x_3297_ = v___x_3292_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_fst_3289_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
v_as_x27_3260_ = v_tail_3274_;
v_b_3261_ = v___x_3297_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_b_3261_);
lean_dec_ref(v_kp_3259_);
v_a_3301_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3275_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3275_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3309_, lean_object* v_as_x27_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3309_, v_as_x27_3310_, v_b_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v_as_x27_3310_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3327_, lean_object* v_mvarId_3328_, lean_object* v_goal_3329_, lean_object* v_kp_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___x_3396_; 
lean_inc(v_fvarId_3327_);
v___x_3396_ = l_Lean_FVarId_getType___redArg(v_fvarId_3327_, v___y_3336_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
v___x_3398_ = lean_whnf(v_a_3397_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___x_3421_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3421_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3399_, v___y_3332_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3461_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3461_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3461_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_unbox(v_a_3422_);
lean_dec(v_a_3422_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v___x_3427_ = lean_box(0);
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
else
{
lean_object* v___x_3431_; 
lean_del_object(v___x_3424_);
v___x_3431_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3332_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; uint8_t v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = lean_unbox(v_a_3432_);
lean_dec(v_a_3432_);
if (v___x_3433_ == 0)
{
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
v___y_3404_ = v___y_3334_;
v___y_3405_ = v___y_3335_;
v___y_3406_ = v___y_3336_;
v___y_3407_ = v___y_3337_;
v___y_3408_ = v___y_3338_;
v___y_3409_ = v___y_3339_;
goto v___jp_3400_;
}
else
{
lean_object* v___x_3434_; 
v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3399_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3444_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3444_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v___x_3440_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3440_);
v___x_3442_ = v___x_3437_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
lean_del_object(v___x_3437_);
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
v___y_3404_ = v___y_3334_;
v___y_3405_ = v___y_3335_;
v___y_3406_ = v___y_3336_;
v___y_3407_ = v___y_3337_;
v___y_3408_ = v___y_3338_;
v___y_3409_ = v___y_3339_;
goto v___jp_3400_;
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3445_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3434_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3434_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3453_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3431_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3431_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec(v_a_3399_);
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3462_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3421_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3421_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
v___jp_3400_:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Expr_getAppFn(v_a_3399_);
lean_dec(v_a_3399_);
if (lean_obj_tag(v___x_3410_) == 4)
{
lean_object* v_declName_3411_; lean_object* v___x_3412_; 
v_declName_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_declName_3411_);
lean_dec_ref(v___x_3410_);
v___x_3412_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3411_, v___y_3403_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref(v___x_3412_);
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
v___y_3345_ = v___y_3404_;
v___y_3346_ = v___y_3405_;
v___y_3347_ = v___y_3406_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3408_;
v___y_3350_ = v___y_3409_;
goto v___jp_3341_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_dec_ref(v___x_3410_);
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
v___y_3345_ = v___y_3404_;
v___y_3346_ = v___y_3405_;
v___y_3347_ = v___y_3406_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3408_;
v___y_3350_ = v___y_3409_;
goto v___jp_3341_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3470_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3398_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3398_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_kp_3330_);
lean_dec(v_mvarId_3328_);
lean_dec(v_fvarId_3327_);
v_a_3478_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3396_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3396_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
v___jp_3341_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = l_Lean_mkFVar(v_fvarId_3327_);
v___x_3352_ = l_Lean_Meta_Grind_cases(v_mvarId_3328_, v___x_3351_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = lean_box(0);
v___x_3355_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3329_, v_a_3353_, v___x_3354_);
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3358_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3330_, v___x_3355_, v___x_3357_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___x_3355_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3379_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3361_ = v___x_3358_;
v_isShared_3362_ = v_isSharedCheck_3379_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3379_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_fst_3363_; lean_object* v_snd_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_fst_3363_ = lean_ctor_get(v_a_3359_, 0);
lean_inc(v_fst_3363_);
v_snd_3364_ = lean_ctor_get(v_a_3359_, 1);
lean_inc(v_snd_3364_);
lean_dec(v_a_3359_);
v___x_3365_ = lean_array_get_size(v_snd_3364_);
v___x_3366_ = lean_nat_dec_eq(v___x_3365_, v___x_3356_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
lean_dec(v_fst_3363_);
v___x_3367_ = lean_array_to_list(v_snd_3364_);
v___x_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3369_);
v___x_3371_ = v___x_3361_;
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
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_dec(v_snd_3364_);
v___x_3373_ = lean_array_to_list(v_fst_3363_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3375_);
v___x_3377_ = v___x_3361_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
v_a_3380_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3358_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3358_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_kp_3330_);
v_a_3388_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3352_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3352_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3486_, lean_object* v_mvarId_3487_, lean_object* v_goal_3488_, lean_object* v_kp_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3486_, v_mvarId_3487_, v_goal_3488_, v_kp_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v_goal_3488_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3501_, lean_object* v_fvarId_3502_, lean_object* v_kp_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v_mvarId_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; 
v_mvarId_3514_ = lean_ctor_get(v_goal_3501_, 1);
lean_inc_n(v_mvarId_3514_, 2);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3515_, 0, v_fvarId_3502_);
lean_closure_set(v___f_3515_, 1, v_mvarId_3514_);
lean_closure_set(v___f_3515_, 2, v_goal_3501_);
lean_closure_set(v___f_3515_, 3, v_kp_3503_);
v___x_3516_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3514_, v___f_3515_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3517_, lean_object* v_fvarId_3518_, lean_object* v_kp_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3517_, v_fvarId_3518_, v_kp_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3531_, lean_object* v_as_3532_, lean_object* v_as_x27_3533_, lean_object* v_b_3534_, lean_object* v_a_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3531_, v_as_x27_3533_, v_b_3534_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3547_, lean_object* v_as_3548_, lean_object* v_as_x27_3549_, lean_object* v_b_3550_, lean_object* v_a_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3547_, v_as_3548_, v_as_x27_3549_, v_b_3550_, v_a_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec(v_as_x27_3549_);
lean_dec(v_as_3548_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3563_, lean_object* v_fvarId_3564_, lean_object* v_generation_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = lean_st_mk_ref(v_goal_3563_);
v___x_3577_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3564_, v_generation_3565_, v___x_3576_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v___x_3577_, 0);
lean_dec(v_unused_3587_);
v___x_3579_ = v___x_3577_;
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v___x_3577_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3581_ = lean_st_ref_get(v___x_3576_);
v___x_3582_ = lean_st_ref_get(v___x_3576_);
lean_dec(v___x_3576_);
lean_dec(v___x_3582_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3581_);
v___x_3584_ = v___x_3579_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3581_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3576_);
v_a_3588_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3577_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3577_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3596_, lean_object* v_fvarId_3597_, lean_object* v_generation_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3596_, v_fvarId_3597_, v_generation_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3612_, lean_object* v_goal_3613_, lean_object* v_kna_3614_, lean_object* v_kp_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_toGoalState_3626_; uint8_t v_inconsistent_3627_; 
v_toGoalState_3626_ = lean_ctor_get(v_goal_3613_, 0);
v_inconsistent_3627_ = lean_ctor_get_uint8(v_toGoalState_3626_, sizeof(void*)*17);
if (v_inconsistent_3627_ == 0)
{
lean_object* v_mvarId_3628_; lean_object* v___x_3629_; 
v_mvarId_3628_ = lean_ctor_get(v_goal_3613_, 1);
lean_inc(v_mvarId_3628_);
v___x_3629_ = l_Lean_MVarId_getType(v_mvarId_3628_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; uint8_t v___x_3631_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = l_Lean_Expr_isFalse(v_a_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
lean_dec_ref(v_kna_3614_);
lean_inc(v_generation_3612_);
v___x_3632_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3613_, v_generation_3612_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref(v___x_3632_);
switch(lean_obj_tag(v_a_3633_))
{
case 0:
{
lean_object* v_goal_3634_; lean_object* v___x_3635_; 
lean_dec(v_generation_3612_);
v_goal_3634_ = lean_ctor_get(v_a_3633_, 0);
lean_inc_ref(v_goal_3634_);
lean_dec_ref(v_a_3633_);
v___x_3635_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3634_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v_toGoalState_3637_; lean_object* v_mvarId_3638_; lean_object* v___x_3639_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
v_toGoalState_3637_ = lean_ctor_get(v_a_3636_, 0);
v_mvarId_3638_ = lean_ctor_get(v_a_3636_, 1);
lean_inc(v_mvarId_3638_);
v___x_3639_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3638_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3639_);
if (lean_obj_tag(v_a_3640_) == 1)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3649_; 
lean_inc_ref(v_toGoalState_3637_);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_a_3636_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; lean_object* v_unused_3651_; 
v_unused_3650_ = lean_ctor_get(v_a_3636_, 1);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_a_3636_, 0);
lean_dec(v_unused_3651_);
v___x_3642_ = v_a_3636_;
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v_a_3636_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_val_3644_; lean_object* v___x_3646_; 
v_val_3644_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_val_3644_);
lean_dec_ref(v_a_3640_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 1, v_val_3644_);
v___x_3646_ = v___x_3642_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_toGoalState_3637_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_val_3644_);
v___x_3646_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; 
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3647_ = lean_apply_11(v_kp_3615_, v___x_3646_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3647_;
}
}
}
else
{
lean_object* v___x_3652_; 
lean_dec(v_a_3640_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3652_ = lean_apply_11(v_kp_3615_, v_a_3636_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3652_;
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v_a_3636_);
lean_dec_ref(v_kp_3615_);
v_a_3653_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3639_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3639_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v_kp_3615_);
v_a_3661_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3635_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3635_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3669_; lean_object* v_goal_3670_; lean_object* v___x_3671_; 
v_fvarId_3669_ = lean_ctor_get(v_a_3633_, 0);
lean_inc_n(v_fvarId_3669_, 2);
v_goal_3670_ = lean_ctor_get(v_a_3633_, 1);
lean_inc_ref_n(v_goal_3670_, 2);
lean_dec_ref(v_a_3633_);
v___x_3671_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3670_, v_fvarId_3669_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
if (lean_obj_tag(v_a_3672_) == 1)
{
lean_object* v_val_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v_goal_3670_);
lean_dec(v_fvarId_3669_);
lean_dec(v_generation_3612_);
v_val_3673_ = lean_ctor_get(v_a_3672_, 0);
lean_inc(v_val_3673_);
lean_dec_ref(v_a_3672_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3674_ = lean_apply_11(v_kp_3615_, v_val_3673_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3674_;
}
else
{
lean_object* v___x_3675_; 
lean_dec(v_a_3672_);
lean_inc_ref(v_kp_3615_);
lean_inc(v_fvarId_3669_);
lean_inc_ref(v_goal_3670_);
v___x_3675_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3670_, v_fvarId_3669_, v_kp_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3697_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3697_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3697_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
if (lean_obj_tag(v_a_3676_) == 1)
{
lean_object* v_val_3680_; lean_object* v___x_3682_; 
lean_dec_ref(v_goal_3670_);
lean_dec(v_fvarId_3669_);
lean_dec_ref(v_kp_3615_);
lean_dec(v_generation_3612_);
v_val_3680_ = lean_ctor_get(v_a_3676_, 0);
lean_inc(v_val_3680_);
lean_dec_ref(v_a_3676_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v_val_3680_);
v___x_3682_ = v___x_3678_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_val_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
lean_object* v_mvarId_3684_; lean_object* v___f_3685_; lean_object* v___x_3686_; 
lean_del_object(v___x_3678_);
lean_dec(v_a_3676_);
v_mvarId_3684_ = lean_ctor_get(v_goal_3670_, 1);
lean_inc(v_mvarId_3684_);
v___f_3685_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3685_, 0, v_goal_3670_);
lean_closure_set(v___f_3685_, 1, v_fvarId_3669_);
lean_closure_set(v___f_3685_, 2, v_generation_3612_);
v___x_3686_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3684_, v___f_3685_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref(v___x_3686_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3688_ = lean_apply_11(v_kp_3615_, v_a_3687_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec_ref(v_kp_3615_);
v_a_3689_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3686_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3686_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v_goal_3670_);
lean_dec(v_fvarId_3669_);
lean_dec_ref(v_kp_3615_);
lean_dec(v_generation_3612_);
v_a_3698_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3675_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3675_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_goal_3670_);
lean_dec(v_fvarId_3669_);
lean_dec_ref(v_kp_3615_);
lean_dec(v_generation_3612_);
v_a_3706_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3671_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3671_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
case 2:
{
lean_object* v_goal_3714_; lean_object* v___x_3715_; 
lean_dec(v_generation_3612_);
v_goal_3714_ = lean_ctor_get(v_a_3633_, 0);
lean_inc_ref(v_goal_3714_);
lean_dec_ref(v_a_3633_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3715_ = lean_apply_11(v_kp_3615_, v_goal_3714_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3715_;
}
default: 
{
lean_object* v_fvarId_3716_; lean_object* v_goal_3717_; lean_object* v___x_3718_; 
lean_dec(v_generation_3612_);
v_fvarId_3716_ = lean_ctor_get(v_a_3633_, 0);
lean_inc(v_fvarId_3716_);
v_goal_3717_ = lean_ctor_get(v_a_3633_, 1);
lean_inc_ref_n(v_goal_3717_, 2);
lean_dec_ref(v_a_3633_);
lean_inc_ref(v_kp_3615_);
v___x_3718_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3717_, v_fvarId_3716_, v_kp_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3728_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3728_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3728_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 1)
{
lean_object* v_val_3723_; lean_object* v___x_3725_; 
lean_dec_ref(v_goal_3717_);
lean_dec_ref(v_kp_3615_);
v_val_3723_ = lean_ctor_get(v_a_3719_, 0);
lean_inc(v_val_3723_);
lean_dec_ref(v_a_3719_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v_val_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_val_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
else
{
lean_object* v___x_3727_; 
lean_del_object(v___x_3721_);
lean_dec(v_a_3719_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3727_ = lean_apply_11(v_kp_3615_, v_goal_3717_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v_goal_3717_);
lean_dec_ref(v_kp_3615_);
v_a_3729_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3718_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3718_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec_ref(v_kp_3615_);
lean_dec(v_generation_3612_);
v_a_3737_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3632_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3632_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v___x_3745_; 
lean_dec_ref(v_kp_3615_);
lean_dec(v_generation_3612_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
lean_inc(v_a_3618_);
lean_inc_ref(v_a_3617_);
lean_inc(v_a_3616_);
v___x_3745_ = lean_apply_11(v_kna_3614_, v_goal_3613_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3745_;
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v_kp_3615_);
lean_dec_ref(v_kna_3614_);
lean_dec_ref(v_goal_3613_);
lean_dec(v_generation_3612_);
v_a_3746_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3629_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3629_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_dec_ref(v_kp_3615_);
lean_dec_ref(v_kna_3614_);
lean_dec_ref(v_goal_3613_);
lean_dec(v_generation_3612_);
v___x_3754_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3756_, lean_object* v_goal_3757_, lean_object* v_kna_3758_, lean_object* v_kp_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Meta_Grind_Action_intro(v_generation_3756_, v_goal_3757_, v_kna_3758_, v_kp_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
return v_res_3770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_unsigned_to_nat(1000000u);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3772_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3787_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3800_, lean_object* v___f_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3815_ = lean_unsigned_to_nat(1000000u);
v___x_3816_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3816_, 0, v_generation_3800_);
v___x_3817_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3817_, 0, v___x_3815_);
lean_closure_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_Meta_Grind_Action_andThen(v___x_3817_, v___f_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3819_, lean_object* v___f_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3819_, v___f_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3837_, lean_object* v_a_3838_, lean_object* v_kna_3839_, lean_object* v_kp_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___f_3851_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3852_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3852_, 0, v_generation_3837_);
lean_closure_set(v___f_3852_, 1, v___f_3851_);
v___x_3853_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3854_ = l_Lean_Meta_Grind_Action_andThen(v___x_3853_, v___f_3852_, v_a_3838_, v_kna_3839_, v_kp_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3855_, lean_object* v_a_3856_, lean_object* v_kna_3857_, lean_object* v_kp_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Meta_Grind_Action_intros(v_generation_3855_, v_a_3856_, v_kna_3857_, v_kp_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
return v_res_3869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3879_ = l_Lean_mkConst(v___x_3878_, v___x_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3880_, lean_object* v_prop_3881_, lean_object* v_proof_3882_, lean_object* v_generation_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_st_mk_ref(v_goal_3880_);
lean_inc(v___y_3892_);
lean_inc_ref(v___y_3891_);
lean_inc(v___y_3890_);
lean_inc_ref(v___y_3889_);
lean_inc(v___y_3888_);
lean_inc_ref(v___y_3887_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3885_);
lean_inc(v___y_3884_);
lean_inc(v___x_3894_);
lean_inc_ref(v_prop_3881_);
v___x_3895_ = lean_grind_preprocess(v_prop_3881_, v___x_3894_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v_expr_3897_; lean_object* v___x_3898_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v_expr_3897_ = lean_ctor_get(v_a_3896_, 0);
lean_inc_ref(v_expr_3897_);
v___x_3898_ = l_Lean_Meta_Simp_Result_getProof(v_a_3896_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3897_);
v___x_3901_ = l_Lean_mkApp4(v___x_3900_, v_prop_3881_, v_expr_3897_, v_a_3899_, v_proof_3882_);
v___x_3902_ = l_Lean_Meta_Grind_add(v_expr_3897_, v___x_3901_, v_generation_3883_, v___x_3894_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v___x_3902_, 0);
lean_dec(v_unused_3912_);
v___x_3904_ = v___x_3902_;
v_isShared_3905_ = v_isSharedCheck_3911_;
goto v_resetjp_3903_;
}
else
{
lean_dec(v___x_3902_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3911_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3906_ = lean_st_ref_get(v___x_3894_);
v___x_3907_ = lean_st_ref_get(v___x_3894_);
lean_dec(v___x_3894_);
lean_dec(v___x_3907_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3906_);
v___x_3909_ = v___x_3904_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3906_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v___x_3894_);
v_a_3913_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3902_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3902_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v_expr_3897_);
lean_dec(v___x_3894_);
lean_dec(v_generation_3883_);
lean_dec_ref(v_proof_3882_);
lean_dec_ref(v_prop_3881_);
v_a_3921_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3898_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3898_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v___x_3894_);
lean_dec(v_generation_3883_);
lean_dec_ref(v_proof_3882_);
lean_dec_ref(v_prop_3881_);
v_a_3929_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3895_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3895_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3937_, lean_object* v_prop_3938_, lean_object* v_proof_3939_, lean_object* v_generation_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3937_, v_prop_3938_, v_proof_3939_, v_generation_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3952_, lean_object* v___f_3953_, lean_object* v_kp_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3952_, v___f_3953_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
lean_inc(v___y_3963_);
lean_inc_ref(v___y_3962_);
lean_inc(v___y_3961_);
lean_inc_ref(v___y_3960_);
lean_inc(v___y_3959_);
lean_inc_ref(v___y_3958_);
lean_inc(v___y_3957_);
lean_inc_ref(v___y_3956_);
lean_inc(v___y_3955_);
v___x_3967_ = lean_apply_11(v_kp_3954_, v_a_3966_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, lean_box(0));
return v___x_3967_;
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v_kp_3954_);
v_a_3968_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3965_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3965_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3976_, lean_object* v___f_3977_, lean_object* v_kp_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3976_, v___f_3977_, v_kp_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3990_, lean_object* v_prop_3991_, lean_object* v_generation_3992_, lean_object* v_goal_3993_, lean_object* v_kna_3994_, lean_object* v_kp_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3991_, v_a_3997_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; uint8_t v___x_4008_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref(v___x_4006_);
v___x_4008_ = lean_unbox(v_a_4007_);
lean_dec(v_a_4007_);
if (v___x_4008_ == 0)
{
lean_object* v_mvarId_4009_; lean_object* v___f_4010_; lean_object* v___f_4011_; lean_object* v___x_4012_; 
lean_dec_ref(v_kna_3994_);
v_mvarId_4009_ = lean_ctor_get(v_goal_3993_, 1);
lean_inc_n(v_mvarId_4009_, 2);
v___f_4010_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4010_, 0, v_goal_3993_);
lean_closure_set(v___f_4010_, 1, v_prop_3991_);
lean_closure_set(v___f_4010_, 2, v_proof_3990_);
lean_closure_set(v___f_4010_, 3, v_generation_3992_);
v___f_4011_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4011_, 0, v_mvarId_4009_);
lean_closure_set(v___f_4011_, 1, v___f_4010_);
lean_closure_set(v___f_4011_, 2, v_kp_3995_);
v___x_4012_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4009_, v___f_4011_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4014_ = l_Lean_Core_mkFreshUserName(v___x_4013_, v_a_4003_, v_a_4004_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v_toGoalState_4016_; lean_object* v_mvarId_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4035_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref(v___x_4014_);
v_toGoalState_4016_ = lean_ctor_get(v_goal_3993_, 0);
v_mvarId_4017_ = lean_ctor_get(v_goal_3993_, 1);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_goal_3993_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4019_ = v_goal_3993_;
v_isShared_4020_ = v_isSharedCheck_4035_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_mvarId_4017_);
lean_inc(v_toGoalState_4016_);
lean_dec(v_goal_3993_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4035_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Lean_MVarId_assert(v_mvarId_4017_, v_a_4015_, v_prop_3991_, v_proof_3990_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4021_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 1, v_a_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_toGoalState_4016_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_a_4022_);
v___x_4024_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_Meta_Grind_Action_intros(v_generation_3992_, v___x_4024_, v_kna_3994_, v_kp_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
return v___x_4025_;
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_del_object(v___x_4019_);
lean_dec_ref(v_toGoalState_4016_);
lean_dec_ref(v_kp_3995_);
lean_dec_ref(v_kna_3994_);
lean_dec(v_generation_3992_);
v_a_4027_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4021_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4021_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec_ref(v_kp_3995_);
lean_dec_ref(v_kna_3994_);
lean_dec_ref(v_goal_3993_);
lean_dec(v_generation_3992_);
lean_dec_ref(v_prop_3991_);
lean_dec_ref(v_proof_3990_);
v_a_4036_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4014_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4014_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v_kp_3995_);
lean_dec_ref(v_kna_3994_);
lean_dec_ref(v_goal_3993_);
lean_dec(v_generation_3992_);
lean_dec_ref(v_prop_3991_);
lean_dec_ref(v_proof_3990_);
v_a_4044_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4006_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4006_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4052_, lean_object* v_prop_4053_, lean_object* v_generation_4054_, lean_object* v_goal_4055_, lean_object* v_kna_4056_, lean_object* v_kp_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4052_, v_prop_4053_, v_generation_4054_, v_goal_4055_, v_kna_4056_, v_kp_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4069_, lean_object* v_kna_4070_, lean_object* v_kp_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_toGoalState_4082_; uint8_t v_inconsistent_4083_; 
v_toGoalState_4082_ = lean_ctor_get(v_goal_4069_, 0);
lean_inc_ref(v_toGoalState_4082_);
v_inconsistent_4083_ = lean_ctor_get_uint8(v_toGoalState_4082_, sizeof(void*)*17);
if (v_inconsistent_4083_ == 0)
{
lean_object* v_mvarId_4084_; lean_object* v_nextDeclIdx_4085_; lean_object* v_enodeMap_4086_; lean_object* v_exprs_4087_; lean_object* v_parents_4088_; lean_object* v_congrTable_4089_; lean_object* v_appMap_4090_; lean_object* v_indicesFound_4091_; lean_object* v_newFacts_4092_; lean_object* v_nextIdx_4093_; lean_object* v_newRawFacts_4094_; lean_object* v_facts_4095_; lean_object* v_extThms_4096_; lean_object* v_ematch_4097_; lean_object* v_inj_4098_; lean_object* v_split_4099_; lean_object* v_clean_4100_; lean_object* v_sstates_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4139_; 
v_mvarId_4084_ = lean_ctor_get(v_goal_4069_, 1);
v_nextDeclIdx_4085_ = lean_ctor_get(v_toGoalState_4082_, 0);
v_enodeMap_4086_ = lean_ctor_get(v_toGoalState_4082_, 1);
v_exprs_4087_ = lean_ctor_get(v_toGoalState_4082_, 2);
v_parents_4088_ = lean_ctor_get(v_toGoalState_4082_, 3);
v_congrTable_4089_ = lean_ctor_get(v_toGoalState_4082_, 4);
v_appMap_4090_ = lean_ctor_get(v_toGoalState_4082_, 5);
v_indicesFound_4091_ = lean_ctor_get(v_toGoalState_4082_, 6);
v_newFacts_4092_ = lean_ctor_get(v_toGoalState_4082_, 7);
v_nextIdx_4093_ = lean_ctor_get(v_toGoalState_4082_, 8);
v_newRawFacts_4094_ = lean_ctor_get(v_toGoalState_4082_, 9);
v_facts_4095_ = lean_ctor_get(v_toGoalState_4082_, 10);
v_extThms_4096_ = lean_ctor_get(v_toGoalState_4082_, 11);
v_ematch_4097_ = lean_ctor_get(v_toGoalState_4082_, 12);
v_inj_4098_ = lean_ctor_get(v_toGoalState_4082_, 13);
v_split_4099_ = lean_ctor_get(v_toGoalState_4082_, 14);
v_clean_4100_ = lean_ctor_get(v_toGoalState_4082_, 15);
v_sstates_4101_ = lean_ctor_get(v_toGoalState_4082_, 16);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_toGoalState_4082_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4103_ = v_toGoalState_4082_;
v_isShared_4104_ = v_isSharedCheck_4139_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_sstates_4101_);
lean_inc(v_clean_4100_);
lean_inc(v_split_4099_);
lean_inc(v_inj_4098_);
lean_inc(v_ematch_4097_);
lean_inc(v_extThms_4096_);
lean_inc(v_facts_4095_);
lean_inc(v_newRawFacts_4094_);
lean_inc(v_nextIdx_4093_);
lean_inc(v_newFacts_4092_);
lean_inc(v_indicesFound_4091_);
lean_inc(v_appMap_4090_);
lean_inc(v_congrTable_4089_);
lean_inc(v_parents_4088_);
lean_inc(v_exprs_4087_);
lean_inc(v_enodeMap_4086_);
lean_inc(v_nextDeclIdx_4085_);
lean_dec(v_toGoalState_4082_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4139_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4094_);
if (lean_obj_tag(v___x_4105_) == 1)
{
lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4135_; 
lean_inc(v_mvarId_4084_);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_goal_4069_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; lean_object* v_unused_4137_; 
v_unused_4136_ = lean_ctor_get(v_goal_4069_, 1);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_goal_4069_, 0);
lean_dec(v_unused_4137_);
v___x_4107_ = v_goal_4069_;
v_isShared_4108_ = v_isSharedCheck_4135_;
goto v_resetjp_4106_;
}
else
{
lean_dec(v_goal_4069_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4135_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v_val_4109_; lean_object* v_fst_4110_; lean_object* v_snd_4111_; lean_object* v_proof_4112_; lean_object* v_prop_4113_; lean_object* v_generation_4114_; lean_object* v_splitSource_4115_; lean_object* v_ematchDiagSource_4116_; lean_object* v_simp_4117_; lean_object* v_simpMethods_4118_; lean_object* v_config_4119_; lean_object* v_anchorRefs_x3f_4120_; uint8_t v_cheapCases_4121_; uint8_t v_reportMVarIssue_4122_; lean_object* v_symPrios_4123_; lean_object* v_extensions_4124_; uint8_t v_debug_4125_; uint8_t v_ematchDiag_4126_; lean_object* v___x_4128_; 
v_val_4109_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_val_4109_);
lean_dec_ref(v___x_4105_);
v_fst_4110_ = lean_ctor_get(v_val_4109_, 0);
lean_inc(v_fst_4110_);
v_snd_4111_ = lean_ctor_get(v_val_4109_, 1);
lean_inc(v_snd_4111_);
lean_dec(v_val_4109_);
v_proof_4112_ = lean_ctor_get(v_fst_4110_, 0);
lean_inc_ref(v_proof_4112_);
v_prop_4113_ = lean_ctor_get(v_fst_4110_, 1);
lean_inc_ref(v_prop_4113_);
v_generation_4114_ = lean_ctor_get(v_fst_4110_, 2);
lean_inc(v_generation_4114_);
v_splitSource_4115_ = lean_ctor_get(v_fst_4110_, 3);
lean_inc(v_splitSource_4115_);
v_ematchDiagSource_4116_ = lean_ctor_get(v_fst_4110_, 4);
lean_inc(v_ematchDiagSource_4116_);
lean_dec(v_fst_4110_);
v_simp_4117_ = lean_ctor_get(v_a_4073_, 0);
v_simpMethods_4118_ = lean_ctor_get(v_a_4073_, 1);
v_config_4119_ = lean_ctor_get(v_a_4073_, 2);
v_anchorRefs_x3f_4120_ = lean_ctor_get(v_a_4073_, 3);
v_cheapCases_4121_ = lean_ctor_get_uint8(v_a_4073_, sizeof(void*)*8);
v_reportMVarIssue_4122_ = lean_ctor_get_uint8(v_a_4073_, sizeof(void*)*8 + 1);
v_symPrios_4123_ = lean_ctor_get(v_a_4073_, 6);
v_extensions_4124_ = lean_ctor_get(v_a_4073_, 7);
v_debug_4125_ = lean_ctor_get_uint8(v_a_4073_, sizeof(void*)*8 + 2);
v_ematchDiag_4126_ = lean_ctor_get_uint8(v_a_4073_, sizeof(void*)*8 + 3);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 9, v_snd_4111_);
v___x_4128_ = v___x_4103_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_nextDeclIdx_4085_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_enodeMap_4086_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_exprs_4087_);
lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_parents_4088_);
lean_ctor_set(v_reuseFailAlloc_4134_, 4, v_congrTable_4089_);
lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_appMap_4090_);
lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_indicesFound_4091_);
lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_newFacts_4092_);
lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_nextIdx_4093_);
lean_ctor_set(v_reuseFailAlloc_4134_, 9, v_snd_4111_);
lean_ctor_set(v_reuseFailAlloc_4134_, 10, v_facts_4095_);
lean_ctor_set(v_reuseFailAlloc_4134_, 11, v_extThms_4096_);
lean_ctor_set(v_reuseFailAlloc_4134_, 12, v_ematch_4097_);
lean_ctor_set(v_reuseFailAlloc_4134_, 13, v_inj_4098_);
lean_ctor_set(v_reuseFailAlloc_4134_, 14, v_split_4099_);
lean_ctor_set(v_reuseFailAlloc_4134_, 15, v_clean_4100_);
lean_ctor_set(v_reuseFailAlloc_4134_, 16, v_sstates_4101_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*17, v_inconsistent_4083_);
v___x_4128_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v_goal_4130_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v___x_4128_);
v_goal_4130_ = v___x_4107_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4128_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_mvarId_4084_);
v_goal_4130_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_inc_ref(v_extensions_4124_);
lean_inc_ref(v_symPrios_4123_);
lean_inc(v_anchorRefs_x3f_4120_);
lean_inc_ref(v_config_4119_);
lean_inc_ref(v_simpMethods_4118_);
lean_inc_ref(v_simp_4117_);
v___x_4131_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_4131_, 0, v_simp_4117_);
lean_ctor_set(v___x_4131_, 1, v_simpMethods_4118_);
lean_ctor_set(v___x_4131_, 2, v_config_4119_);
lean_ctor_set(v___x_4131_, 3, v_anchorRefs_x3f_4120_);
lean_ctor_set(v___x_4131_, 4, v_splitSource_4115_);
lean_ctor_set(v___x_4131_, 5, v_ematchDiagSource_4116_);
lean_ctor_set(v___x_4131_, 6, v_symPrios_4123_);
lean_ctor_set(v___x_4131_, 7, v_extensions_4124_);
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*8, v_cheapCases_4121_);
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*8 + 1, v_reportMVarIssue_4122_);
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*8 + 2, v_debug_4125_);
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*8 + 3, v_ematchDiag_4126_);
v___x_4132_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4112_, v_prop_4113_, v_generation_4114_, v_goal_4130_, v_kna_4070_, v_kp_4071_, v_a_4072_, v___x_4131_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
lean_dec_ref(v___x_4131_);
return v___x_4132_;
}
}
}
}
else
{
lean_object* v___x_4138_; 
lean_dec(v___x_4105_);
lean_del_object(v___x_4103_);
lean_dec_ref(v_sstates_4101_);
lean_dec_ref(v_clean_4100_);
lean_dec_ref(v_split_4099_);
lean_dec_ref(v_inj_4098_);
lean_dec_ref(v_ematch_4097_);
lean_dec_ref(v_extThms_4096_);
lean_dec_ref(v_facts_4095_);
lean_dec(v_nextIdx_4093_);
lean_dec_ref(v_newFacts_4092_);
lean_dec_ref(v_indicesFound_4091_);
lean_dec_ref(v_appMap_4090_);
lean_dec_ref(v_congrTable_4089_);
lean_dec_ref(v_parents_4088_);
lean_dec_ref(v_exprs_4087_);
lean_dec_ref(v_enodeMap_4086_);
lean_dec(v_nextDeclIdx_4085_);
lean_dec_ref(v_kp_4071_);
lean_inc(v_a_4080_);
lean_inc_ref(v_a_4079_);
lean_inc(v_a_4078_);
lean_inc_ref(v_a_4077_);
lean_inc(v_a_4076_);
lean_inc_ref(v_a_4075_);
lean_inc(v_a_4074_);
lean_inc_ref(v_a_4073_);
lean_inc(v_a_4072_);
v___x_4138_ = lean_apply_11(v_kna_4070_, v_goal_4069_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, lean_box(0));
return v___x_4138_;
}
}
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_dec_ref(v_toGoalState_4082_);
lean_dec_ref(v_kp_4071_);
lean_dec_ref(v_kna_4070_);
lean_dec_ref(v_goal_4069_);
v___x_4140_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
return v___x_4141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4142_, lean_object* v_kna_4143_, lean_object* v_kp_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4142_, v_kna_4143_, v_kp_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4156_, lean_object* v_kp_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4168_ = lean_unsigned_to_nat(1000000u);
v___x_4169_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4170_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4168_, v___x_4169_, v_a_4156_, v_kp_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4171_, lean_object* v_kp_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4171_, v_kp_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4184_, lean_object* v_kna_4185_, lean_object* v_kp_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4184_, v_kp_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4198_, lean_object* v_kna_4199_, lean_object* v_kp_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4198_, v_kna_4199_, v_kp_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_kna_4199_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4212_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4227_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4240_, lean_object* v___f_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Meta_Grind_Action_andThen(v_a_4240_, v___f_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4256_, lean_object* v___f_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4256_, v___f_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4284_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4277_ = v___x_4274_;
v_isShared_4278_ = v_isSharedCheck_4284_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4274_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4284_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___x_4282_; 
v___f_4279_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4280_, 0, v_a_4275_);
lean_closure_set(v___f_4280_, 1, v___f_4279_);
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 0, v___f_4280_);
v___x_4282_ = v___x_4277_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___f_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
else
{
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4286_;
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
