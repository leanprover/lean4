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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0;
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
size_t v_x_39912__boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_x_39912__boxed_292_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_res_293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_289_, v_x_39912__boxed_292_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_x_289_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_295_; uint64_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1723u);
v___x_296_ = lean_uint64_of_nat(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint64_t v___y_300_; 
if (lean_obj_tag(v_x_298_) == 0)
{
uint64_t v___x_303_; 
v___x_303_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
v___y_300_ = v___x_303_;
goto v___jp_299_;
}
else
{
uint64_t v_hash_304_; 
v_hash_304_ = lean_ctor_get_uint64(v_x_298_, sizeof(void*)*2);
v___y_300_ = v_hash_304_;
goto v___jp_299_;
}
v___jp_299_:
{
size_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_uint64_to_usize(v___y_300_);
v___x_302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_297_, v___x_301_, v_x_298_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_x_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v_toGoalState_314_; lean_object* v_clean_315_; lean_object* v_snd_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_333_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_toGoalState_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_toGoalState_314_);
lean_dec(v___x_313_);
v_clean_315_ = lean_ctor_get(v_toGoalState_314_, 15);
lean_inc_ref(v_clean_315_);
lean_dec_ref(v_toGoalState_314_);
v_snd_316_ = lean_ctor_get(v_a_310_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_a_310_, 0);
lean_dec(v_unused_334_);
v___x_318_ = v_a_310_;
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snd_316_);
lean_dec(v_a_310_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_333_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_used_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_used_320_ = lean_ctor_get(v_clean_315_, 0);
lean_inc_ref(v_used_320_);
lean_dec_ref(v_clean_315_);
lean_inc(v_snd_316_);
lean_inc(v_a_309_);
v___x_321_ = lean_name_append_index_after(v_a_309_, v_snd_316_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_snd_316_, v___x_322_);
lean_dec(v_snd_316_);
v___x_324_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_320_, v___x_321_);
lean_dec_ref(v_used_320_);
if (v___x_324_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_a_309_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_323_);
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_326_ = v___x_318_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_323_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
else
{
lean_object* v___x_330_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_323_);
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_330_ = v___x_318_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_323_);
v___x_330_ = v_reuseFailAlloc_332_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v_a_310_ = v___x_330_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_335_, v_a_336_, v___y_337_);
lean_dec(v___y_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_ks_344_; lean_object* v_vs_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_369_; 
v_ks_344_ = lean_ctor_get(v_x_340_, 0);
v_vs_345_ = lean_ctor_get(v_x_340_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_369_ == 0)
{
v___x_347_ = v_x_340_;
v_isShared_348_ = v_isSharedCheck_369_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_vs_345_);
lean_inc(v_ks_344_);
lean_dec(v_x_340_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_369_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_array_get_size(v_ks_344_);
v___x_350_ = lean_nat_dec_lt(v_x_341_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v_x_341_);
v___x_351_ = lean_array_push(v_ks_344_, v_x_342_);
v___x_352_ = lean_array_push(v_vs_345_, v_x_343_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_352_);
lean_ctor_set(v___x_347_, 0, v___x_351_);
v___x_354_ = v___x_347_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_352_);
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
lean_object* v_k_x27_356_; uint8_t v___x_357_; 
v_k_x27_356_ = lean_array_fget_borrowed(v_ks_344_, v_x_341_);
v___x_357_ = lean_name_eq(v_x_342_, v_k_x27_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_359_; 
if (v_isShared_348_ == 0)
{
v___x_359_ = v___x_347_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_ks_344_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_vs_345_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_x_341_, v___x_360_);
lean_dec(v_x_341_);
v_x_340_ = v___x_359_;
v_x_341_ = v___x_361_;
goto _start;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_364_ = lean_array_fset(v_ks_344_, v_x_341_, v_x_342_);
v___x_365_ = lean_array_fset(v_vs_345_, v_x_341_, v_x_343_);
lean_dec(v_x_341_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_365_);
lean_ctor_set(v___x_347_, 0, v___x_364_);
v___x_367_ = v___x_347_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_370_, lean_object* v_k_371_, lean_object* v_v_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_370_, v___x_373_, v_k_371_, v_v_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_376_, size_t v_x_377_, size_t v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v_es_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v_j_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_es_381_ = lean_ctor_get(v_x_376_, 0);
v___x_382_ = ((size_t)31ULL);
v___x_383_ = lean_usize_land(v_x_377_, v___x_382_);
v_j_384_ = lean_usize_to_nat(v___x_383_);
v___x_385_ = lean_array_get_size(v_es_381_);
v___x_386_ = lean_nat_dec_lt(v_j_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec(v_j_384_);
lean_dec(v_x_380_);
lean_dec(v_x_379_);
return v_x_376_;
}
else
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_425_; 
lean_inc_ref(v_es_381_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_x_376_, 0);
lean_dec(v_unused_426_);
v___x_388_ = v_x_376_;
v_isShared_389_ = v_isSharedCheck_425_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_x_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_425_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_v_390_; lean_object* v___x_391_; lean_object* v_xs_x27_392_; lean_object* v___y_394_; 
v_v_390_ = lean_array_fget(v_es_381_, v_j_384_);
v___x_391_ = lean_box(0);
v_xs_x27_392_ = lean_array_fset(v_es_381_, v_j_384_, v___x_391_);
switch(lean_obj_tag(v_v_390_))
{
case 0:
{
lean_object* v_key_399_; lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_410_; 
v_key_399_ = lean_ctor_get(v_v_390_, 0);
v_val_400_ = lean_ctor_get(v_v_390_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_v_390_);
if (v_isSharedCheck_410_ == 0)
{
v___x_402_ = v_v_390_;
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_inc(v_key_399_);
lean_dec(v_v_390_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
uint8_t v___x_404_; 
v___x_404_ = lean_name_eq(v_x_379_, v_key_399_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_del_object(v___x_402_);
v___x_405_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_399_, v_val_400_, v_x_379_, v_x_380_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
v___y_394_ = v___x_406_;
goto v___jp_393_;
}
else
{
lean_object* v___x_408_; 
lean_dec(v_val_400_);
lean_dec(v_key_399_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v_x_380_);
lean_ctor_set(v___x_402_, 0, v_x_379_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_x_379_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_x_380_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v___y_394_ = v___x_408_;
goto v___jp_393_;
}
}
}
}
case 1:
{
lean_object* v_node_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_423_; 
v_node_411_ = lean_ctor_get(v_v_390_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_v_390_);
if (v_isSharedCheck_423_ == 0)
{
v___x_413_ = v_v_390_;
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_node_411_);
lean_dec(v_v_390_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_415_ = ((size_t)5ULL);
v___x_416_ = lean_usize_shift_right(v_x_377_, v___x_415_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_x_378_, v___x_417_);
v___x_419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_411_, v___x_416_, v___x_418_, v_x_379_, v_x_380_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_419_);
v___x_421_ = v___x_413_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v___y_394_ = v___x_421_;
goto v___jp_393_;
}
}
}
default: 
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_x_379_);
lean_ctor_set(v___x_424_, 1, v_x_380_);
v___y_394_ = v___x_424_;
goto v___jp_393_;
}
}
v___jp_393_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_array_fset(v_xs_x27_392_, v_j_384_, v___y_394_);
lean_dec(v_j_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_395_);
v___x_397_ = v___x_388_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v_vs_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_448_; 
v_ks_427_ = lean_ctor_get(v_x_376_, 0);
v_vs_428_ = lean_ctor_get(v_x_376_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_448_ == 0)
{
v___x_430_ = v_x_376_;
v_isShared_431_ = v_isSharedCheck_448_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_vs_428_);
lean_inc(v_ks_427_);
lean_dec(v_x_376_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_448_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_ks_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_vs_428_);
v___x_433_ = v_reuseFailAlloc_447_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v_newNode_434_; uint8_t v___y_436_; size_t v___x_442_; uint8_t v___x_443_; 
v_newNode_434_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_433_, v_x_379_, v_x_380_);
v___x_442_ = ((size_t)7ULL);
v___x_443_ = lean_usize_dec_le(v___x_442_, v_x_378_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_434_);
v___x_445_ = lean_unsigned_to_nat(4u);
v___x_446_ = lean_nat_dec_lt(v___x_444_, v___x_445_);
lean_dec(v___x_444_);
v___y_436_ = v___x_446_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___x_443_;
goto v___jp_435_;
}
v___jp_435_:
{
if (v___y_436_ == 0)
{
lean_object* v_ks_437_; lean_object* v_vs_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_ks_437_ = lean_ctor_get(v_newNode_434_, 0);
lean_inc_ref(v_ks_437_);
v_vs_438_ = lean_ctor_get(v_newNode_434_, 1);
lean_inc_ref(v_vs_438_);
lean_dec_ref(v_newNode_434_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_378_, v_ks_437_, v_vs_438_, v___x_439_, v___x_440_);
lean_dec_ref(v_vs_438_);
lean_dec_ref(v_ks_437_);
return v___x_441_;
}
else
{
return v_newNode_434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_449_, lean_object* v_keys_450_, lean_object* v_vals_451_, lean_object* v_i_452_, lean_object* v_entries_453_){
_start:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_array_get_size(v_keys_450_);
v___x_455_ = lean_nat_dec_lt(v_i_452_, v___x_454_);
if (v___x_455_ == 0)
{
lean_dec(v_i_452_);
return v_entries_453_;
}
else
{
lean_object* v_k_456_; lean_object* v_v_457_; uint64_t v___y_459_; 
v_k_456_ = lean_array_fget_borrowed(v_keys_450_, v_i_452_);
v_v_457_ = lean_array_fget_borrowed(v_vals_451_, v_i_452_);
if (lean_obj_tag(v_k_456_) == 0)
{
uint64_t v___x_470_; 
v___x_470_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
v___y_459_ = v___x_470_;
goto v___jp_458_;
}
else
{
uint64_t v_hash_471_; 
v_hash_471_ = lean_ctor_get_uint64(v_k_456_, sizeof(void*)*2);
v___y_459_ = v_hash_471_;
goto v___jp_458_;
}
v___jp_458_:
{
size_t v_h_460_; size_t v___x_461_; lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v_h_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_h_460_ = lean_uint64_to_usize(v___y_459_);
v___x_461_ = ((size_t)5ULL);
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_sub(v_depth_449_, v___x_463_);
v___x_465_ = lean_usize_mul(v___x_461_, v___x_464_);
v_h_466_ = lean_usize_shift_right(v_h_460_, v___x_465_);
v___x_467_ = lean_nat_add(v_i_452_, v___x_462_);
lean_dec(v_i_452_);
lean_inc(v_v_457_);
lean_inc(v_k_456_);
v___x_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_453_, v_h_466_, v_depth_449_, v_k_456_, v_v_457_);
v_i_452_ = v___x_467_;
v_entries_453_ = v___x_468_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_472_, lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
size_t v_depth_boxed_477_; lean_object* v_res_478_; 
v_depth_boxed_477_ = lean_unbox_usize(v_depth_472_);
lean_dec(v_depth_472_);
v_res_478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_477_, v_keys_473_, v_vals_474_, v_i_475_, v_entries_476_);
lean_dec_ref(v_vals_474_);
lean_dec_ref(v_keys_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
size_t v_x_40101__boxed_484_; size_t v_x_40102__boxed_485_; lean_object* v_res_486_; 
v_x_40101__boxed_484_ = lean_unbox_usize(v_x_480_);
lean_dec(v_x_480_);
v_x_40102__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_res_486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_479_, v_x_40101__boxed_484_, v_x_40102__boxed_485_, v_x_482_, v_x_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
uint64_t v___y_491_; 
if (lean_obj_tag(v_x_488_) == 0)
{
uint64_t v___x_495_; 
v___x_495_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
v___y_491_ = v___x_495_;
goto v___jp_490_;
}
else
{
uint64_t v_hash_496_; 
v_hash_496_ = lean_ctor_get_uint64(v_x_488_, sizeof(void*)*2);
v___y_491_ = v_hash_496_;
goto v___jp_490_;
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_uint64_to_usize(v___y_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_487_, v___x_492_, v___x_493_, v_x_488_, v_x_489_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_i_499_, lean_object* v_k_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_keys_497_);
v___x_502_ = lean_nat_dec_lt(v_i_499_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v_i_499_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v_k_x27_504_; uint8_t v___x_505_; 
v_k_x27_504_ = lean_array_fget_borrowed(v_keys_497_, v_i_499_);
v___x_505_ = lean_name_eq(v_k_500_, v_k_x27_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_i_499_, v___x_506_);
lean_dec(v_i_499_);
v_i_499_ = v___x_507_;
goto _start;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_array_fget_borrowed(v_vals_498_, v_i_499_);
lean_dec(v_i_499_);
lean_inc(v___x_509_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_i_513_, lean_object* v_k_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_511_, v_vals_512_, v_i_513_, v_k_514_);
lean_dec(v_k_514_);
lean_dec_ref(v_vals_512_);
lean_dec_ref(v_keys_511_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_516_, size_t v_x_517_, lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_es_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_j_523_; lean_object* v___x_524_; 
v_es_519_ = lean_ctor_get(v_x_516_, 0);
v___x_520_ = lean_box(2);
v___x_521_ = ((size_t)31ULL);
v___x_522_ = lean_usize_land(v_x_517_, v___x_521_);
v_j_523_ = lean_usize_to_nat(v___x_522_);
v___x_524_ = lean_array_get_borrowed(v___x_520_, v_es_519_, v_j_523_);
lean_dec(v_j_523_);
switch(lean_obj_tag(v___x_524_))
{
case 0:
{
lean_object* v_key_525_; lean_object* v_val_526_; uint8_t v___x_527_; 
v_key_525_ = lean_ctor_get(v___x_524_, 0);
v_val_526_ = lean_ctor_get(v___x_524_, 1);
v___x_527_ = lean_name_eq(v_x_518_, v_key_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
lean_inc(v_val_526_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_val_526_);
return v___x_529_;
}
}
case 1:
{
lean_object* v_node_530_; size_t v___x_531_; size_t v___x_532_; 
v_node_530_ = lean_ctor_get(v___x_524_, 0);
v___x_531_ = ((size_t)5ULL);
v___x_532_ = lean_usize_shift_right(v_x_517_, v___x_531_);
v_x_516_ = v_node_530_;
v_x_517_ = v___x_532_;
goto _start;
}
default: 
{
lean_object* v___x_534_; 
v___x_534_ = lean_box(0);
return v___x_534_;
}
}
}
else
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_ks_535_ = lean_ctor_get(v_x_516_, 0);
v_vs_536_ = lean_ctor_get(v_x_516_, 1);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_535_, v_vs_536_, v___x_537_, v_x_518_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
size_t v_x_40298__boxed_542_; lean_object* v_res_543_; 
v_x_40298__boxed_542_ = lean_unbox_usize(v_x_540_);
lean_dec(v_x_540_);
v_res_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_539_, v_x_40298__boxed_542_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_x_539_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
uint64_t v___y_547_; 
if (lean_obj_tag(v_x_545_) == 0)
{
uint64_t v___x_550_; 
v___x_550_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
v___y_547_ = v___x_550_;
goto v___jp_546_;
}
else
{
uint64_t v_hash_551_; 
v_hash_551_ = lean_ctor_get_uint64(v_x_545_, sizeof(void*)*2);
v___y_547_ = v_hash_551_;
goto v___jp_546_;
}
v___jp_546_:
{
size_t v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_uint64_to_usize(v___y_547_);
v___x_549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_544_, v___x_548_, v_x_545_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_x_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_558_, lean_object* v_type_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_name_572_; lean_object* v___y_573_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v_name_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_562_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_786_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_786_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_786_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_786_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v_clean_751_; 
v_clean_751_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*13 + 16);
lean_dec(v_a_726_);
if (v_clean_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_558_);
if (lean_obj_tag(v___x_752_) == 1)
{
lean_object* v_val_753_; lean_object* v___x_755_; 
lean_dec_ref(v_type_559_);
lean_dec(v_name_558_);
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v___x_752_, 1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_val_753_);
v___x_755_ = v___x_728_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_val_753_);
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
uint8_t v___x_757_; 
lean_dec(v___x_752_);
v___x_757_ = l_Lean_Name_hasMacroScopes(v_name_558_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_del_object(v___x_728_);
lean_dec_ref(v_type_559_);
v___x_758_ = l_Lean_Core_mkFreshUserName(v_name_558_, v_a_568_, v_a_569_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = l_Lean_Name_eraseMacroScopes(v_name_558_);
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_761_ = lean_name_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_763_ = lean_name_eq(v___x_759_, v___x_762_);
lean_dec(v___x_759_);
if (v___x_763_ == 0)
{
lean_object* v___x_765_; 
lean_dec_ref(v_type_559_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_name_558_);
v___x_765_ = v___x_728_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_name_558_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_del_object(v___x_728_);
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_759_);
lean_del_object(v___x_728_);
goto v___jp_730_;
}
}
}
}
else
{
uint8_t v___x_767_; 
lean_del_object(v___x_728_);
v___x_767_ = l_Lean_Name_hasMacroScopes(v_name_558_);
if (v___x_767_ == 0)
{
v_name_700_ = v_name_558_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
goto v___jp_699_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_768_ = l_Lean_Name_eraseMacroScopes(v_name_558_);
lean_dec(v_name_558_);
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_783_ = lean_name_eq(v___x_768_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_785_ = lean_name_eq(v___x_768_, v___x_784_);
if (v___x_785_ == 0)
{
v_name_700_ = v___x_768_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
goto v___jp_699_;
}
else
{
goto v___jp_769_;
}
}
else
{
goto v___jp_769_;
}
v___jp_769_:
{
lean_object* v___x_770_; 
lean_inc_ref(v_type_559_);
v___x_770_ = l_Lean_Meta_isProp(v_type_559_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; uint8_t v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_unbox(v_a_771_);
lean_dec(v_a_771_);
if (v___x_772_ == 0)
{
v_name_700_ = v___x_768_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
goto v___jp_699_;
}
else
{
lean_object* v___x_773_; 
lean_dec(v___x_768_);
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_700_ = v___x_773_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
v___y_705_ = v_a_564_;
v___y_706_ = v_a_565_;
v___y_707_ = v_a_566_;
v___y_708_ = v_a_567_;
v___y_709_ = v_a_568_;
v___y_710_ = v_a_569_;
goto v___jp_699_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v___x_768_);
lean_dec_ref(v_type_559_);
v_a_774_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_770_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_770_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
v___jp_730_:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Meta_isProp(v_type_559_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_742_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_742_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
uint8_t v___x_736_; 
v___x_736_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v_name_558_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_name_558_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_734_);
lean_dec(v_name_558_);
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_741_ = l_Lean_Core_mkFreshUserName(v___x_740_, v_a_568_, v_a_569_);
return v___x_741_;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_name_558_);
v_a_743_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_731_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_731_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_type_559_);
lean_dec(v_name_558_);
v_a_787_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_725_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_725_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
v___jp_571_:
{
lean_object* v___x_574_; lean_object* v_toGoalState_575_; lean_object* v_clean_576_; lean_object* v_mvarId_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_622_; 
v___x_574_ = lean_st_ref_take(v___y_573_);
v_toGoalState_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_toGoalState_575_);
v_clean_576_ = lean_ctor_get(v_toGoalState_575_, 15);
lean_inc_ref(v_clean_576_);
v_mvarId_577_ = lean_ctor_get(v___x_574_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_574_, 0);
lean_dec(v_unused_623_);
v___x_579_ = v___x_574_;
v_isShared_580_ = v_isSharedCheck_622_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_mvarId_577_);
lean_dec(v___x_574_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_622_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_nextDeclIdx_581_; lean_object* v_enodeMap_582_; lean_object* v_exprs_583_; lean_object* v_parents_584_; lean_object* v_congrTable_585_; lean_object* v_appMap_586_; lean_object* v_indicesFound_587_; lean_object* v_newFacts_588_; uint8_t v_inconsistent_589_; lean_object* v_nextIdx_590_; lean_object* v_newRawFacts_591_; lean_object* v_facts_592_; lean_object* v_extThms_593_; lean_object* v_ematch_594_; lean_object* v_inj_595_; lean_object* v_split_596_; lean_object* v_sstates_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_620_; 
v_nextDeclIdx_581_ = lean_ctor_get(v_toGoalState_575_, 0);
v_enodeMap_582_ = lean_ctor_get(v_toGoalState_575_, 1);
v_exprs_583_ = lean_ctor_get(v_toGoalState_575_, 2);
v_parents_584_ = lean_ctor_get(v_toGoalState_575_, 3);
v_congrTable_585_ = lean_ctor_get(v_toGoalState_575_, 4);
v_appMap_586_ = lean_ctor_get(v_toGoalState_575_, 5);
v_indicesFound_587_ = lean_ctor_get(v_toGoalState_575_, 6);
v_newFacts_588_ = lean_ctor_get(v_toGoalState_575_, 7);
v_inconsistent_589_ = lean_ctor_get_uint8(v_toGoalState_575_, sizeof(void*)*17);
v_nextIdx_590_ = lean_ctor_get(v_toGoalState_575_, 8);
v_newRawFacts_591_ = lean_ctor_get(v_toGoalState_575_, 9);
v_facts_592_ = lean_ctor_get(v_toGoalState_575_, 10);
v_extThms_593_ = lean_ctor_get(v_toGoalState_575_, 11);
v_ematch_594_ = lean_ctor_get(v_toGoalState_575_, 12);
v_inj_595_ = lean_ctor_get(v_toGoalState_575_, 13);
v_split_596_ = lean_ctor_get(v_toGoalState_575_, 14);
v_sstates_597_ = lean_ctor_get(v_toGoalState_575_, 16);
v_isSharedCheck_620_ = !lean_is_exclusive(v_toGoalState_575_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_toGoalState_575_, 15);
lean_dec(v_unused_621_);
v___x_599_ = v_toGoalState_575_;
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_sstates_597_);
lean_inc(v_split_596_);
lean_inc(v_inj_595_);
lean_inc(v_ematch_594_);
lean_inc(v_extThms_593_);
lean_inc(v_facts_592_);
lean_inc(v_newRawFacts_591_);
lean_inc(v_nextIdx_590_);
lean_inc(v_newFacts_588_);
lean_inc(v_indicesFound_587_);
lean_inc(v_appMap_586_);
lean_inc(v_congrTable_585_);
lean_inc(v_parents_584_);
lean_inc(v_exprs_583_);
lean_inc(v_enodeMap_582_);
lean_inc(v_nextDeclIdx_581_);
lean_dec(v_toGoalState_575_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_used_601_; lean_object* v_next_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_619_; 
v_used_601_ = lean_ctor_get(v_clean_576_, 0);
v_next_602_ = lean_ctor_get(v_clean_576_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_clean_576_);
if (v_isSharedCheck_619_ == 0)
{
v___x_604_ = v_clean_576_;
v_isShared_605_ = v_isSharedCheck_619_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_next_602_);
lean_inc(v_used_601_);
lean_dec(v_clean_576_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_619_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_box(0);
lean_inc(v_name_572_);
v___x_607_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_601_, v_name_572_, v___x_606_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_607_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_next_602_);
v___x_609_ = v_reuseFailAlloc_618_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 15, v___x_609_);
v___x_611_ = v___x_599_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_nextDeclIdx_581_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_enodeMap_582_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_exprs_583_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_parents_584_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_congrTable_585_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_appMap_586_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_indicesFound_587_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_newFacts_588_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_nextIdx_590_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_newRawFacts_591_);
lean_ctor_set(v_reuseFailAlloc_617_, 10, v_facts_592_);
lean_ctor_set(v_reuseFailAlloc_617_, 11, v_extThms_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 12, v_ematch_594_);
lean_ctor_set(v_reuseFailAlloc_617_, 13, v_inj_595_);
lean_ctor_set(v_reuseFailAlloc_617_, 14, v_split_596_);
lean_ctor_set(v_reuseFailAlloc_617_, 15, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 16, v_sstates_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_617_, sizeof(void*)*17, v_inconsistent_589_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_611_);
v___x_613_ = v___x_579_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_mvarId_577_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_st_ref_set(v___y_573_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_name_572_);
return v___x_615_;
}
}
}
}
}
}
}
v___jp_624_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___y_630_);
lean_ctor_set(v___x_638_, 1, v___y_637_);
lean_inc(v___y_629_);
v___x_639_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_629_, v___x_638_, v___y_632_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v_toGoalState_642_; lean_object* v_clean_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v_mvarId_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_689_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_st_ref_take(v___y_632_);
v_toGoalState_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_ref(v_toGoalState_642_);
v_clean_643_ = lean_ctor_get(v_toGoalState_642_, 15);
lean_inc_ref(v_clean_643_);
v_fst_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_a_640_, 1);
lean_inc(v_snd_645_);
lean_dec(v_a_640_);
v_mvarId_646_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_690_);
v___x_648_ = v___x_641_;
v_isShared_649_ = v_isSharedCheck_689_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_mvarId_646_);
lean_dec(v___x_641_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_689_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_nextDeclIdx_650_; lean_object* v_enodeMap_651_; lean_object* v_exprs_652_; lean_object* v_parents_653_; lean_object* v_congrTable_654_; lean_object* v_appMap_655_; lean_object* v_indicesFound_656_; lean_object* v_newFacts_657_; uint8_t v_inconsistent_658_; lean_object* v_nextIdx_659_; lean_object* v_newRawFacts_660_; lean_object* v_facts_661_; lean_object* v_extThms_662_; lean_object* v_ematch_663_; lean_object* v_inj_664_; lean_object* v_split_665_; lean_object* v_sstates_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_687_; 
v_nextDeclIdx_650_ = lean_ctor_get(v_toGoalState_642_, 0);
v_enodeMap_651_ = lean_ctor_get(v_toGoalState_642_, 1);
v_exprs_652_ = lean_ctor_get(v_toGoalState_642_, 2);
v_parents_653_ = lean_ctor_get(v_toGoalState_642_, 3);
v_congrTable_654_ = lean_ctor_get(v_toGoalState_642_, 4);
v_appMap_655_ = lean_ctor_get(v_toGoalState_642_, 5);
v_indicesFound_656_ = lean_ctor_get(v_toGoalState_642_, 6);
v_newFacts_657_ = lean_ctor_get(v_toGoalState_642_, 7);
v_inconsistent_658_ = lean_ctor_get_uint8(v_toGoalState_642_, sizeof(void*)*17);
v_nextIdx_659_ = lean_ctor_get(v_toGoalState_642_, 8);
v_newRawFacts_660_ = lean_ctor_get(v_toGoalState_642_, 9);
v_facts_661_ = lean_ctor_get(v_toGoalState_642_, 10);
v_extThms_662_ = lean_ctor_get(v_toGoalState_642_, 11);
v_ematch_663_ = lean_ctor_get(v_toGoalState_642_, 12);
v_inj_664_ = lean_ctor_get(v_toGoalState_642_, 13);
v_split_665_ = lean_ctor_get(v_toGoalState_642_, 14);
v_sstates_666_ = lean_ctor_get(v_toGoalState_642_, 16);
v_isSharedCheck_687_ = !lean_is_exclusive(v_toGoalState_642_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_toGoalState_642_, 15);
lean_dec(v_unused_688_);
v___x_668_ = v_toGoalState_642_;
v_isShared_669_ = v_isSharedCheck_687_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_sstates_666_);
lean_inc(v_split_665_);
lean_inc(v_inj_664_);
lean_inc(v_ematch_663_);
lean_inc(v_extThms_662_);
lean_inc(v_facts_661_);
lean_inc(v_newRawFacts_660_);
lean_inc(v_nextIdx_659_);
lean_inc(v_newFacts_657_);
lean_inc(v_indicesFound_656_);
lean_inc(v_appMap_655_);
lean_inc(v_congrTable_654_);
lean_inc(v_parents_653_);
lean_inc(v_exprs_652_);
lean_inc(v_enodeMap_651_);
lean_inc(v_nextDeclIdx_650_);
lean_dec(v_toGoalState_642_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_687_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_used_670_; lean_object* v_next_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_686_; 
v_used_670_ = lean_ctor_get(v_clean_643_, 0);
v_next_671_ = lean_ctor_get(v_clean_643_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_clean_643_);
if (v_isSharedCheck_686_ == 0)
{
v___x_673_ = v_clean_643_;
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_next_671_);
lean_inc(v_used_670_);
lean_dec(v_clean_643_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_671_, v___y_629_, v_snd_645_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_used_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_685_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 15, v___x_677_);
v___x_679_ = v___x_668_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_nextDeclIdx_650_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_enodeMap_651_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_exprs_652_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_parents_653_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_congrTable_654_);
lean_ctor_set(v_reuseFailAlloc_684_, 5, v_appMap_655_);
lean_ctor_set(v_reuseFailAlloc_684_, 6, v_indicesFound_656_);
lean_ctor_set(v_reuseFailAlloc_684_, 7, v_newFacts_657_);
lean_ctor_set(v_reuseFailAlloc_684_, 8, v_nextIdx_659_);
lean_ctor_set(v_reuseFailAlloc_684_, 9, v_newRawFacts_660_);
lean_ctor_set(v_reuseFailAlloc_684_, 10, v_facts_661_);
lean_ctor_set(v_reuseFailAlloc_684_, 11, v_extThms_662_);
lean_ctor_set(v_reuseFailAlloc_684_, 12, v_ematch_663_);
lean_ctor_set(v_reuseFailAlloc_684_, 13, v_inj_664_);
lean_ctor_set(v_reuseFailAlloc_684_, 14, v_split_665_);
lean_ctor_set(v_reuseFailAlloc_684_, 15, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_684_, 16, v_sstates_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_684_, sizeof(void*)*17, v_inconsistent_658_);
v___x_679_ = v_reuseFailAlloc_684_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_679_);
v___x_681_ = v___x_648_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_mvarId_646_);
v___x_681_ = v_reuseFailAlloc_683_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_st_ref_set(v___y_632_, v___x_681_);
v_name_572_ = v_fst_644_;
v___y_573_ = v___y_632_;
goto v___jp_571_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v___y_629_);
v_a_691_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_639_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_639_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
v___jp_699_:
{
lean_object* v___x_711_; lean_object* v_toGoalState_712_; lean_object* v_clean_713_; lean_object* v_used_714_; uint8_t v___x_715_; 
v___x_711_ = lean_st_ref_get(v___y_701_);
v_toGoalState_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_toGoalState_712_);
lean_dec(v___x_711_);
v_clean_713_ = lean_ctor_get(v_toGoalState_712_, 15);
lean_inc_ref(v_clean_713_);
lean_dec_ref(v_toGoalState_712_);
v_used_714_ = lean_ctor_get(v_clean_713_, 0);
lean_inc_ref(v_used_714_);
lean_dec_ref(v_clean_713_);
v___x_715_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_714_, v_name_700_);
lean_dec_ref(v_used_714_);
if (v___x_715_ == 0)
{
lean_dec_ref(v_type_559_);
v_name_572_ = v_name_700_;
v___y_573_ = v___y_701_;
goto v___jp_571_;
}
else
{
lean_object* v___x_716_; 
lean_inc(v_name_700_);
v___x_716_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_700_, v_type_559_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v_toGoalState_719_; lean_object* v_clean_720_; lean_object* v_next_721_; lean_object* v___x_722_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_st_ref_get(v___y_701_);
v_toGoalState_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_toGoalState_719_);
lean_dec(v___x_718_);
v_clean_720_ = lean_ctor_get(v_toGoalState_719_, 15);
lean_inc_ref(v_clean_720_);
lean_dec_ref(v_toGoalState_719_);
v_next_721_ = lean_ctor_get(v_clean_720_, 1);
lean_inc_ref(v_next_721_);
lean_dec_ref(v_clean_720_);
v___x_722_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_721_, v_a_717_);
lean_dec_ref(v_next_721_);
if (lean_obj_tag(v___x_722_) == 1)
{
lean_object* v_val_723_; 
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v___x_722_, 1);
v___y_625_ = v___y_710_;
v___y_626_ = v___y_705_;
v___y_627_ = v___y_704_;
v___y_628_ = v___y_707_;
v___y_629_ = v_a_717_;
v___y_630_ = v_name_700_;
v___y_631_ = v___y_708_;
v___y_632_ = v___y_701_;
v___y_633_ = v___y_702_;
v___y_634_ = v___y_709_;
v___y_635_ = v___y_706_;
v___y_636_ = v___y_703_;
v___y_637_ = v_val_723_;
goto v___jp_624_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v___x_722_);
v___x_724_ = lean_unsigned_to_nat(1u);
v___y_625_ = v___y_710_;
v___y_626_ = v___y_705_;
v___y_627_ = v___y_704_;
v___y_628_ = v___y_707_;
v___y_629_ = v_a_717_;
v___y_630_ = v_name_700_;
v___y_631_ = v___y_708_;
v___y_632_ = v___y_701_;
v___y_633_ = v___y_702_;
v___y_634_ = v___y_709_;
v___y_635_ = v___y_706_;
v___y_636_ = v___y_703_;
v___y_637_ = v___x_724_;
goto v___jp_624_;
}
}
else
{
lean_dec(v_name_700_);
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_795_, lean_object* v_type_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_795_, v_type_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec(v_a_797_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_810_, v_x_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_815_, v_x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_818_, v_x_819_, v_x_820_);
lean_dec(v_x_820_);
lean_dec_ref(v_x_819_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_823_, lean_object* v_inst_824_, lean_object* v_a_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_823_, v_a_825_, v___y_826_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_838_, lean_object* v_inst_839_, lean_object* v_a_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_838_, v_inst_839_, v_a_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec(v___y_841_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_857_, v_x_858_, v_x_859_);
lean_dec(v_x_859_);
lean_dec_ref(v_x_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, size_t v_x_863_, size_t v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_862_, v_x_863_, v_x_864_, v_x_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
size_t v_x_40795__boxed_874_; size_t v_x_40796__boxed_875_; lean_object* v_res_876_; 
v_x_40795__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_x_40796__boxed_875_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_res_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_868_, v_x_869_, v_x_40795__boxed_874_, v_x_40796__boxed_875_, v_x_872_, v_x_873_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, size_t v_x_879_, lean_object* v_x_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_878_, v_x_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
size_t v_x_40812__boxed_886_; uint8_t v_res_887_; lean_object* v_r_888_; 
v_x_40812__boxed_886_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_887_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_882_, v_x_883_, v_x_40812__boxed_886_, v_x_885_);
lean_dec(v_x_885_);
lean_dec_ref(v_x_883_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_889_, lean_object* v_x_890_, size_t v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_890_, v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
size_t v_x_40823__boxed_898_; lean_object* v_res_899_; 
v_x_40823__boxed_898_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_res_899_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_894_, v_x_895_, v_x_40823__boxed_898_, v_x_897_);
lean_dec(v_x_897_);
lean_dec_ref(v_x_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_900_, lean_object* v_n_901_, lean_object* v_k_902_, lean_object* v_v_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_901_, v_k_902_, v_v_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_905_, size_t v_depth_906_, lean_object* v_keys_907_, lean_object* v_vals_908_, lean_object* v_heq_909_, lean_object* v_i_910_, lean_object* v_entries_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_906_, v_keys_907_, v_vals_908_, v_i_910_, v_entries_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_913_, lean_object* v_depth_914_, lean_object* v_keys_915_, lean_object* v_vals_916_, lean_object* v_heq_917_, lean_object* v_i_918_, lean_object* v_entries_919_){
_start:
{
size_t v_depth_boxed_920_; lean_object* v_res_921_; 
v_depth_boxed_920_ = lean_unbox_usize(v_depth_914_);
lean_dec(v_depth_914_);
v_res_921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_913_, v_depth_boxed_920_, v_keys_915_, v_vals_916_, v_heq_917_, v_i_918_, v_entries_919_);
lean_dec_ref(v_vals_916_);
lean_dec_ref(v_keys_915_);
return v_res_921_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_k_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_923_, v_i_926_, v_k_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_929_, lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_heq_932_, lean_object* v_i_933_, lean_object* v_k_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_929_, v_keys_930_, v_vals_931_, v_heq_932_, v_i_933_, v_k_934_);
lean_dec(v_k_934_);
lean_dec_ref(v_vals_931_);
lean_dec_ref(v_keys_930_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_k_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_938_, v_vals_939_, v_i_941_, v_k_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_944_, lean_object* v_keys_945_, lean_object* v_vals_946_, lean_object* v_heq_947_, lean_object* v_i_948_, lean_object* v_k_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_944_, v_keys_945_, v_vals_946_, v_heq_947_, v_i_948_, v_k_949_);
lean_dec(v_k_949_);
lean_dec_ref(v_vals_946_);
lean_dec_ref(v_keys_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_952_, v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v_env_964_; lean_object* v___x_965_; lean_object* v_mctx_966_; lean_object* v_lctx_967_; lean_object* v_options_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_963_ = lean_st_ref_get(v___y_961_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = lean_st_ref_get(v___y_959_);
v_mctx_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_mctx_966_);
lean_dec(v___x_965_);
v_lctx_967_ = lean_ctor_get(v___y_958_, 2);
v_options_968_ = lean_ctor_get(v___y_960_, 2);
lean_inc_ref(v_options_968_);
lean_inc_ref(v_lctx_967_);
v___x_969_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_969_, 0, v_env_964_);
lean_ctor_set(v___x_969_, 1, v_mctx_966_);
lean_ctor_set(v___x_969_, 2, v_lctx_967_);
lean_ctor_set(v___x_969_, 3, v_options_968_);
v___x_970_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v_msgData_957_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_ref_985_; lean_object* v___x_986_; lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_ref_985_ = lean_ctor_get(v___y_982_, 5);
v___x_986_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_inc(v_ref_985_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_ref_985_);
lean_ctor_set(v___x_991_, 1, v_a_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 1);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___x_1072_; lean_object* v_mvarId_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_st_ref_get(v_a_1006_);
v_mvarId_1073_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_mvarId_1073_);
lean_dec(v___x_1072_);
v___x_1074_ = l_Lean_MVarId_getType(v_mvarId_1073_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
switch(lean_obj_tag(v_a_1075_))
{
case 7:
{
lean_object* v_binderName_1076_; lean_object* v_binderType_1077_; 
v_binderName_1076_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_binderName_1076_);
v_binderType_1077_ = lean_ctor_get(v_a_1075_, 1);
lean_inc_ref(v_binderType_1077_);
lean_dec_ref_known(v_a_1075_, 3);
v_fst_1018_ = v_binderName_1076_;
v_snd_1019_ = v_binderType_1077_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
v___y_1028_ = v_a_1014_;
v___y_1029_ = v_a_1015_;
goto v___jp_1017_;
}
case 8:
{
lean_object* v_declName_1078_; lean_object* v_type_1079_; 
v_declName_1078_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_declName_1078_);
v_type_1079_ = lean_ctor_get(v_a_1075_, 1);
lean_inc_ref(v_type_1079_);
lean_dec_ref_known(v_a_1075_, 4);
v_fst_1018_ = v_declName_1078_;
v_snd_1019_ = v_type_1079_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
v___y_1024_ = v_a_1010_;
v___y_1025_ = v_a_1011_;
v___y_1026_ = v_a_1012_;
v___y_1027_ = v_a_1013_;
v___y_1028_ = v_a_1014_;
v___y_1029_ = v_a_1015_;
goto v___jp_1017_;
}
default: 
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1075_);
v___x_1080_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1081_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1080_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1074_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1074_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
v___jp_1017_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1018_, v_snd_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v_mvarId_1033_; lean_object* v___x_1034_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_st_ref_get(v___y_1020_);
v_mvarId_1033_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_mvarId_1033_);
lean_dec(v___x_1032_);
v___x_1034_ = l_Lean_MVarId_intro(v_mvarId_1033_, v_a_1031_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1055_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1055_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1055_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v_toGoalState_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1053_; 
v_fst_1039_ = lean_ctor_get(v_a_1035_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v_a_1035_, 1);
lean_inc(v_snd_1040_);
lean_dec(v_a_1035_);
v___x_1041_ = lean_st_ref_take(v___y_1020_);
v_toGoalState_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1041_, 1);
lean_dec(v_unused_1054_);
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_toGoalState_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v_snd_1040_);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_toGoalState_1042_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_snd_1040_);
v___x_1047_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_st_ref_set(v___y_1020_, v___x_1047_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_fst_1039_);
v___x_1050_ = v___x_1037_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fst_1039_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1034_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1034_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1030_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1030_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec(v_a_1098_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1110_, lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1111_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1124_, v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec(v___y_1126_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc(v___y_1139_);
v___x_1150_ = lean_apply_11(v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, lean_box(0));
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; 
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc(v___y_1166_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1177_, 0, v_x_1165_);
lean_closure_set(v___f_1177_, 1, v___y_1166_);
lean_closure_set(v___f_1177_, 2, v___y_1167_);
lean_closure_set(v___f_1177_, 3, v___y_1168_);
lean_closure_set(v___f_1177_, 4, v___y_1169_);
lean_closure_set(v___f_1177_, 5, v___y_1170_);
lean_closure_set(v___f_1177_, 6, v___y_1171_);
v___x_1178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1164_, v___f_1177_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1178_) == 0)
{
return v___x_1178_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1201_, lean_object* v_mvarId_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1202_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_mvarId_1217_, lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1216_, v_mvarId_1217_, v_x_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
v___x_1242_ = lean_apply_10(v_x_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, lean_box(0));
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1255_, lean_object* v_x_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
lean_inc(v___y_1261_);
lean_inc_ref(v___y_1260_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1267_, 0, v_x_1256_);
lean_closure_set(v___f_1267_, 1, v___y_1257_);
lean_closure_set(v___f_1267_, 2, v___y_1258_);
lean_closure_set(v___f_1267_, 3, v___y_1259_);
lean_closure_set(v___f_1267_, 4, v___y_1260_);
lean_closure_set(v___f_1267_, 5, v___y_1261_);
v___x_1268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1255_, v___f_1267_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
return v___x_1268_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1277_, v_x_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1290_, lean_object* v_mvarId_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_mvarId_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1304_, v_mvarId_1305_, v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1318_, lean_object* v_generation_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
lean_inc(v_a_1318_);
v___x_1331_ = l_Lean_FVarId_getDecl___redArg(v_a_1318_, v___y_1326_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1333_ = l_Lean_LocalDecl_type(v_a_1332_);
lean_dec(v_a_1332_);
lean_inc_ref(v___x_1333_);
v___x_1334_ = l_Lean_Meta_isProp(v___x_1333_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; uint8_t v___x_1336_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1336_ = lean_unbox(v_a_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v___x_1333_);
lean_inc(v_a_1318_);
v___x_1337_ = l_Lean_FVarId_getDecl___redArg(v_a_1318_, v___y_1326_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1339_ = lean_unbox(v_a_1335_);
lean_dec(v_a_1335_);
v___x_1340_ = l_Lean_LocalDecl_value(v_a_1338_, v___x_1339_);
lean_dec(v_a_1338_);
v___x_1341_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1340_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
lean_inc(v_a_1318_);
v___x_1343_ = l_Lean_mkFVar(v_a_1318_);
v___x_1344_ = l_Lean_Meta_Sym_shareCommon(v___x_1343_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
lean_inc(v_a_1342_);
v___x_1346_ = l_Lean_Meta_Simp_Result_getProof(v_a_1342_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_expr_1348_; lean_object* v___x_1349_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_expr_1348_ = lean_ctor_get(v_a_1342_, 0);
lean_inc_ref(v_expr_1348_);
lean_dec(v_a_1342_);
v___x_1349_ = l_Lean_Meta_Grind_addNewEq(v_a_1345_, v_expr_1348_, v_a_1347_, v_generation_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1358_; 
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1359_);
v___x_1351_ = v___x_1349_;
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v___x_1349_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1358_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = lean_st_ref_get(v___y_1320_);
v___x_1354_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_a_1318_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1354_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1318_);
v_a_1360_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1349_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1349_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1345_);
lean_dec(v_a_1342_);
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1368_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1346_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1346_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_a_1342_);
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1376_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1344_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1344_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1384_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1341_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1341_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_a_1335_);
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1392_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1337_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1337_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_a_1335_);
lean_dec(v_generation_1319_);
v___x_1400_ = lean_st_ref_get(v___y_1320_);
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1333_);
v___x_1402_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1401_, v___x_1333_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_mvarId_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v_mvarId_1404_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_mvarId_1404_);
lean_dec(v___x_1400_);
v___x_1405_ = l_Lean_mkFVar(v_a_1318_);
v___x_1406_ = l_Lean_MVarId_assert(v_mvarId_1404_, v_a_1403_, v___x_1333_, v___x_1405_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1425_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1425_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1425_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v_toGoalState_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1423_; 
v___x_1411_ = lean_st_ref_get(v___y_1320_);
v_toGoalState_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1411_, 1);
lean_dec(v_unused_1424_);
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_toGoalState_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_a_1407_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_toGoalState_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1407_);
v___x_1417_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1418_);
v___x_1420_ = v___x_1409_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1406_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1406_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v___x_1400_);
lean_dec_ref(v___x_1333_);
lean_dec(v_a_1318_);
v_a_1434_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1402_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1402_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v___x_1333_);
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1442_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1334_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1334_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_generation_1319_);
lean_dec(v_a_1318_);
v_a_1450_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1331_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1331_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1458_, lean_object* v_generation_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1458_, v_generation_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v___y_1460_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v_ks_1476_; lean_object* v_vs_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1501_; 
v_ks_1476_ = lean_ctor_get(v_x_1472_, 0);
v_vs_1477_ = lean_ctor_get(v_x_1472_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1472_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1479_ = v_x_1472_;
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_vs_1477_);
lean_inc(v_ks_1476_);
lean_dec(v_x_1472_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1501_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_array_get_size(v_ks_1476_);
v___x_1482_ = lean_nat_dec_lt(v_x_1473_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_dec(v_x_1473_);
v___x_1483_ = lean_array_push(v_ks_1476_, v_x_1474_);
v___x_1484_ = lean_array_push(v_vs_1477_, v_x_1475_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v___x_1484_);
lean_ctor_set(v___x_1479_, 0, v___x_1483_);
v___x_1486_ = v___x_1479_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
else
{
lean_object* v_k_x27_1488_; uint8_t v___x_1489_; 
v_k_x27_1488_ = lean_array_fget_borrowed(v_ks_1476_, v_x_1473_);
v___x_1489_ = l_Lean_instBEqMVarId_beq(v_x_1474_, v_k_x27_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1491_; 
if (v_isShared_1480_ == 0)
{
v___x_1491_ = v___x_1479_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_ks_1476_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_vs_1477_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_unsigned_to_nat(1u);
v___x_1493_ = lean_nat_add(v_x_1473_, v___x_1492_);
lean_dec(v_x_1473_);
v_x_1472_ = v___x_1491_;
v_x_1473_ = v___x_1493_;
goto _start;
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1496_ = lean_array_fset(v_ks_1476_, v_x_1473_, v_x_1474_);
v___x_1497_ = lean_array_fset(v_vs_1477_, v_x_1473_, v_x_1475_);
lean_dec(v_x_1473_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v___x_1497_);
lean_ctor_set(v___x_1479_, 0, v___x_1496_);
v___x_1499_ = v___x_1479_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1502_, lean_object* v_k_1503_, lean_object* v_v_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1502_, v___x_1505_, v_k_1503_, v_v_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1507_, size_t v_x_1508_, size_t v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_es_1512_; size_t v___x_1513_; size_t v___x_1514_; lean_object* v_j_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_es_1512_ = lean_ctor_get(v_x_1507_, 0);
v___x_1513_ = ((size_t)31ULL);
v___x_1514_ = lean_usize_land(v_x_1508_, v___x_1513_);
v_j_1515_ = lean_usize_to_nat(v___x_1514_);
v___x_1516_ = lean_array_get_size(v_es_1512_);
v___x_1517_ = lean_nat_dec_lt(v_j_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v_j_1515_);
lean_dec(v_x_1511_);
lean_dec(v_x_1510_);
return v_x_1507_;
}
else
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1556_; 
lean_inc_ref(v_es_1512_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_x_1507_, 0);
lean_dec(v_unused_1557_);
v___x_1519_ = v_x_1507_;
v_isShared_1520_ = v_isSharedCheck_1556_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_x_1507_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1556_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_v_1521_; lean_object* v___x_1522_; lean_object* v_xs_x27_1523_; lean_object* v___y_1525_; 
v_v_1521_ = lean_array_fget(v_es_1512_, v_j_1515_);
v___x_1522_ = lean_box(0);
v_xs_x27_1523_ = lean_array_fset(v_es_1512_, v_j_1515_, v___x_1522_);
switch(lean_obj_tag(v_v_1521_))
{
case 0:
{
lean_object* v_key_1530_; lean_object* v_val_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1541_; 
v_key_1530_ = lean_ctor_get(v_v_1521_, 0);
v_val_1531_ = lean_ctor_get(v_v_1521_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_v_1521_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1533_ = v_v_1521_;
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_val_1531_);
lean_inc(v_key_1530_);
lean_dec(v_v_1521_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1541_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Lean_instBEqMVarId_beq(v_x_1510_, v_key_1530_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_del_object(v___x_1533_);
v___x_1536_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1530_, v_val_1531_, v_x_1510_, v_x_1511_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
v___y_1525_ = v___x_1537_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_val_1531_);
lean_dec(v_key_1530_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_x_1511_);
lean_ctor_set(v___x_1533_, 0, v_x_1510_);
v___x_1539_ = v___x_1533_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_x_1510_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_x_1511_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v___y_1525_ = v___x_1539_;
goto v___jp_1524_;
}
}
}
}
case 1:
{
lean_object* v_node_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1554_; 
v_node_1542_ = lean_ctor_get(v_v_1521_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_v_1521_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1544_ = v_v_1521_;
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_node_1542_);
lean_dec(v_v_1521_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1546_ = ((size_t)5ULL);
v___x_1547_ = lean_usize_shift_right(v_x_1508_, v___x_1546_);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_add(v_x_1509_, v___x_1548_);
v___x_1550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1542_, v___x_1547_, v___x_1549_, v_x_1510_, v_x_1511_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1550_);
v___x_1552_ = v___x_1544_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
v___y_1525_ = v___x_1552_;
goto v___jp_1524_;
}
}
}
default: 
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_x_1510_);
lean_ctor_set(v___x_1555_, 1, v_x_1511_);
v___y_1525_ = v___x_1555_;
goto v___jp_1524_;
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_array_fset(v_xs_x27_1523_, v_j_1515_, v___y_1525_);
lean_dec(v_j_1515_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1526_);
v___x_1528_ = v___x_1519_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
lean_object* v_ks_1558_; lean_object* v_vs_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1579_; 
v_ks_1558_ = lean_ctor_get(v_x_1507_, 0);
v_vs_1559_ = lean_ctor_get(v_x_1507_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1507_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1561_ = v_x_1507_;
v_isShared_1562_ = v_isSharedCheck_1579_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_vs_1559_);
lean_inc(v_ks_1558_);
lean_dec(v_x_1507_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1579_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_ks_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_vs_1559_);
v___x_1564_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v_newNode_1565_; uint8_t v___y_1567_; size_t v___x_1573_; uint8_t v___x_1574_; 
v_newNode_1565_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1564_, v_x_1510_, v_x_1511_);
v___x_1573_ = ((size_t)7ULL);
v___x_1574_ = lean_usize_dec_le(v___x_1573_, v_x_1509_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1565_);
v___x_1576_ = lean_unsigned_to_nat(4u);
v___x_1577_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
lean_dec(v___x_1575_);
v___y_1567_ = v___x_1577_;
goto v___jp_1566_;
}
else
{
v___y_1567_ = v___x_1574_;
goto v___jp_1566_;
}
v___jp_1566_:
{
if (v___y_1567_ == 0)
{
lean_object* v_ks_1568_; lean_object* v_vs_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_ks_1568_ = lean_ctor_get(v_newNode_1565_, 0);
lean_inc_ref(v_ks_1568_);
v_vs_1569_ = lean_ctor_get(v_newNode_1565_, 1);
lean_inc_ref(v_vs_1569_);
lean_dec_ref(v_newNode_1565_);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1572_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1509_, v_ks_1568_, v_vs_1569_, v___x_1570_, v___x_1571_);
lean_dec_ref(v_vs_1569_);
lean_dec_ref(v_ks_1568_);
return v___x_1572_;
}
else
{
return v_newNode_1565_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1580_, lean_object* v_keys_1581_, lean_object* v_vals_1582_, lean_object* v_i_1583_, lean_object* v_entries_1584_){
_start:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_array_get_size(v_keys_1581_);
v___x_1586_ = lean_nat_dec_lt(v_i_1583_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec(v_i_1583_);
return v_entries_1584_;
}
else
{
lean_object* v_k_1587_; lean_object* v_v_1588_; uint64_t v___x_1589_; size_t v_h_1590_; size_t v___x_1591_; lean_object* v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; size_t v_h_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_k_1587_ = lean_array_fget_borrowed(v_keys_1581_, v_i_1583_);
v_v_1588_ = lean_array_fget_borrowed(v_vals_1582_, v_i_1583_);
v___x_1589_ = l_Lean_instHashableMVarId_hash(v_k_1587_);
v_h_1590_ = lean_uint64_to_usize(v___x_1589_);
v___x_1591_ = ((size_t)5ULL);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_sub(v_depth_1580_, v___x_1593_);
v___x_1595_ = lean_usize_mul(v___x_1591_, v___x_1594_);
v_h_1596_ = lean_usize_shift_right(v_h_1590_, v___x_1595_);
v___x_1597_ = lean_nat_add(v_i_1583_, v___x_1592_);
lean_dec(v_i_1583_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
v___x_1598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1584_, v_h_1596_, v_depth_1580_, v_k_1587_, v_v_1588_);
v_i_1583_ = v___x_1597_;
v_entries_1584_ = v___x_1598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1600_, lean_object* v_keys_1601_, lean_object* v_vals_1602_, lean_object* v_i_1603_, lean_object* v_entries_1604_){
_start:
{
size_t v_depth_boxed_1605_; lean_object* v_res_1606_; 
v_depth_boxed_1605_ = lean_unbox_usize(v_depth_1600_);
lean_dec(v_depth_1600_);
v_res_1606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1605_, v_keys_1601_, v_vals_1602_, v_i_1603_, v_entries_1604_);
lean_dec_ref(v_vals_1602_);
lean_dec_ref(v_keys_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
size_t v_x_194788__boxed_1612_; size_t v_x_194789__boxed_1613_; lean_object* v_res_1614_; 
v_x_194788__boxed_1612_ = lean_unbox_usize(v_x_1608_);
lean_dec(v_x_1608_);
v_x_194789__boxed_1613_ = lean_unbox_usize(v_x_1609_);
lean_dec(v_x_1609_);
v_res_1614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1607_, v_x_194788__boxed_1612_, v_x_194789__boxed_1613_, v_x_1610_, v_x_1611_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
uint64_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = l_Lean_instHashableMVarId_hash(v_x_1616_);
v___x_1619_ = lean_uint64_to_usize(v___x_1618_);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1615_, v___x_1619_, v___x_1620_, v_x_1616_, v_x_1617_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1622_, lean_object* v_val_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v_mctx_1627_; lean_object* v_cache_1628_; lean_object* v_zetaDeltaFVarIds_1629_; lean_object* v_postponed_1630_; lean_object* v_diag_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1659_; 
v___x_1626_ = lean_st_ref_take(v___y_1624_);
v_mctx_1627_ = lean_ctor_get(v___x_1626_, 0);
v_cache_1628_ = lean_ctor_get(v___x_1626_, 1);
v_zetaDeltaFVarIds_1629_ = lean_ctor_get(v___x_1626_, 2);
v_postponed_1630_ = lean_ctor_get(v___x_1626_, 3);
v_diag_1631_ = lean_ctor_get(v___x_1626_, 4);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1633_ = v___x_1626_;
v_isShared_1634_ = v_isSharedCheck_1659_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_diag_1631_);
lean_inc(v_postponed_1630_);
lean_inc(v_zetaDeltaFVarIds_1629_);
lean_inc(v_cache_1628_);
lean_inc(v_mctx_1627_);
lean_dec(v___x_1626_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1659_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v_depth_1635_; lean_object* v_levelAssignDepth_1636_; lean_object* v_lmvarCounter_1637_; lean_object* v_mvarCounter_1638_; lean_object* v_lDecls_1639_; lean_object* v_decls_1640_; lean_object* v_userNames_1641_; lean_object* v_lAssignment_1642_; lean_object* v_eAssignment_1643_; lean_object* v_dAssignment_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1658_; 
v_depth_1635_ = lean_ctor_get(v_mctx_1627_, 0);
v_levelAssignDepth_1636_ = lean_ctor_get(v_mctx_1627_, 1);
v_lmvarCounter_1637_ = lean_ctor_get(v_mctx_1627_, 2);
v_mvarCounter_1638_ = lean_ctor_get(v_mctx_1627_, 3);
v_lDecls_1639_ = lean_ctor_get(v_mctx_1627_, 4);
v_decls_1640_ = lean_ctor_get(v_mctx_1627_, 5);
v_userNames_1641_ = lean_ctor_get(v_mctx_1627_, 6);
v_lAssignment_1642_ = lean_ctor_get(v_mctx_1627_, 7);
v_eAssignment_1643_ = lean_ctor_get(v_mctx_1627_, 8);
v_dAssignment_1644_ = lean_ctor_get(v_mctx_1627_, 9);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_mctx_1627_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1646_ = v_mctx_1627_;
v_isShared_1647_ = v_isSharedCheck_1658_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_dAssignment_1644_);
lean_inc(v_eAssignment_1643_);
lean_inc(v_lAssignment_1642_);
lean_inc(v_userNames_1641_);
lean_inc(v_decls_1640_);
lean_inc(v_lDecls_1639_);
lean_inc(v_mvarCounter_1638_);
lean_inc(v_lmvarCounter_1637_);
lean_inc(v_levelAssignDepth_1636_);
lean_inc(v_depth_1635_);
lean_dec(v_mctx_1627_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1658_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1643_, v_mvarId_1622_, v_val_1623_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 8, v___x_1648_);
v___x_1650_ = v___x_1646_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_depth_1635_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_levelAssignDepth_1636_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_lmvarCounter_1637_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_mvarCounter_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_lDecls_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v_decls_1640_);
lean_ctor_set(v_reuseFailAlloc_1657_, 6, v_userNames_1641_);
lean_ctor_set(v_reuseFailAlloc_1657_, 7, v_lAssignment_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 8, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1657_, 9, v_dAssignment_1644_);
v___x_1650_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1650_);
v___x_1652_ = v___x_1633_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_cache_1628_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_zetaDeltaFVarIds_1629_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_postponed_1630_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_diag_1631_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_st_ref_set(v___y_1624_, v___x_1652_);
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1660_, lean_object* v_val_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1660_, v_val_1661_, v___y_1662_);
lean_dec(v___y_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_ngen_1668_; lean_object* v_namePrefix_1669_; lean_object* v_idx_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1699_; 
v___x_1667_ = lean_st_ref_get(v___y_1665_);
v_ngen_1668_ = lean_ctor_get(v___x_1667_, 2);
lean_inc_ref(v_ngen_1668_);
lean_dec(v___x_1667_);
v_namePrefix_1669_ = lean_ctor_get(v_ngen_1668_, 0);
v_idx_1670_ = lean_ctor_get(v_ngen_1668_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_ngen_1668_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1672_ = v_ngen_1668_;
v_isShared_1673_ = v_isSharedCheck_1699_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_idx_1670_);
lean_inc(v_namePrefix_1669_);
lean_dec(v_ngen_1668_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1699_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_env_1675_; lean_object* v_nextMacroScope_1676_; lean_object* v_auxDeclNGen_1677_; lean_object* v_traceState_1678_; lean_object* v_cache_1679_; lean_object* v_messages_1680_; lean_object* v_infoState_1681_; lean_object* v_snapshotTasks_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1697_; 
v___x_1674_ = lean_st_ref_take(v___y_1665_);
v_env_1675_ = lean_ctor_get(v___x_1674_, 0);
v_nextMacroScope_1676_ = lean_ctor_get(v___x_1674_, 1);
v_auxDeclNGen_1677_ = lean_ctor_get(v___x_1674_, 3);
v_traceState_1678_ = lean_ctor_get(v___x_1674_, 4);
v_cache_1679_ = lean_ctor_get(v___x_1674_, 5);
v_messages_1680_ = lean_ctor_get(v___x_1674_, 6);
v_infoState_1681_ = lean_ctor_get(v___x_1674_, 7);
v_snapshotTasks_1682_ = lean_ctor_get(v___x_1674_, 8);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v___x_1674_, 2);
lean_dec(v_unused_1698_);
v___x_1684_ = v___x_1674_;
v_isShared_1685_ = v_isSharedCheck_1697_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_snapshotTasks_1682_);
lean_inc(v_infoState_1681_);
lean_inc(v_messages_1680_);
lean_inc(v_cache_1679_);
lean_inc(v_traceState_1678_);
lean_inc(v_auxDeclNGen_1677_);
lean_inc(v_nextMacroScope_1676_);
lean_inc(v_env_1675_);
lean_dec(v___x_1674_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1697_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_r_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_inc(v_idx_1670_);
lean_inc(v_namePrefix_1669_);
v_r_1686_ = l_Lean_Name_num___override(v_namePrefix_1669_, v_idx_1670_);
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_add(v_idx_1670_, v___x_1687_);
lean_dec(v_idx_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v___x_1688_);
v___x_1690_ = v___x_1672_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_namePrefix_1669_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 2, v___x_1690_);
v___x_1692_ = v___x_1684_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_env_1675_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_nextMacroScope_1676_);
lean_ctor_set(v_reuseFailAlloc_1695_, 2, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1695_, 3, v_auxDeclNGen_1677_);
lean_ctor_set(v_reuseFailAlloc_1695_, 4, v_traceState_1678_);
lean_ctor_set(v_reuseFailAlloc_1695_, 5, v_cache_1679_);
lean_ctor_set(v_reuseFailAlloc_1695_, 6, v_messages_1680_);
lean_ctor_set(v_reuseFailAlloc_1695_, 7, v_infoState_1681_);
lean_ctor_set(v_reuseFailAlloc_1695_, 8, v_snapshotTasks_1682_);
v___x_1692_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_st_ref_set(v___y_1665_, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_r_1686_);
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1700_);
lean_dec(v___y_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v___x_1714_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1712_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1740_, lean_object* v_a_1741_, uint8_t v___x_1742_, uint8_t v___x_1743_, uint8_t v___x_1744_, lean_object* v_a_1745_, lean_object* v___x_1746_, lean_object* v_expr_1747_, lean_object* v___x_1748_, lean_object* v_val_1749_, lean_object* v_mvarId_1750_, lean_object* v___x_1751_, lean_object* v_a_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_mkLambdaFVars(v___x_1740_, v_a_1741_, v___x_1742_, v___x_1743_, v___x_1742_, v___x_1743_, v___x_1744_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1767_ = lean_box(0);
v___x_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_a_1745_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = l_Lean_mkConst(v___x_1766_, v___x_1768_);
v___x_1770_ = lean_unsigned_to_nat(5u);
v___x_1771_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___x_1772_ = lean_array_push(v___x_1771_, v___x_1746_);
v___x_1773_ = lean_array_push(v___x_1772_, v_expr_1747_);
v___x_1774_ = lean_array_push(v___x_1773_, v___x_1748_);
v___x_1775_ = lean_array_push(v___x_1774_, v_val_1749_);
v___x_1776_ = lean_array_push(v___x_1775_, v_a_1765_);
v___x_1777_ = l_Lean_mkAppN(v___x_1769_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1750_, v___x_1777_, v___y_1760_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1796_; 
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1797_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v_toGoalState_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1794_; 
v___x_1782_ = lean_st_ref_get(v___y_1753_);
v_toGoalState_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1782_, 1);
lean_dec(v_unused_1795_);
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_toGoalState_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1751_);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_toGoalState_1783_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1751_);
v___x_1788_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1752_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1789_);
v___x_1791_ = v___x_1780_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
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
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1752_);
lean_dec(v___x_1751_);
v_a_1798_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1778_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1778_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1752_);
lean_dec(v___x_1751_);
lean_dec(v_mvarId_1750_);
lean_dec_ref(v_val_1749_);
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_expr_1747_);
lean_dec_ref(v___x_1746_);
lean_dec(v_a_1745_);
v_a_1806_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1764_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1764_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1814_ = _args[0];
lean_object* v_a_1815_ = _args[1];
lean_object* v___x_1816_ = _args[2];
lean_object* v___x_1817_ = _args[3];
lean_object* v___x_1818_ = _args[4];
lean_object* v_a_1819_ = _args[5];
lean_object* v___x_1820_ = _args[6];
lean_object* v_expr_1821_ = _args[7];
lean_object* v___x_1822_ = _args[8];
lean_object* v_val_1823_ = _args[9];
lean_object* v_mvarId_1824_ = _args[10];
lean_object* v___x_1825_ = _args[11];
lean_object* v_a_1826_ = _args[12];
lean_object* v___y_1827_ = _args[13];
lean_object* v___y_1828_ = _args[14];
lean_object* v___y_1829_ = _args[15];
lean_object* v___y_1830_ = _args[16];
lean_object* v___y_1831_ = _args[17];
lean_object* v___y_1832_ = _args[18];
lean_object* v___y_1833_ = _args[19];
lean_object* v___y_1834_ = _args[20];
lean_object* v___y_1835_ = _args[21];
lean_object* v___y_1836_ = _args[22];
lean_object* v___y_1837_ = _args[23];
_start:
{
uint8_t v___x_195114__boxed_1838_; uint8_t v___x_195115__boxed_1839_; uint8_t v___x_195116__boxed_1840_; lean_object* v_res_1841_; 
v___x_195114__boxed_1838_ = lean_unbox(v___x_1816_);
v___x_195115__boxed_1839_ = lean_unbox(v___x_1817_);
v___x_195116__boxed_1840_ = lean_unbox(v___x_1818_);
v_res_1841_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1814_, v_a_1815_, v___x_195114__boxed_1838_, v___x_195115__boxed_1839_, v___x_195116__boxed_1840_, v_a_1819_, v___x_1820_, v_expr_1821_, v___x_1822_, v_val_1823_, v_mvarId_1824_, v___x_1825_, v_a_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___x_1814_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1847_, lean_object* v_a_1848_, uint8_t v___x_1849_, uint8_t v___x_1850_, uint8_t v___x_1851_, lean_object* v_a_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_expr_1855_, lean_object* v___x_1856_, lean_object* v_val_1857_, lean_object* v_mvarId_1858_, lean_object* v___x_1859_, lean_object* v_a_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Meta_mkLambdaFVars(v___x_1847_, v_a_1848_, v___x_1849_, v___x_1850_, v___x_1849_, v___x_1850_, v___x_1851_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1852_);
lean_ctor_set(v___x_1875_, 1, v___x_1853_);
v___x_1876_ = l_Lean_mkConst(v___x_1874_, v___x_1875_);
v___x_1877_ = lean_unsigned_to_nat(5u);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___x_1877_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1854_);
v___x_1880_ = lean_array_push(v___x_1879_, v_expr_1855_);
v___x_1881_ = lean_array_push(v___x_1880_, v___x_1856_);
v___x_1882_ = lean_array_push(v___x_1881_, v_val_1857_);
v___x_1883_ = lean_array_push(v___x_1882_, v_a_1873_);
v___x_1884_ = l_Lean_mkAppN(v___x_1876_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1858_, v___x_1884_, v___y_1868_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1903_; 
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___x_1885_, 0);
lean_dec(v_unused_1904_);
v___x_1887_ = v___x_1885_;
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
else
{
lean_dec(v___x_1885_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v_toGoalState_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1901_; 
v___x_1889_ = lean_st_ref_get(v___y_1861_);
v_toGoalState_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v___x_1889_, 1);
lean_dec(v_unused_1902_);
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_toGoalState_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1901_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1859_);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_toGoalState_1890_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1859_);
v___x_1895_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1860_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1896_);
v___x_1898_ = v___x_1887_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_a_1860_);
lean_dec(v___x_1859_);
v_a_1905_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1885_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1885_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1860_);
lean_dec(v___x_1859_);
lean_dec(v_mvarId_1858_);
lean_dec_ref(v_val_1857_);
lean_dec_ref(v___x_1856_);
lean_dec_ref(v_expr_1855_);
lean_dec_ref(v___x_1854_);
lean_dec(v___x_1853_);
lean_dec(v_a_1852_);
v_a_1913_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1872_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1872_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1921_ = _args[0];
lean_object* v_a_1922_ = _args[1];
lean_object* v___x_1923_ = _args[2];
lean_object* v___x_1924_ = _args[3];
lean_object* v___x_1925_ = _args[4];
lean_object* v_a_1926_ = _args[5];
lean_object* v___x_1927_ = _args[6];
lean_object* v___x_1928_ = _args[7];
lean_object* v_expr_1929_ = _args[8];
lean_object* v___x_1930_ = _args[9];
lean_object* v_val_1931_ = _args[10];
lean_object* v_mvarId_1932_ = _args[11];
lean_object* v___x_1933_ = _args[12];
lean_object* v_a_1934_ = _args[13];
lean_object* v___y_1935_ = _args[14];
lean_object* v___y_1936_ = _args[15];
lean_object* v___y_1937_ = _args[16];
lean_object* v___y_1938_ = _args[17];
lean_object* v___y_1939_ = _args[18];
lean_object* v___y_1940_ = _args[19];
lean_object* v___y_1941_ = _args[20];
lean_object* v___y_1942_ = _args[21];
lean_object* v___y_1943_ = _args[22];
lean_object* v___y_1944_ = _args[23];
lean_object* v___y_1945_ = _args[24];
_start:
{
uint8_t v___x_195296__boxed_1946_; uint8_t v___x_195297__boxed_1947_; uint8_t v___x_195298__boxed_1948_; lean_object* v_res_1949_; 
v___x_195296__boxed_1946_ = lean_unbox(v___x_1923_);
v___x_195297__boxed_1947_ = lean_unbox(v___x_1924_);
v___x_195298__boxed_1948_ = lean_unbox(v___x_1925_);
v_res_1949_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1921_, v_a_1922_, v___x_195296__boxed_1946_, v___x_195297__boxed_1947_, v___x_195298__boxed_1948_, v_a_1926_, v___x_1927_, v___x_1928_, v_expr_1929_, v___x_1930_, v_val_1931_, v_mvarId_1932_, v___x_1933_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___x_1921_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1950_, lean_object* v_a_1951_, uint8_t v___x_1952_, uint8_t v___x_1953_, uint8_t v___x_1954_, lean_object* v_mvarId_1955_, lean_object* v___x_1956_, lean_object* v_a_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_mkLambdaFVars(v___x_1950_, v_a_1951_, v___x_1952_, v___x_1953_, v___x_1952_, v___x_1953_, v___x_1954_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1955_, v_a_1970_, v___y_1965_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1989_; 
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v___x_1971_, 0);
lean_dec(v_unused_1990_);
v___x_1973_ = v___x_1971_;
v_isShared_1974_ = v_isSharedCheck_1989_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v___x_1971_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1989_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v_toGoalState_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1987_; 
v___x_1975_ = lean_st_ref_get(v___y_1958_);
v_toGoalState_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1975_, 1);
lean_dec(v_unused_1988_);
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1987_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_toGoalState_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1987_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1956_);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_toGoalState_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1956_);
v___x_1981_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1957_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1982_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1956_);
v_a_1991_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1971_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1971_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1956_);
lean_dec(v_mvarId_1955_);
v_a_1999_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1969_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1969_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2007_ = _args[0];
lean_object* v_a_2008_ = _args[1];
lean_object* v___x_2009_ = _args[2];
lean_object* v___x_2010_ = _args[3];
lean_object* v___x_2011_ = _args[4];
lean_object* v_mvarId_2012_ = _args[5];
lean_object* v___x_2013_ = _args[6];
lean_object* v_a_2014_ = _args[7];
lean_object* v___y_2015_ = _args[8];
lean_object* v___y_2016_ = _args[9];
lean_object* v___y_2017_ = _args[10];
lean_object* v___y_2018_ = _args[11];
lean_object* v___y_2019_ = _args[12];
lean_object* v___y_2020_ = _args[13];
lean_object* v___y_2021_ = _args[14];
lean_object* v___y_2022_ = _args[15];
lean_object* v___y_2023_ = _args[16];
lean_object* v___y_2024_ = _args[17];
lean_object* v___y_2025_ = _args[18];
_start:
{
uint8_t v___x_195467__boxed_2026_; uint8_t v___x_195468__boxed_2027_; uint8_t v___x_195469__boxed_2028_; lean_object* v_res_2029_; 
v___x_195467__boxed_2026_ = lean_unbox(v___x_2009_);
v___x_195468__boxed_2027_ = lean_unbox(v___x_2010_);
v___x_195469__boxed_2028_ = lean_unbox(v___x_2011_);
v_res_2029_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2007_, v_a_2008_, v___x_195467__boxed_2026_, v___x_195468__boxed_2027_, v___x_195469__boxed_2028_, v_mvarId_2012_, v___x_2013_, v_a_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___x_2007_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2032_, lean_object* v___x_2033_, lean_object* v_generation_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
lean_inc(v_mvarId_2032_);
v___x_2046_ = l_Lean_MVarId_getTag(v_mvarId_2032_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2033_, v_a_2047_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_n(v_a_2049_, 2);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2032_, v_a_2049_, v___y_2042_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; lean_object* v_toGoalState_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref_known(v___x_2050_, 1);
v___x_2051_ = lean_st_ref_get(v___y_2035_);
v_toGoalState_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2051_, 1);
lean_dec(v_unused_2062_);
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2061_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_toGoalState_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2061_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Expr_mvarId_x21(v_a_2049_);
lean_dec(v_a_2049_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 1, v___x_2056_);
v___x_2058_ = v___x_2054_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_toGoalState_2052_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2058_, v_generation_2034_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2049_);
lean_dec(v_generation_2034_);
v_a_2063_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2050_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_generation_2034_);
lean_dec(v_mvarId_2032_);
v_a_2071_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2048_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2048_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_generation_2034_);
lean_dec_ref(v___x_2033_);
lean_dec(v_mvarId_2032_);
v_a_2079_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2046_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2046_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2087_, lean_object* v___x_2088_, lean_object* v_generation_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2087_, v___x_2088_, v_generation_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec(v___y_2090_);
return v_res_2101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2109_ = l_Lean_mkConst(v___x_2108_, v___x_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2110_, lean_object* v_generation_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v_a_2124_; lean_object* v___y_2129_; lean_object* v___x_2139_; lean_object* v_mvarId_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2408_; 
lean_inc_ref(v_goal_2110_);
v___x_2122_ = lean_st_mk_ref(v_goal_2110_);
v___x_2139_ = lean_st_ref_get(v___x_2122_);
v_mvarId_2140_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2139_, 0);
lean_dec(v_unused_2409_);
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2408_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_mvarId_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2408_;
goto v_resetjp_2141_;
}
v___jp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_st_ref_get(v___x_2122_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
v___jp_2128_:
{
if (lean_obj_tag(v___y_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___y_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___y_2129_, 1);
v_a_2124_ = v_a_2130_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v___x_2122_);
v_a_2131_ = lean_ctor_get(v___y_2129_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___y_2129_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___y_2129_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___y_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_MVarId_getType(v_mvarId_2140_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Expr_isForall(v_a_2145_);
v___x_2147_ = 1;
if (v___x_2146_ == 0)
{
uint8_t v___x_2148_; 
lean_del_object(v___x_2142_);
v___x_2148_ = l_Lean_Expr_isLet(v_a_2145_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec(v_a_2145_);
lean_dec_ref(v___y_2117_);
lean_dec(v_generation_2111_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_goal_2110_);
v_a_2124_ = v___x_2149_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2150_; 
lean_dec_ref(v_goal_2110_);
v___x_2150_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2113_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; uint8_t v_zetaDelta_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v_zetaDelta_2152_ = lean_ctor_get_uint8(v_a_2151_, sizeof(void*)*13 + 19);
lean_dec(v_a_2151_);
if (v_zetaDelta_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_a_2145_);
v___x_2153_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v_mvarId_2156_; lean_object* v___f_2157_; lean_object* v___x_2158_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_st_ref_get(v___x_2122_);
v_mvarId_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_mvarId_2156_);
lean_dec(v___x_2155_);
v___f_2157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2157_, 0, v_a_2154_);
lean_closure_set(v___f_2157_, 1, v_generation_2111_);
v___x_2158_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2156_, v___f_2157_, v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec_ref(v___y_2117_);
v___y_2129_ = v___x_2158_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
lean_dec(v_generation_2111_);
v_a_2159_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2153_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2153_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v_mvarId_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; 
v___x_2167_ = lean_st_ref_get(v___x_2122_);
v_mvarId_2168_ = lean_ctor_get(v___x_2167_, 1);
lean_inc_n(v_mvarId_2168_, 2);
lean_dec(v___x_2167_);
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2170_ = l_Lean_Meta_expandLet(v_a_2145_, v___x_2169_, v___x_2147_);
lean_dec(v_a_2145_);
v___f_2171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2171_, 0, v_mvarId_2168_);
lean_closure_set(v___f_2171_, 1, v___x_2170_);
lean_closure_set(v___f_2171_, 2, v_generation_2111_);
v___x_2172_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2168_, v___f_2171_, v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec_ref(v___y_2117_);
v___y_2129_ = v___x_2172_;
goto v___jp_2128_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
lean_dec(v_generation_2111_);
v_a_2173_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2150_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2150_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_generation_2111_);
lean_dec_ref(v_goal_2110_);
v___x_2181_ = l_Lean_Expr_bindingDomain_x21(v_a_2145_);
lean_inc_ref(v___x_2181_);
v___x_2182_ = l_Lean_Meta_isProp(v___x_2181_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_unbox(v_a_2183_);
lean_dec(v_a_2183_);
v___x_2185_ = lean_bool_not(v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v_mvarId_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2376_; 
lean_del_object(v___x_2142_);
v___x_2186_ = lean_st_ref_get(v___x_2122_);
v_mvarId_2187_ = lean_ctor_get(v___x_2186_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2377_);
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2376_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_mvarId_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2376_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; 
lean_inc(v_mvarId_2187_);
v___x_2191_ = l_Lean_MVarId_getTag(v_mvarId_2187_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2193_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
lean_inc_ref(v___x_2181_);
v___x_2195_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2181_, v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v_expr_2197_; lean_object* v_proof_x3f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v_expr_2197_ = lean_ctor_get(v_a_2196_, 0);
lean_inc_ref_n(v_expr_2197_, 2);
v_proof_x3f_2198_ = lean_ctor_get(v_a_2196_, 1);
lean_inc(v_proof_x3f_2198_);
lean_dec(v_a_2196_);
v___x_2199_ = l_Lean_Expr_bindingName_x21(v_a_2145_);
lean_inc(v___x_2199_);
v___x_2200_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2199_, v_expr_2197_, v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_lctx_2202_; lean_object* v_localInstances_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___x_2243_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2200_, 1);
v_lctx_2202_ = lean_ctor_get(v___y_2117_, 2);
v_localInstances_2203_ = lean_ctor_get(v___y_2117_, 3);
lean_inc_n(v_a_2194_, 2);
v___x_2204_ = l_Lean_mkFVar(v_a_2194_);
v___x_2205_ = l_Lean_Expr_bindingInfo_x21(v_a_2145_);
v___x_2206_ = 0;
lean_inc_ref_n(v_expr_2197_, 2);
lean_inc_ref(v_lctx_2202_);
v___x_2207_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2202_, v_a_2194_, v_a_2201_, v_expr_2197_, v___x_2205_, v___x_2206_);
v___x_2243_ = l_Lean_Meta_isClass_x3f(v_expr_2197_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v_localInsts_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
v___x_2245_ = l_Lean_Expr_bindingBody_x21(v_a_2145_);
if (lean_obj_tag(v_a_2244_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; 
v_val_2331_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v_a_2244_, 1);
lean_inc_ref(v___x_2204_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v___x_2204_);
lean_ctor_set(v___x_2189_, 0, v_val_2331_);
v___x_2333_ = v___x_2189_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_val_2331_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2204_);
v___x_2333_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; 
lean_inc_ref(v_localInstances_2203_);
v___x_2334_ = lean_array_push(v_localInstances_2203_, v___x_2333_);
lean_inc(v___x_2122_);
v_localInsts_2247_ = v___x_2334_;
v___y_2248_ = v___x_2122_;
v___y_2249_ = v___y_2112_;
v___y_2250_ = v___y_2113_;
v___y_2251_ = v___y_2114_;
v___y_2252_ = v___y_2115_;
v___y_2253_ = v___y_2116_;
v___y_2254_ = v___y_2117_;
v___y_2255_ = v___y_2118_;
v___y_2256_ = v___y_2119_;
v___y_2257_ = v___y_2120_;
goto v___jp_2246_;
}
}
else
{
lean_inc_ref(v_localInstances_2203_);
lean_dec(v_a_2244_);
lean_del_object(v___x_2189_);
lean_inc(v___x_2122_);
v_localInsts_2247_ = v_localInstances_2203_;
v___y_2248_ = v___x_2122_;
v___y_2249_ = v___y_2112_;
v___y_2250_ = v___y_2113_;
v___y_2251_ = v___y_2114_;
v___y_2252_ = v___y_2115_;
v___y_2253_ = v___y_2116_;
v___y_2254_ = v___y_2117_;
v___y_2255_ = v___y_2118_;
v___y_2256_ = v___y_2119_;
v___y_2257_ = v___y_2120_;
goto v___jp_2246_;
}
v___jp_2246_:
{
if (lean_obj_tag(v_proof_x3f_2198_) == 0)
{
uint8_t v___x_2258_; 
lean_dec(v___x_2199_);
lean_dec_ref(v_expr_2197_);
lean_dec_ref(v___x_2181_);
v___x_2258_ = l_Lean_Expr_isArrow(v_a_2145_);
lean_dec(v_a_2145_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_expr_instantiate1(v___x_2245_, v___x_2204_);
lean_dec_ref(v___x_2245_);
v___y_2209_ = v___y_2252_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v_localInsts_2247_;
v___y_2212_ = v___y_2251_;
v___y_2213_ = v___y_2255_;
v___y_2214_ = v___y_2257_;
v___y_2215_ = v___y_2253_;
v___y_2216_ = v___y_2248_;
v___y_2217_ = v___y_2254_;
v___y_2218_ = v___y_2249_;
v___y_2219_ = v___y_2250_;
v___y_2220_ = v___x_2259_;
goto v___jp_2208_;
}
else
{
v___y_2209_ = v___y_2252_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v_localInsts_2247_;
v___y_2212_ = v___y_2251_;
v___y_2213_ = v___y_2255_;
v___y_2214_ = v___y_2257_;
v___y_2215_ = v___y_2253_;
v___y_2216_ = v___y_2248_;
v___y_2217_ = v___y_2254_;
v___y_2218_ = v___y_2249_;
v___y_2219_ = v___y_2250_;
v___y_2220_ = v___x_2245_;
goto v___jp_2208_;
}
}
else
{
lean_object* v_val_2260_; uint8_t v___x_2261_; 
v_val_2260_ = lean_ctor_get(v_proof_x3f_2198_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v_proof_x3f_2198_, 1);
v___x_2261_ = l_Lean_Expr_isArrow(v_a_2145_);
lean_dec(v_a_2145_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_inc_ref(v___x_2245_);
lean_inc_ref_n(v___x_2181_, 2);
v___x_2262_ = l_Lean_mkLambda(v___x_2199_, v___x_2205_, v___x_2181_, v___x_2245_);
v___x_2263_ = lean_box(0);
v___x_2264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___x_2204_);
lean_inc(v_val_2260_);
lean_inc_ref(v_expr_2197_);
v___x_2265_ = l_Lean_mkApp4(v___x_2264_, v___x_2181_, v_expr_2197_, v_val_2260_, v___x_2204_);
v___x_2266_ = lean_expr_instantiate1(v___x_2245_, v___x_2265_);
lean_dec_ref(v___x_2265_);
lean_dec_ref(v___x_2245_);
lean_inc_ref(v___x_2266_);
v___x_2267_ = l_Lean_Meta_getLevel(v___x_2266_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = 2;
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2207_, v_localInsts_2247_, v___x_2266_, v___x_2269_, v_a_2192_, v___x_2270_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = l_Lean_Expr_mvarId_x21(v_a_2272_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_mk_empty_array_with_capacity(v___x_2274_);
v___x_2276_ = lean_array_push(v___x_2275_, v___x_2204_);
v___x_2277_ = 1;
v___x_2278_ = lean_box(v___x_2261_);
v___x_2279_ = lean_box(v___x_2147_);
v___x_2280_ = lean_box(v___x_2277_);
lean_inc(v___x_2273_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2281_, 0, v___x_2276_);
lean_closure_set(v___f_2281_, 1, v_a_2272_);
lean_closure_set(v___f_2281_, 2, v___x_2278_);
lean_closure_set(v___f_2281_, 3, v___x_2279_);
lean_closure_set(v___f_2281_, 4, v___x_2280_);
lean_closure_set(v___f_2281_, 5, v_a_2268_);
lean_closure_set(v___f_2281_, 6, v___x_2263_);
lean_closure_set(v___f_2281_, 7, v___x_2181_);
lean_closure_set(v___f_2281_, 8, v_expr_2197_);
lean_closure_set(v___f_2281_, 9, v___x_2262_);
lean_closure_set(v___f_2281_, 10, v_val_2260_);
lean_closure_set(v___f_2281_, 11, v_mvarId_2187_);
lean_closure_set(v___f_2281_, 12, v___x_2273_);
lean_closure_set(v___f_2281_, 13, v_a_2194_);
v___x_2282_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2273_, v___f_2281_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
v___y_2129_ = v___x_2282_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2268_);
lean_dec_ref(v___x_2262_);
lean_dec(v_val_2260_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v___x_2122_);
v_a_2283_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2271_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2271_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v___x_2266_);
lean_dec_ref(v___x_2262_);
lean_dec(v_val_2260_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
lean_dec_ref(v_localInsts_2247_);
lean_dec_ref(v___x_2207_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_a_2192_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v___x_2122_);
v_a_2291_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2267_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2267_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2299_; 
lean_dec(v___x_2199_);
lean_inc_ref(v___x_2245_);
v___x_2299_ = l_Lean_Meta_getLevel(v___x_2245_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = 2;
v___x_2302_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_2245_);
v___x_2303_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2207_, v_localInsts_2247_, v___x_2245_, v___x_2301_, v_a_2192_, v___x_2302_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___f_2313_; lean_object* v___x_2314_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_Expr_mvarId_x21(v_a_2304_);
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_mk_empty_array_with_capacity(v___x_2306_);
v___x_2308_ = lean_array_push(v___x_2307_, v___x_2204_);
v___x_2309_ = 1;
v___x_2310_ = lean_box(v___x_2185_);
v___x_2311_ = lean_box(v___x_2147_);
v___x_2312_ = lean_box(v___x_2309_);
lean_inc(v___x_2305_);
v___f_2313_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2313_, 0, v___x_2308_);
lean_closure_set(v___f_2313_, 1, v_a_2304_);
lean_closure_set(v___f_2313_, 2, v___x_2310_);
lean_closure_set(v___f_2313_, 3, v___x_2311_);
lean_closure_set(v___f_2313_, 4, v___x_2312_);
lean_closure_set(v___f_2313_, 5, v_a_2300_);
lean_closure_set(v___f_2313_, 6, v___x_2181_);
lean_closure_set(v___f_2313_, 7, v_expr_2197_);
lean_closure_set(v___f_2313_, 8, v___x_2245_);
lean_closure_set(v___f_2313_, 9, v_val_2260_);
lean_closure_set(v___f_2313_, 10, v_mvarId_2187_);
lean_closure_set(v___f_2313_, 11, v___x_2305_);
lean_closure_set(v___f_2313_, 12, v_a_2194_);
v___x_2314_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2305_, v___f_2313_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
v___y_2129_ = v___x_2314_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2300_);
lean_dec(v_val_2260_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
lean_dec_ref(v___x_2245_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v___x_2122_);
v_a_2315_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2303_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2303_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_val_2260_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2248_);
lean_dec_ref(v_localInsts_2247_);
lean_dec_ref(v___x_2245_);
lean_dec_ref(v___x_2207_);
lean_dec_ref(v___x_2204_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_a_2192_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v___x_2122_);
v_a_2323_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2299_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2299_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___x_2207_);
lean_dec_ref(v___x_2204_);
lean_dec(v___x_2199_);
lean_dec(v_proof_x3f_2198_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_a_2192_);
lean_del_object(v___x_2189_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2336_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2243_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2243_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
v___jp_2208_:
{
uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = 2;
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2207_, v___y_2211_, v___y_2220_, v___x_2221_, v_a_2192_, v___x_2222_, v___y_2217_, v___y_2213_, v___y_2210_, v___y_2214_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___f_2233_; lean_object* v___x_2234_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = l_Lean_Expr_mvarId_x21(v_a_2224_);
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_mk_empty_array_with_capacity(v___x_2226_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2204_);
v___x_2229_ = 1;
v___x_2230_ = lean_box(v___x_2185_);
v___x_2231_ = lean_box(v___x_2147_);
v___x_2232_ = lean_box(v___x_2229_);
lean_inc(v___x_2225_);
v___f_2233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2233_, 0, v___x_2228_);
lean_closure_set(v___f_2233_, 1, v_a_2224_);
lean_closure_set(v___f_2233_, 2, v___x_2230_);
lean_closure_set(v___f_2233_, 3, v___x_2231_);
lean_closure_set(v___f_2233_, 4, v___x_2232_);
lean_closure_set(v___f_2233_, 5, v_mvarId_2187_);
lean_closure_set(v___f_2233_, 6, v___x_2225_);
lean_closure_set(v___f_2233_, 7, v_a_2194_);
v___x_2234_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2225_, v___f_2233_, v___y_2216_, v___y_2218_, v___y_2219_, v___y_2212_, v___y_2209_, v___y_2215_, v___y_2217_, v___y_2213_, v___y_2210_, v___y_2214_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
v___y_2129_ = v___x_2234_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___x_2204_);
lean_dec(v_a_2194_);
lean_dec(v_mvarId_2187_);
lean_dec(v___x_2122_);
v_a_2235_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2223_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2223_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v___x_2199_);
lean_dec(v_proof_x3f_2198_);
lean_dec_ref(v_expr_2197_);
lean_dec(v_a_2194_);
lean_dec(v_a_2192_);
lean_del_object(v___x_2189_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2344_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2200_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2200_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2194_);
lean_dec(v_a_2192_);
lean_del_object(v___x_2189_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2352_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2195_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2195_);
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
lean_dec(v_a_2192_);
lean_del_object(v___x_2189_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2360_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2193_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2193_);
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
lean_del_object(v___x_2189_);
lean_dec(v_mvarId_2187_);
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2368_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2191_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2191_);
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
}
else
{
lean_object* v___x_2378_; 
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
v___x_2378_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec_ref(v___y_2117_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = lean_st_ref_get(v___x_2122_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 3);
lean_ctor_set(v___x_2142_, 1, v___x_2380_);
lean_ctor_set(v___x_2142_, 0, v_a_2379_);
v___x_2382_ = v___x_2142_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2379_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
v_a_2124_ = v___x_2382_;
goto v___jp_2123_;
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2142_);
lean_dec(v___x_2122_);
v_a_2384_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2378_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2378_);
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
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v___x_2181_);
lean_dec(v_a_2145_);
lean_del_object(v___x_2142_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
v_a_2392_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2182_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2182_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_del_object(v___x_2142_);
lean_dec(v___x_2122_);
lean_dec_ref(v___y_2117_);
lean_dec(v_generation_2111_);
lean_dec_ref(v_goal_2110_);
v_a_2400_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2144_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2144_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2410_, lean_object* v_generation_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2410_, v_generation_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2423_, lean_object* v_generation_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_mvarId_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; 
v_mvarId_2435_ = lean_ctor_get(v_goal_2423_, 1);
lean_inc(v_mvarId_2435_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2436_, 0, v_goal_2423_);
lean_closure_set(v___f_2436_, 1, v_generation_2424_);
v___x_2437_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2435_, v___f_2436_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2446_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_fst_2442_; lean_object* v___x_2444_; 
v_fst_2442_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_fst_2442_);
lean_dec(v_a_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_fst_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_fst_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2437_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2437_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2455_, lean_object* v_generation_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2455_, v_generation_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2468_, lean_object* v_val_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2468_, v_val_2469_, v___y_2477_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2482_, lean_object* v_val_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2482_, v_val_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2484_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2505_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2521_, v_x_2522_, v_x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2525_, lean_object* v_x_2526_, size_t v_x_2527_, size_t v_x_2528_, lean_object* v_x_2529_, lean_object* v_x_2530_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2526_, v_x_2527_, v_x_2528_, v_x_2529_, v_x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
size_t v_x_196445__boxed_2538_; size_t v_x_196446__boxed_2539_; lean_object* v_res_2540_; 
v_x_196445__boxed_2538_ = lean_unbox_usize(v_x_2534_);
lean_dec(v_x_2534_);
v_x_196446__boxed_2539_ = lean_unbox_usize(v_x_2535_);
lean_dec(v_x_2535_);
v_res_2540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2532_, v_x_2533_, v_x_196445__boxed_2538_, v_x_196446__boxed_2539_, v_x_2536_, v_x_2537_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2541_, lean_object* v_n_2542_, lean_object* v_k_2543_, lean_object* v_v_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2542_, v_k_2543_, v_v_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2546_, size_t v_depth_2547_, lean_object* v_keys_2548_, lean_object* v_vals_2549_, lean_object* v_heq_2550_, lean_object* v_i_2551_, lean_object* v_entries_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2547_, v_keys_2548_, v_vals_2549_, v_i_2551_, v_entries_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2554_, lean_object* v_depth_2555_, lean_object* v_keys_2556_, lean_object* v_vals_2557_, lean_object* v_heq_2558_, lean_object* v_i_2559_, lean_object* v_entries_2560_){
_start:
{
size_t v_depth_boxed_2561_; lean_object* v_res_2562_; 
v_depth_boxed_2561_ = lean_unbox_usize(v_depth_2555_);
lean_dec(v_depth_2555_);
v_res_2562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2554_, v_depth_boxed_2561_, v_keys_2556_, v_vals_2557_, v_heq_2558_, v_i_2559_, v_entries_2560_);
lean_dec_ref(v_vals_2557_);
lean_dec_ref(v_keys_2556_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2564_, v_x_2565_, v_x_2566_, v_x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Expr_getAppFn(v_type_2569_);
if (lean_obj_tag(v___x_2572_) == 4)
{
lean_object* v_declName_2573_; lean_object* v___x_2574_; 
v_declName_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_declName_2573_);
lean_dec_ref_known(v___x_2572_, 2);
v___x_2574_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2573_, v_a_2570_);
lean_dec(v_declName_2573_);
return v___x_2574_;
}
else
{
uint8_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v___x_2572_);
v___x_2575_ = 0;
v___x_2576_ = lean_box(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2578_, v_a_2579_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_type_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2582_, v_a_2584_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_type_2594_);
return v_res_2605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
lean_ctor_set(v___x_2611_, 3, v___x_2610_);
lean_ctor_set(v___x_2611_, 4, v___x_2609_);
lean_ctor_set(v___x_2611_, 5, v___x_2609_);
lean_ctor_set(v___x_2611_, 6, v___x_2609_);
lean_ctor_set(v___x_2611_, 7, v___x_2609_);
lean_ctor_set(v___x_2611_, 8, v___x_2609_);
lean_ctor_set(v___x_2611_, 9, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_unsigned_to_nat(32u);
v___x_2613_ = lean_mk_empty_array_with_capacity(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = ((size_t)5ULL);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_unsigned_to_nat(32u);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2617_);
v___x_2619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2620_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
lean_ctor_set(v___x_2620_, 2, v___x_2616_);
lean_ctor_set(v___x_2620_, 3, v___x_2616_);
lean_ctor_set_usize(v___x_2620_, 4, v___x_2615_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(1);
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2623_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
lean_ctor_set(v___x_2624_, 2, v___x_2621_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2633_ = l_Lean_stringToMessageData(v___x_2632_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2636_ = l_Lean_stringToMessageData(v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2639_ = l_Lean_stringToMessageData(v___x_2638_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2646_, lean_object* v_declHint_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v_env_2651_; uint8_t v___y_2653_; uint8_t v___x_2709_; uint8_t v___x_2710_; 
v___x_2650_ = lean_st_ref_get(v___y_2648_);
v_env_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_ref(v_env_2651_);
lean_dec(v___x_2650_);
v___x_2709_ = l_Lean_Name_isAnonymous(v_declHint_2647_);
v___x_2710_ = lean_bool_not(v___x_2709_);
if (v___x_2710_ == 0)
{
v___y_2653_ = v___x_2710_;
goto v___jp_2652_;
}
else
{
uint8_t v_isExporting_2711_; 
v_isExporting_2711_ = lean_ctor_get_uint8(v_env_2651_, sizeof(void*)*8);
v___y_2653_ = v_isExporting_2711_;
goto v___jp_2652_;
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_msg_2646_);
return v___x_2654_;
}
else
{
uint8_t v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = 0;
lean_inc_ref(v_env_2651_);
v___x_2656_ = l_Lean_Environment_setExporting(v_env_2651_, v___x_2655_);
lean_inc(v_declHint_2647_);
lean_inc_ref(v___x_2656_);
v___x_2657_ = l_Lean_Environment_contains(v___x_2656_, v_declHint_2647_, v___y_2653_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_msg_2646_);
return v___x_2658_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v_c_2664_; lean_object* v___x_2665_; 
v___x_2659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2661_ = l_Lean_Options_empty;
v___x_2662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2656_);
lean_ctor_set(v___x_2662_, 1, v___x_2659_);
lean_ctor_set(v___x_2662_, 2, v___x_2660_);
lean_ctor_set(v___x_2662_, 3, v___x_2661_);
lean_inc(v_declHint_2647_);
v___x_2663_ = l_Lean_MessageData_ofConstName(v_declHint_2647_, v___x_2655_);
v_c_2664_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2664_, 0, v___x_2662_);
lean_ctor_set(v_c_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2651_, v_declHint_2647_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v_c_2664_);
v___x_2668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_MessageData_note(v___x_2669_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_msg_2646_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
else
{
lean_object* v_val_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2708_; 
v_val_2673_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2675_ = v___x_2665_;
v_isShared_2676_ = v_isSharedCheck_2708_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_val_2673_);
lean_dec(v___x_2665_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2708_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_mod_2680_; uint8_t v___x_2681_; 
v___x_2677_ = lean_box(0);
v___x_2678_ = l_Lean_Environment_header(v_env_2651_);
lean_dec_ref(v_env_2651_);
v___x_2679_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2678_);
v_mod_2680_ = lean_array_get(v___x_2677_, v___x_2679_, v_val_2673_);
lean_dec(v_val_2673_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = l_Lean_isPrivateName(v_declHint_2647_);
lean_dec(v_declHint_2647_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v_c_2664_);
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_MessageData_ofName(v_mod_2680_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_note(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_msg_2646_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2691_);
v___x_2693_ = v___x_2675_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v_c_2664_);
v___x_2697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_MessageData_ofName(v_mod_2680_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_MessageData_note(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_msg_2646_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2704_);
v___x_2706_ = v___x_2675_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2712_, lean_object* v_declHint_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2712_, v_declHint_2713_, v___y_2714_);
lean_dec(v___y_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2717_, lean_object* v_declHint_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2732_; 
v___x_2722_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2717_, v_declHint_2718_, v___y_2720_);
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2732_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2732_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2727_ = l_Lean_unknownIdentifierMessageTag;
v___x_2728_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v_a_2723_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2728_);
v___x_2730_ = v___x_2725_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2733_, v_declHint_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v_env_2744_; lean_object* v_options_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2743_ = lean_st_ref_get(v___y_2741_);
v_env_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_env_2744_);
lean_dec(v___x_2743_);
v_options_2745_ = lean_ctor_get(v___y_2740_, 2);
v___x_2746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2747_ = lean_unsigned_to_nat(32u);
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2747_);
lean_dec_ref(v___x_2748_);
v___x_2749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2745_);
v___x_2750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2750_, 0, v_env_2744_);
lean_ctor_set(v___x_2750_, 1, v___x_2746_);
lean_ctor_set(v___x_2750_, 2, v___x_2749_);
lean_ctor_set(v___x_2750_, 3, v_options_2745_);
v___x_2751_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_msgData_2739_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_ref_2762_; lean_object* v___x_2763_; lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2772_; 
v_ref_2762_ = lean_ctor_get(v___y_2759_, 5);
v___x_2763_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2758_, v___y_2759_, v___y_2760_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2772_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2772_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_inc(v_ref_2762_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_ref_2762_);
lean_ctor_set(v___x_2768_, 1, v_a_2764_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 1);
lean_ctor_set(v___x_2766_, 0, v___x_2768_);
v___x_2770_ = v___x_2766_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2778_, lean_object* v_msg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_fileName_2783_; lean_object* v_fileMap_2784_; lean_object* v_options_2785_; lean_object* v_currRecDepth_2786_; lean_object* v_maxRecDepth_2787_; lean_object* v_ref_2788_; lean_object* v_currNamespace_2789_; lean_object* v_openDecls_2790_; lean_object* v_initHeartbeats_2791_; lean_object* v_maxHeartbeats_2792_; lean_object* v_quotContext_2793_; lean_object* v_currMacroScope_2794_; uint8_t v_diag_2795_; lean_object* v_cancelTk_x3f_2796_; uint8_t v_suppressElabErrors_2797_; lean_object* v_inheritedTraceOptions_2798_; lean_object* v_ref_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_fileName_2783_ = lean_ctor_get(v___y_2780_, 0);
v_fileMap_2784_ = lean_ctor_get(v___y_2780_, 1);
v_options_2785_ = lean_ctor_get(v___y_2780_, 2);
v_currRecDepth_2786_ = lean_ctor_get(v___y_2780_, 3);
v_maxRecDepth_2787_ = lean_ctor_get(v___y_2780_, 4);
v_ref_2788_ = lean_ctor_get(v___y_2780_, 5);
v_currNamespace_2789_ = lean_ctor_get(v___y_2780_, 6);
v_openDecls_2790_ = lean_ctor_get(v___y_2780_, 7);
v_initHeartbeats_2791_ = lean_ctor_get(v___y_2780_, 8);
v_maxHeartbeats_2792_ = lean_ctor_get(v___y_2780_, 9);
v_quotContext_2793_ = lean_ctor_get(v___y_2780_, 10);
v_currMacroScope_2794_ = lean_ctor_get(v___y_2780_, 11);
v_diag_2795_ = lean_ctor_get_uint8(v___y_2780_, sizeof(void*)*14);
v_cancelTk_x3f_2796_ = lean_ctor_get(v___y_2780_, 12);
v_suppressElabErrors_2797_ = lean_ctor_get_uint8(v___y_2780_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2798_ = lean_ctor_get(v___y_2780_, 13);
v_ref_2799_ = l_Lean_replaceRef(v_ref_2778_, v_ref_2788_);
lean_inc_ref(v_inheritedTraceOptions_2798_);
lean_inc(v_cancelTk_x3f_2796_);
lean_inc(v_currMacroScope_2794_);
lean_inc(v_quotContext_2793_);
lean_inc(v_maxHeartbeats_2792_);
lean_inc(v_initHeartbeats_2791_);
lean_inc(v_openDecls_2790_);
lean_inc(v_currNamespace_2789_);
lean_inc(v_maxRecDepth_2787_);
lean_inc(v_currRecDepth_2786_);
lean_inc_ref(v_options_2785_);
lean_inc_ref(v_fileMap_2784_);
lean_inc_ref(v_fileName_2783_);
v___x_2800_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2800_, 0, v_fileName_2783_);
lean_ctor_set(v___x_2800_, 1, v_fileMap_2784_);
lean_ctor_set(v___x_2800_, 2, v_options_2785_);
lean_ctor_set(v___x_2800_, 3, v_currRecDepth_2786_);
lean_ctor_set(v___x_2800_, 4, v_maxRecDepth_2787_);
lean_ctor_set(v___x_2800_, 5, v_ref_2799_);
lean_ctor_set(v___x_2800_, 6, v_currNamespace_2789_);
lean_ctor_set(v___x_2800_, 7, v_openDecls_2790_);
lean_ctor_set(v___x_2800_, 8, v_initHeartbeats_2791_);
lean_ctor_set(v___x_2800_, 9, v_maxHeartbeats_2792_);
lean_ctor_set(v___x_2800_, 10, v_quotContext_2793_);
lean_ctor_set(v___x_2800_, 11, v_currMacroScope_2794_);
lean_ctor_set(v___x_2800_, 12, v_cancelTk_x3f_2796_);
lean_ctor_set(v___x_2800_, 13, v_inheritedTraceOptions_2798_);
lean_ctor_set_uint8(v___x_2800_, sizeof(void*)*14, v_diag_2795_);
lean_ctor_set_uint8(v___x_2800_, sizeof(void*)*14 + 1, v_suppressElabErrors_2797_);
v___x_2801_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2779_, v___x_2800_, v___y_2781_);
lean_dec_ref_known(v___x_2800_, 14);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2802_, lean_object* v_msg_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2802_, v_msg_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_ref_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2808_, lean_object* v_msg_2809_, lean_object* v_declHint_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; 
v___x_2814_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2809_, v_declHint_2810_, v___y_2811_, v___y_2812_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2808_, v_a_2815_, v___y_2811_, v___y_2812_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2817_, lean_object* v_msg_2818_, lean_object* v_declHint_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2817_, v_msg_2818_, v_declHint_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_ref_2817_);
return v_res_2823_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2826_ = l_Lean_stringToMessageData(v___x_2825_);
return v___x_2826_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2829_ = l_Lean_stringToMessageData(v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2830_, lean_object* v_constName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2835_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2836_ = 0;
lean_inc(v_constName_2831_);
v___x_2837_ = l_Lean_MessageData_ofConstName(v_constName_2831_, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2830_, v___x_2840_, v_constName_2831_, v___y_2832_, v___y_2833_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2842_, lean_object* v_constName_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2842_, v_constName_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_ref_2842_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_ref_2852_; lean_object* v___x_2853_; 
v_ref_2852_ = lean_ctor_get(v___y_2849_, 5);
v___x_2853_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2852_, v_constName_2848_, v___y_2849_, v___y_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v_env_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_st_ref_get(v___y_2861_);
v_env_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_ref(v_env_2864_);
lean_dec(v___x_2863_);
v___x_2865_ = 0;
lean_inc(v_constName_2859_);
v___x_2866_ = l_Lean_Environment_find_x3f(v_env_2864_, v_constName_2859_, v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2859_, v___y_2860_, v___y_2861_);
return v___x_2867_;
}
else
{
lean_object* v_val_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_constName_2859_);
v_val_2868_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2866_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_val_2868_);
lean_dec(v___x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 0);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_val_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Expr_getAppFn(v_type_2881_);
if (lean_obj_tag(v___x_2885_) == 4)
{
lean_object* v_declName_2886_; lean_object* v___x_2887_; 
v_declName_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_declName_2886_);
lean_dec_ref_known(v___x_2885_, 2);
v___x_2887_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2886_, v_a_2882_, v_a_2883_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2905_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2905_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2905_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
if (lean_obj_tag(v_a_2888_) == 5)
{
lean_object* v_val_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v_val_2892_ = lean_ctor_get(v_a_2888_, 0);
lean_inc_ref(v_val_2892_);
lean_dec_ref_known(v_a_2888_, 1);
v___x_2893_ = l_Lean_InductiveVal_numCtors(v_val_2892_);
lean_dec_ref(v_val_2892_);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_dec_le(v___x_2893_, v___x_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(v___x_2895_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2896_);
v___x_2898_ = v___x_2890_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
else
{
uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec(v_a_2888_);
v___x_2900_ = 0;
v___x_2901_ = lean_box(v___x_2900_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2901_);
v___x_2903_ = v___x_2890_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2887_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2887_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
uint8_t v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v___x_2885_);
v___x_2914_ = 0;
v___x_2915_ = lean_box(v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v_type_2917_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2922_, lean_object* v_constName_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2923_, v___y_2924_, v___y_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_constName_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2928_, v_constName_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2934_, lean_object* v_ref_2935_, lean_object* v_constName_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2935_, v_constName_2936_, v___y_2937_, v___y_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2941_, lean_object* v_ref_2942_, lean_object* v_constName_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2941_, v_ref_2942_, v_constName_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v_ref_2942_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2948_, lean_object* v_ref_2949_, lean_object* v_msg_2950_, lean_object* v_declHint_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2949_, v_msg_2950_, v_declHint_2951_, v___y_2952_, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_ref_2957_, lean_object* v_msg_2958_, lean_object* v_declHint_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2956_, v_ref_2957_, v_msg_2958_, v_declHint_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v_ref_2957_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2964_, lean_object* v_declHint_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2964_, v_declHint_2965_, v___y_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2970_, lean_object* v_declHint_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2970_, v_declHint_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2976_, lean_object* v_ref_2977_, lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2977_, v_msg_2978_, v___y_2979_, v___y_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2983_, lean_object* v_ref_2984_, lean_object* v_msg_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2983_, v_ref_2984_, v_msg_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v_ref_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2991_, v___y_2992_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2996_, v_msg_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3002_, lean_object* v_fvarId_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_toGoalState_3009_; lean_object* v_mvarId_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3046_; 
v_toGoalState_3009_ = lean_ctor_get(v_goal_3002_, 0);
v_mvarId_3010_ = lean_ctor_get(v_goal_3002_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_goal_3002_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3012_ = v_goal_3002_;
v_isShared_3013_ = v_isSharedCheck_3046_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_mvarId_3010_);
lean_inc(v_toGoalState_3009_);
lean_dec(v_goal_3002_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3046_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3010_, v_fvarId_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3037_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3037_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3037_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
if (lean_obj_tag(v_a_3015_) == 1)
{
lean_object* v_val_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3032_; 
v_val_3019_ = lean_ctor_get(v_a_3015_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_a_3015_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3021_ = v_a_3015_;
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_val_3019_);
lean_dec(v_a_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3032_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v_val_3019_);
v___x_3024_ = v___x_3012_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_toGoalState_3009_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_val_3019_);
v___x_3024_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3024_);
v___x_3026_ = v___x_3021_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3026_);
v___x_3028_ = v___x_3017_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_a_3015_);
lean_del_object(v___x_3012_);
lean_dec_ref(v_toGoalState_3009_);
v___x_3033_ = lean_box(0);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3033_);
v___x_3035_ = v___x_3017_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_3012_);
lean_dec_ref(v_toGoalState_3009_);
v_a_3038_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3014_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3014_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3047_, lean_object* v_fvarId_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3047_, v_fvarId_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3055_, v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
v_a_3071_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3062_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3062_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3079_, v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3087_, lean_object* v_mvarId_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3088_, v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_mvarId_3097_, lean_object* v_x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3096_, v_mvarId_3097_, v_x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3105_, lean_object* v_toGoalState_3106_, lean_object* v_goal_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; 
lean_inc(v_mvarId_3105_);
v___x_3113_ = l_Lean_MVarId_getType(v_mvarId_3105_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = l_Lean_Meta_isProp(v_a_3114_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3142_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3142_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3142_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_unbox(v_a_3116_);
lean_dec(v_a_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_del_object(v___x_3118_);
lean_dec_ref(v_goal_3107_);
v___x_3121_ = l_Lean_MVarId_exfalso(v_mvarId_3105_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3130_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v_toGoalState_3106_);
lean_ctor_set(v___x_3126_, 1, v_a_3122_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3126_);
v___x_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_toGoalState_3106_);
v_a_3131_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3121_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3121_);
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
lean_object* v___x_3140_; 
lean_dec_ref(v_toGoalState_3106_);
lean_dec(v_mvarId_3105_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_goal_3107_);
v___x_3140_ = v___x_3118_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_goal_3107_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v_goal_3107_);
lean_dec_ref(v_toGoalState_3106_);
lean_dec(v_mvarId_3105_);
v_a_3143_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3115_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3115_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v_goal_3107_);
lean_dec_ref(v_toGoalState_3106_);
lean_dec(v_mvarId_3105_);
v_a_3151_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3113_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3113_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3159_, lean_object* v_toGoalState_3160_, lean_object* v_goal_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3159_, v_toGoalState_3160_, v_goal_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_toGoalState_3174_; lean_object* v_mvarId_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; 
v_toGoalState_3174_ = lean_ctor_get(v_goal_3168_, 0);
lean_inc_ref(v_toGoalState_3174_);
v_mvarId_3175_ = lean_ctor_get(v_goal_3168_, 1);
lean_inc_n(v_mvarId_3175_, 2);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3176_, 0, v_mvarId_3175_);
lean_closure_set(v___f_3176_, 1, v_toGoalState_3174_);
lean_closure_set(v___f_3176_, 2, v_goal_3168_);
v___x_3177_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3175_, v___f_3176_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_mvarId_3191_; lean_object* v___x_3192_; 
v_mvarId_3191_ = lean_ctor_get(v_goal_3185_, 1);
lean_inc(v_mvarId_3191_);
lean_dec_ref(v_goal_3185_);
v___x_3192_ = l_Lean_MVarId_getDecl(v_mvarId_3191_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3202_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3202_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3202_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_lctx_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v_lctx_3197_ = lean_ctor_get(v_a_3193_, 1);
lean_inc_ref(v_lctx_3197_);
lean_dec(v_a_3193_);
v___x_3198_ = l_Lean_LocalContext_lastDecl(v_lctx_3197_);
lean_dec_ref(v_lctx_3197_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3198_);
v___x_3200_ = v___x_3195_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
v_a_3203_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3192_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3192_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
if (lean_obj_tag(v_a_3219_) == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = l_List_reverse___redArg(v_a_3220_);
return v___x_3221_;
}
else
{
lean_object* v_head_3222_; lean_object* v_tail_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3233_; 
v_head_3222_ = lean_ctor_get(v_a_3219_, 0);
v_tail_3223_ = lean_ctor_get(v_a_3219_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_a_3219_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3225_ = v_a_3219_;
v_isShared_3226_ = v_isSharedCheck_3233_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_tail_3223_);
lean_inc(v_head_3222_);
lean_dec(v_a_3219_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3233_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_toGoalState_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v_toGoalState_3227_ = lean_ctor_get(v_goal_3218_, 0);
lean_inc_ref(v_toGoalState_3227_);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_toGoalState_3227_);
lean_ctor_set(v___x_3228_, 1, v_head_3222_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v_a_3220_);
lean_ctor_set(v___x_3225_, 0, v___x_3228_);
v___x_3230_ = v___x_3225_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_a_3220_);
v___x_3230_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
v_a_3219_ = v_tail_3223_;
v_a_3220_ = v___x_3230_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3234_, v_a_3235_, v_a_3236_);
lean_dec_ref(v_goal_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3238_, lean_object* v_as_x27_3239_, lean_object* v_b_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
if (lean_obj_tag(v_as_x27_3239_) == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v_kp_3238_);
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_b_3240_);
return v___x_3251_;
}
else
{
lean_object* v_head_3252_; lean_object* v_tail_3253_; lean_object* v___x_3254_; 
v_head_3252_ = lean_ctor_get(v_as_x27_3239_, 0);
v_tail_3253_ = lean_ctor_get(v_as_x27_3239_, 1);
lean_inc_ref(v_kp_3238_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc(v_head_3252_);
v___x_3254_ = lean_apply_11(v_kp_3238_, v_head_3252_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, lean_box(0));
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
if (lean_obj_tag(v_a_3255_) == 0)
{
lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3267_; 
v_fst_3256_ = lean_ctor_get(v_b_3240_, 0);
v_snd_3257_ = lean_ctor_get(v_b_3240_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_b_3240_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3259_ = v_b_3240_;
v_isShared_3260_ = v_isSharedCheck_3267_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_snd_3257_);
lean_inc(v_fst_3256_);
lean_dec(v_b_3240_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3267_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v_seq_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v_seq_3261_ = lean_ctor_get(v_a_3255_, 0);
lean_inc(v_seq_3261_);
lean_dec_ref_known(v_a_3255_, 1);
v___x_3262_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3256_, v_seq_3261_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3262_);
v___x_3264_ = v___x_3259_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_snd_3257_);
v___x_3264_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
v_as_x27_3239_ = v_tail_3253_;
v_b_3240_ = v___x_3264_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3279_; 
v_fst_3268_ = lean_ctor_get(v_b_3240_, 0);
v_snd_3269_ = lean_ctor_get(v_b_3240_, 1);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_b_3240_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3271_ = v_b_3240_;
v_isShared_3272_ = v_isSharedCheck_3279_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_snd_3269_);
lean_inc(v_fst_3268_);
lean_dec(v_b_3240_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3279_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_gs_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v_gs_3273_ = lean_ctor_get(v_a_3255_, 0);
lean_inc(v_gs_3273_);
lean_dec_ref_known(v_a_3255_, 1);
v___x_3274_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3269_, v_gs_3273_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 1, v___x_3274_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_fst_3268_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
v_as_x27_3239_ = v_tail_3253_;
v_b_3240_ = v___x_3276_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_b_3240_);
lean_dec_ref(v_kp_3238_);
v_a_3280_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3254_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3254_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3288_, lean_object* v_as_x27_3289_, lean_object* v_b_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3288_, v_as_x27_3289_, v_b_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v_as_x27_3289_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3306_, lean_object* v_mvarId_3307_, lean_object* v_goal_3308_, lean_object* v_kp_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___x_3375_; 
lean_inc(v_fvarId_3306_);
v___x_3375_ = l_Lean_FVarId_getType___redArg(v_fvarId_3306_, v___y_3315_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
v___x_3377_ = lean_whnf(v_a_3376_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___x_3400_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3400_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3378_, v___y_3311_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3440_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3440_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3440_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_unbox(v_a_3401_);
lean_dec(v_a_3401_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v___x_3406_ = lean_box(0);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3406_);
v___x_3408_ = v___x_3403_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
else
{
lean_object* v___x_3410_; 
lean_del_object(v___x_3403_);
v___x_3410_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3311_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; uint8_t v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3412_ == 0)
{
v___y_3380_ = v___y_3310_;
v___y_3381_ = v___y_3311_;
v___y_3382_ = v___y_3312_;
v___y_3383_ = v___y_3313_;
v___y_3384_ = v___y_3314_;
v___y_3385_ = v___y_3315_;
v___y_3386_ = v___y_3316_;
v___y_3387_ = v___y_3317_;
v___y_3388_ = v___y_3318_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3378_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3423_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_unbox(v_a_3414_);
lean_dec(v_a_3414_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v___x_3419_ = lean_box(0);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3419_);
v___x_3421_ = v___x_3416_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
else
{
lean_del_object(v___x_3416_);
v___y_3380_ = v___y_3310_;
v___y_3381_ = v___y_3311_;
v___y_3382_ = v___y_3312_;
v___y_3383_ = v___y_3313_;
v___y_3384_ = v___y_3314_;
v___y_3385_ = v___y_3315_;
v___y_3386_ = v___y_3316_;
v___y_3387_ = v___y_3317_;
v___y_3388_ = v___y_3318_;
goto v___jp_3379_;
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3424_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3413_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3413_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3432_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3410_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3410_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3441_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3400_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3400_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_Expr_getAppFn(v_a_3378_);
lean_dec(v_a_3378_);
if (lean_obj_tag(v___x_3389_) == 4)
{
lean_object* v_declName_3390_; lean_object* v___x_3391_; 
v_declName_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_declName_3390_);
lean_dec_ref_known(v___x_3389_, 2);
v___x_3391_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3390_, v___y_3382_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_dec_ref_known(v___x_3391_, 1);
v___y_3321_ = v___y_3380_;
v___y_3322_ = v___y_3381_;
v___y_3323_ = v___y_3382_;
v___y_3324_ = v___y_3383_;
v___y_3325_ = v___y_3384_;
v___y_3326_ = v___y_3385_;
v___y_3327_ = v___y_3386_;
v___y_3328_ = v___y_3387_;
v___y_3329_ = v___y_3388_;
goto v___jp_3320_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_dec_ref(v___x_3389_);
v___y_3321_ = v___y_3380_;
v___y_3322_ = v___y_3381_;
v___y_3323_ = v___y_3382_;
v___y_3324_ = v___y_3383_;
v___y_3325_ = v___y_3384_;
v___y_3326_ = v___y_3385_;
v___y_3327_ = v___y_3386_;
v___y_3328_ = v___y_3387_;
v___y_3329_ = v___y_3388_;
goto v___jp_3320_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3449_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3377_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3377_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v_kp_3309_);
lean_dec(v_mvarId_3307_);
lean_dec(v_fvarId_3306_);
v_a_3457_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3375_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3375_);
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
v___jp_3320_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = l_Lean_mkFVar(v_fvarId_3306_);
v___x_3331_ = l_Lean_Meta_Grind_cases(v_mvarId_3307_, v___x_3330_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3331_, 1);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3308_, v_a_3332_, v___x_3333_);
v___x_3335_ = lean_unsigned_to_nat(0u);
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3337_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3309_, v___x_3334_, v___x_3336_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___x_3334_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3358_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3358_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3358_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_fst_3342_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_fst_3342_);
v_snd_3343_ = lean_ctor_get(v_a_3338_, 1);
lean_inc(v_snd_3343_);
lean_dec(v_a_3338_);
v___x_3344_ = lean_array_get_size(v_snd_3343_);
v___x_3345_ = lean_nat_dec_eq(v___x_3344_, v___x_3335_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
lean_dec(v_fst_3342_);
v___x_3346_ = lean_array_to_list(v_snd_3343_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3348_);
v___x_3350_ = v___x_3340_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_snd_3343_);
v___x_3352_ = lean_array_to_list(v_fst_3342_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3354_);
v___x_3356_ = v___x_3340_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
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
v_a_3359_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3337_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3337_);
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
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec_ref(v_kp_3309_);
v_a_3367_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3331_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3331_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3465_, lean_object* v_mvarId_3466_, lean_object* v_goal_3467_, lean_object* v_kp_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3465_, v_mvarId_3466_, v_goal_3467_, v_kp_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v_goal_3467_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3480_, lean_object* v_fvarId_3481_, lean_object* v_kp_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_mvarId_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; 
v_mvarId_3493_ = lean_ctor_get(v_goal_3480_, 1);
lean_inc_n(v_mvarId_3493_, 2);
v___f_3494_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3494_, 0, v_fvarId_3481_);
lean_closure_set(v___f_3494_, 1, v_mvarId_3493_);
lean_closure_set(v___f_3494_, 2, v_goal_3480_);
lean_closure_set(v___f_3494_, 3, v_kp_3482_);
v___x_3495_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3493_, v___f_3494_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3496_, lean_object* v_fvarId_3497_, lean_object* v_kp_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3496_, v_fvarId_3497_, v_kp_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3510_, lean_object* v_as_3511_, lean_object* v_as_x27_3512_, lean_object* v_b_3513_, lean_object* v_a_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3510_, v_as_x27_3512_, v_b_3513_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3526_, lean_object* v_as_3527_, lean_object* v_as_x27_3528_, lean_object* v_b_3529_, lean_object* v_a_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3526_, v_as_3527_, v_as_x27_3528_, v_b_3529_, v_a_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec(v_as_x27_3528_);
lean_dec(v_as_3527_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3542_, lean_object* v_fvarId_3543_, lean_object* v_generation_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_st_mk_ref(v_goal_3542_);
v___x_3556_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3543_, v_generation_3544_, v___x_3555_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3565_; 
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3556_, 0);
lean_dec(v_unused_3566_);
v___x_3558_ = v___x_3556_;
v_isShared_3559_ = v_isSharedCheck_3565_;
goto v_resetjp_3557_;
}
else
{
lean_dec(v___x_3556_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3565_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3560_ = lean_st_ref_get(v___x_3555_);
v___x_3561_ = lean_st_ref_get(v___x_3555_);
lean_dec(v___x_3555_);
lean_dec(v___x_3561_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3560_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v___x_3555_);
v_a_3567_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3556_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3556_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3575_, lean_object* v_fvarId_3576_, lean_object* v_generation_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3575_, v_fvarId_3576_, v_generation_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3591_, lean_object* v_goal_3592_, lean_object* v_kna_3593_, lean_object* v_kp_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_toGoalState_3605_; uint8_t v_inconsistent_3606_; 
v_toGoalState_3605_ = lean_ctor_get(v_goal_3592_, 0);
v_inconsistent_3606_ = lean_ctor_get_uint8(v_toGoalState_3605_, sizeof(void*)*17);
if (v_inconsistent_3606_ == 0)
{
lean_object* v_mvarId_3607_; lean_object* v___x_3608_; 
v_mvarId_3607_ = lean_ctor_get(v_goal_3592_, 1);
lean_inc(v_mvarId_3607_);
v___x_3608_ = l_Lean_MVarId_getType(v_mvarId_3607_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; uint8_t v___x_3610_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v___x_3610_ = l_Lean_Expr_isFalse(v_a_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec_ref(v_kna_3593_);
lean_inc(v_generation_3591_);
v___x_3611_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3592_, v_generation_3591_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
switch(lean_obj_tag(v_a_3612_))
{
case 0:
{
lean_object* v_goal_3613_; lean_object* v___x_3614_; 
lean_dec(v_generation_3591_);
v_goal_3613_ = lean_ctor_get(v_a_3612_, 0);
lean_inc_ref(v_goal_3613_);
lean_dec_ref_known(v_a_3612_, 1);
v___x_3614_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3613_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v_toGoalState_3616_; lean_object* v_mvarId_3617_; lean_object* v___x_3618_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
v_toGoalState_3616_ = lean_ctor_get(v_a_3615_, 0);
v_mvarId_3617_ = lean_ctor_get(v_a_3615_, 1);
lean_inc(v_mvarId_3617_);
v___x_3618_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3617_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
if (lean_obj_tag(v_a_3619_) == 1)
{
lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3628_; 
lean_inc_ref(v_toGoalState_3616_);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_a_3615_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3629_ = lean_ctor_get(v_a_3615_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_a_3615_, 0);
lean_dec(v_unused_3630_);
v___x_3621_ = v_a_3615_;
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v_a_3615_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v_val_3623_; lean_object* v___x_3625_; 
v_val_3623_ = lean_ctor_get(v_a_3619_, 0);
lean_inc(v_val_3623_);
lean_dec_ref_known(v_a_3619_, 1);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 1, v_val_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_toGoalState_3616_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_val_3623_);
v___x_3625_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; 
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3626_ = lean_apply_11(v_kp_3594_, v___x_3625_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3626_;
}
}
}
else
{
lean_object* v___x_3631_; 
lean_dec(v_a_3619_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3631_ = lean_apply_11(v_kp_3594_, v_a_3615_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3631_;
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_a_3615_);
lean_dec_ref(v_kp_3594_);
v_a_3632_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3618_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3618_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v_kp_3594_);
v_a_3640_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3614_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3614_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3648_; lean_object* v_goal_3649_; lean_object* v___x_3650_; 
v_fvarId_3648_ = lean_ctor_get(v_a_3612_, 0);
lean_inc_n(v_fvarId_3648_, 2);
v_goal_3649_ = lean_ctor_get(v_a_3612_, 1);
lean_inc_ref_n(v_goal_3649_, 2);
lean_dec_ref_known(v_a_3612_, 2);
v___x_3650_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3649_, v_fvarId_3648_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
if (lean_obj_tag(v_a_3651_) == 1)
{
lean_object* v_val_3652_; lean_object* v___x_3653_; 
lean_dec_ref(v_goal_3649_);
lean_dec(v_fvarId_3648_);
lean_dec(v_generation_3591_);
v_val_3652_ = lean_ctor_get(v_a_3651_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_a_3651_, 1);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3653_ = lean_apply_11(v_kp_3594_, v_val_3652_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; 
lean_dec(v_a_3651_);
lean_inc_ref(v_kp_3594_);
lean_inc(v_fvarId_3648_);
lean_inc_ref(v_goal_3649_);
v___x_3654_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3649_, v_fvarId_3648_, v_kp_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3676_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3676_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3676_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
if (lean_obj_tag(v_a_3655_) == 1)
{
lean_object* v_val_3659_; lean_object* v___x_3661_; 
lean_dec_ref(v_goal_3649_);
lean_dec(v_fvarId_3648_);
lean_dec_ref(v_kp_3594_);
lean_dec(v_generation_3591_);
v_val_3659_ = lean_ctor_get(v_a_3655_, 0);
lean_inc(v_val_3659_);
lean_dec_ref_known(v_a_3655_, 1);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_val_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_val_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
else
{
lean_object* v_mvarId_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; 
lean_del_object(v___x_3657_);
lean_dec(v_a_3655_);
v_mvarId_3663_ = lean_ctor_get(v_goal_3649_, 1);
lean_inc(v_mvarId_3663_);
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3664_, 0, v_goal_3649_);
lean_closure_set(v___f_3664_, 1, v_fvarId_3648_);
lean_closure_set(v___f_3664_, 2, v_generation_3591_);
v___x_3665_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3663_, v___f_3664_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3667_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3667_ = lean_apply_11(v_kp_3594_, v_a_3666_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3667_;
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v_kp_3594_);
v_a_3668_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3665_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3665_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v_goal_3649_);
lean_dec(v_fvarId_3648_);
lean_dec_ref(v_kp_3594_);
lean_dec(v_generation_3591_);
v_a_3677_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3654_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3654_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec_ref(v_goal_3649_);
lean_dec(v_fvarId_3648_);
lean_dec_ref(v_kp_3594_);
lean_dec(v_generation_3591_);
v_a_3685_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3650_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3650_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
case 2:
{
lean_object* v_goal_3693_; lean_object* v___x_3694_; 
lean_dec(v_generation_3591_);
v_goal_3693_ = lean_ctor_get(v_a_3612_, 0);
lean_inc_ref(v_goal_3693_);
lean_dec_ref_known(v_a_3612_, 1);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3694_ = lean_apply_11(v_kp_3594_, v_goal_3693_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3694_;
}
default: 
{
lean_object* v_fvarId_3695_; lean_object* v_goal_3696_; lean_object* v___x_3697_; 
lean_dec(v_generation_3591_);
v_fvarId_3695_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_fvarId_3695_);
v_goal_3696_ = lean_ctor_get(v_a_3612_, 1);
lean_inc_ref_n(v_goal_3696_, 2);
lean_dec_ref_known(v_a_3612_, 2);
lean_inc_ref(v_kp_3594_);
v___x_3697_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3696_, v_fvarId_3695_, v_kp_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3707_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3707_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3707_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
if (lean_obj_tag(v_a_3698_) == 1)
{
lean_object* v_val_3702_; lean_object* v___x_3704_; 
lean_dec_ref(v_goal_3696_);
lean_dec_ref(v_kp_3594_);
v_val_3702_ = lean_ctor_get(v_a_3698_, 0);
lean_inc(v_val_3702_);
lean_dec_ref_known(v_a_3698_, 1);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v_val_3702_);
v___x_3704_ = v___x_3700_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_val_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v___x_3706_; 
lean_del_object(v___x_3700_);
lean_dec(v_a_3698_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3706_ = lean_apply_11(v_kp_3594_, v_goal_3696_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3706_;
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v_goal_3696_);
lean_dec_ref(v_kp_3594_);
v_a_3708_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3697_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3697_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec_ref(v_kp_3594_);
lean_dec(v_generation_3591_);
v_a_3716_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3611_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3611_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___x_3724_; 
lean_dec_ref(v_kp_3594_);
lean_dec(v_generation_3591_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
lean_inc_ref(v_a_3600_);
lean_inc(v_a_3599_);
lean_inc_ref(v_a_3598_);
lean_inc(v_a_3597_);
lean_inc_ref(v_a_3596_);
lean_inc(v_a_3595_);
v___x_3724_ = lean_apply_11(v_kna_3593_, v_goal_3592_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, lean_box(0));
return v___x_3724_;
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec_ref(v_kp_3594_);
lean_dec_ref(v_kna_3593_);
lean_dec_ref(v_goal_3592_);
lean_dec(v_generation_3591_);
v_a_3725_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3608_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3608_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec_ref(v_kp_3594_);
lean_dec_ref(v_kna_3593_);
lean_dec_ref(v_goal_3592_);
lean_dec(v_generation_3591_);
v___x_3733_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3735_, lean_object* v_goal_3736_, lean_object* v_kna_3737_, lean_object* v_kp_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Meta_Grind_Action_intro(v_generation_3735_, v_goal_3736_, v_kna_3737_, v_kp_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
return v_res_3749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_unsigned_to_nat(1000000u);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3751_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3766_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3779_, lean_object* v___f_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_unsigned_to_nat(1000000u);
v___x_3795_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3795_, 0, v_generation_3779_);
v___x_3796_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3796_, 0, v___x_3794_);
lean_closure_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l_Lean_Meta_Grind_Action_andThen(v___x_3796_, v___f_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3798_, lean_object* v___f_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3798_, v___f_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3816_, lean_object* v_a_3817_, lean_object* v_kna_3818_, lean_object* v_kp_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___f_3830_; lean_object* v___f_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___f_3830_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3831_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3831_, 0, v_generation_3816_);
lean_closure_set(v___f_3831_, 1, v___f_3830_);
v___x_3832_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3833_ = l_Lean_Meta_Grind_Action_andThen(v___x_3832_, v___f_3831_, v_a_3817_, v_kna_3818_, v_kp_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3834_, lean_object* v_a_3835_, lean_object* v_kna_3836_, lean_object* v_kp_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Meta_Grind_Action_intros(v_generation_3834_, v_a_3835_, v_kna_3836_, v_kp_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
return v_res_3848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3858_ = l_Lean_mkConst(v___x_3857_, v___x_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3859_, lean_object* v_prop_3860_, lean_object* v_proof_3861_, lean_object* v_generation_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_st_mk_ref(v_goal_3859_);
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
lean_inc(v___y_3867_);
lean_inc_ref(v___y_3866_);
lean_inc(v___y_3865_);
lean_inc_ref(v___y_3864_);
lean_inc(v___y_3863_);
lean_inc(v___x_3873_);
lean_inc_ref(v_prop_3860_);
v___x_3874_ = lean_grind_preprocess(v_prop_3860_, v___x_3873_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v_expr_3876_; lean_object* v___x_3877_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v_expr_3876_ = lean_ctor_get(v_a_3875_, 0);
lean_inc_ref(v_expr_3876_);
v___x_3877_ = l_Lean_Meta_Simp_Result_getProof(v_a_3875_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3876_);
v___x_3880_ = l_Lean_mkApp4(v___x_3879_, v_prop_3860_, v_expr_3876_, v_a_3878_, v_proof_3861_);
v___x_3881_ = l_Lean_Meta_Grind_add(v_expr_3876_, v___x_3880_, v_generation_3862_, v___x_3873_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3890_; 
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3881_, 0);
lean_dec(v_unused_3891_);
v___x_3883_ = v___x_3881_;
v_isShared_3884_ = v_isSharedCheck_3890_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v___x_3881_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3890_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3885_ = lean_st_ref_get(v___x_3873_);
v___x_3886_ = lean_st_ref_get(v___x_3873_);
lean_dec(v___x_3873_);
lean_dec(v___x_3886_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3885_);
v___x_3888_ = v___x_3883_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3885_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v___x_3873_);
v_a_3892_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3881_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3881_);
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
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v_expr_3876_);
lean_dec(v___x_3873_);
lean_dec(v_generation_3862_);
lean_dec_ref(v_proof_3861_);
lean_dec_ref(v_prop_3860_);
v_a_3900_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3877_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3877_);
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
lean_dec(v___x_3873_);
lean_dec(v_generation_3862_);
lean_dec_ref(v_proof_3861_);
lean_dec_ref(v_prop_3860_);
v_a_3908_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3874_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3874_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3916_, lean_object* v_prop_3917_, lean_object* v_proof_3918_, lean_object* v_generation_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3916_, v_prop_3917_, v_proof_3918_, v_generation_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3931_, lean_object* v___f_3932_, lean_object* v_kp_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3931_, v___f_3932_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3946_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
lean_inc(v___y_3942_);
lean_inc_ref(v___y_3941_);
lean_inc(v___y_3940_);
lean_inc_ref(v___y_3939_);
lean_inc(v___y_3938_);
lean_inc_ref(v___y_3937_);
lean_inc(v___y_3936_);
lean_inc_ref(v___y_3935_);
lean_inc(v___y_3934_);
v___x_3946_ = lean_apply_11(v_kp_3933_, v_a_3945_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, lean_box(0));
return v___x_3946_;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_kp_3933_);
v_a_3947_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3944_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3944_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3955_, lean_object* v___f_3956_, lean_object* v_kp_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3955_, v___f_3956_, v_kp_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3969_, lean_object* v_prop_3970_, lean_object* v_generation_3971_, lean_object* v_goal_3972_, lean_object* v_kna_3973_, lean_object* v_kp_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3970_, v_a_3976_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; uint8_t v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = lean_unbox(v_a_3986_);
lean_dec(v_a_3986_);
if (v___x_3987_ == 0)
{
lean_object* v_mvarId_3988_; lean_object* v___f_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; 
lean_dec_ref(v_kna_3973_);
v_mvarId_3988_ = lean_ctor_get(v_goal_3972_, 1);
lean_inc_n(v_mvarId_3988_, 2);
v___f_3989_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3989_, 0, v_goal_3972_);
lean_closure_set(v___f_3989_, 1, v_prop_3970_);
lean_closure_set(v___f_3989_, 2, v_proof_3969_);
lean_closure_set(v___f_3989_, 3, v_generation_3971_);
v___f_3990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_3990_, 0, v_mvarId_3988_);
lean_closure_set(v___f_3990_, 1, v___f_3989_);
lean_closure_set(v___f_3990_, 2, v_kp_3974_);
v___x_3991_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3988_, v___f_3990_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_3993_ = l_Lean_Core_mkFreshUserName(v___x_3992_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v_toGoalState_3995_; lean_object* v_mvarId_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4014_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v_toGoalState_3995_ = lean_ctor_get(v_goal_3972_, 0);
v_mvarId_3996_ = lean_ctor_get(v_goal_3972_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_goal_3972_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3998_ = v_goal_3972_;
v_isShared_3999_ = v_isSharedCheck_4014_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_mvarId_3996_);
lean_inc(v_toGoalState_3995_);
lean_dec(v_goal_3972_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4014_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_MVarId_assert(v_mvarId_3996_, v_a_3994_, v_prop_3970_, v_proof_3969_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 1, v_a_4001_);
v___x_4003_ = v___x_3998_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_toGoalState_3995_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_4001_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Meta_Grind_Action_intros(v_generation_3971_, v___x_4003_, v_kna_3973_, v_kp_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4004_;
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_del_object(v___x_3998_);
lean_dec_ref(v_toGoalState_3995_);
lean_dec_ref(v_kp_3974_);
lean_dec_ref(v_kna_3973_);
lean_dec(v_generation_3971_);
v_a_4006_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4000_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4000_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v_kp_3974_);
lean_dec_ref(v_kna_3973_);
lean_dec_ref(v_goal_3972_);
lean_dec(v_generation_3971_);
lean_dec_ref(v_prop_3970_);
lean_dec_ref(v_proof_3969_);
v_a_4015_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3993_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3993_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v_kp_3974_);
lean_dec_ref(v_kna_3973_);
lean_dec_ref(v_goal_3972_);
lean_dec(v_generation_3971_);
lean_dec_ref(v_prop_3970_);
lean_dec_ref(v_proof_3969_);
v_a_4023_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_3985_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_3985_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4031_, lean_object* v_prop_4032_, lean_object* v_generation_4033_, lean_object* v_goal_4034_, lean_object* v_kna_4035_, lean_object* v_kp_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4031_, v_prop_4032_, v_generation_4033_, v_goal_4034_, v_kna_4035_, v_kp_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4048_, lean_object* v_kna_4049_, lean_object* v_kp_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_toGoalState_4061_; uint8_t v_inconsistent_4062_; 
v_toGoalState_4061_ = lean_ctor_get(v_goal_4048_, 0);
lean_inc_ref(v_toGoalState_4061_);
v_inconsistent_4062_ = lean_ctor_get_uint8(v_toGoalState_4061_, sizeof(void*)*17);
if (v_inconsistent_4062_ == 0)
{
lean_object* v_mvarId_4063_; lean_object* v_nextDeclIdx_4064_; lean_object* v_enodeMap_4065_; lean_object* v_exprs_4066_; lean_object* v_parents_4067_; lean_object* v_congrTable_4068_; lean_object* v_appMap_4069_; lean_object* v_indicesFound_4070_; lean_object* v_newFacts_4071_; lean_object* v_nextIdx_4072_; lean_object* v_newRawFacts_4073_; lean_object* v_facts_4074_; lean_object* v_extThms_4075_; lean_object* v_ematch_4076_; lean_object* v_inj_4077_; lean_object* v_split_4078_; lean_object* v_clean_4079_; lean_object* v_sstates_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4118_; 
v_mvarId_4063_ = lean_ctor_get(v_goal_4048_, 1);
v_nextDeclIdx_4064_ = lean_ctor_get(v_toGoalState_4061_, 0);
v_enodeMap_4065_ = lean_ctor_get(v_toGoalState_4061_, 1);
v_exprs_4066_ = lean_ctor_get(v_toGoalState_4061_, 2);
v_parents_4067_ = lean_ctor_get(v_toGoalState_4061_, 3);
v_congrTable_4068_ = lean_ctor_get(v_toGoalState_4061_, 4);
v_appMap_4069_ = lean_ctor_get(v_toGoalState_4061_, 5);
v_indicesFound_4070_ = lean_ctor_get(v_toGoalState_4061_, 6);
v_newFacts_4071_ = lean_ctor_get(v_toGoalState_4061_, 7);
v_nextIdx_4072_ = lean_ctor_get(v_toGoalState_4061_, 8);
v_newRawFacts_4073_ = lean_ctor_get(v_toGoalState_4061_, 9);
v_facts_4074_ = lean_ctor_get(v_toGoalState_4061_, 10);
v_extThms_4075_ = lean_ctor_get(v_toGoalState_4061_, 11);
v_ematch_4076_ = lean_ctor_get(v_toGoalState_4061_, 12);
v_inj_4077_ = lean_ctor_get(v_toGoalState_4061_, 13);
v_split_4078_ = lean_ctor_get(v_toGoalState_4061_, 14);
v_clean_4079_ = lean_ctor_get(v_toGoalState_4061_, 15);
v_sstates_4080_ = lean_ctor_get(v_toGoalState_4061_, 16);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_toGoalState_4061_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4082_ = v_toGoalState_4061_;
v_isShared_4083_ = v_isSharedCheck_4118_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_sstates_4080_);
lean_inc(v_clean_4079_);
lean_inc(v_split_4078_);
lean_inc(v_inj_4077_);
lean_inc(v_ematch_4076_);
lean_inc(v_extThms_4075_);
lean_inc(v_facts_4074_);
lean_inc(v_newRawFacts_4073_);
lean_inc(v_nextIdx_4072_);
lean_inc(v_newFacts_4071_);
lean_inc(v_indicesFound_4070_);
lean_inc(v_appMap_4069_);
lean_inc(v_congrTable_4068_);
lean_inc(v_parents_4067_);
lean_inc(v_exprs_4066_);
lean_inc(v_enodeMap_4065_);
lean_inc(v_nextDeclIdx_4064_);
lean_dec(v_toGoalState_4061_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4118_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4073_);
if (lean_obj_tag(v___x_4084_) == 1)
{
lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4114_; 
lean_inc(v_mvarId_4063_);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_goal_4048_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; lean_object* v_unused_4116_; 
v_unused_4115_ = lean_ctor_get(v_goal_4048_, 1);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_goal_4048_, 0);
lean_dec(v_unused_4116_);
v___x_4086_ = v_goal_4048_;
v_isShared_4087_ = v_isSharedCheck_4114_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v_goal_4048_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4114_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v_val_4088_; lean_object* v_fst_4089_; lean_object* v_snd_4090_; lean_object* v_proof_4091_; lean_object* v_prop_4092_; lean_object* v_generation_4093_; lean_object* v_splitSource_4094_; lean_object* v_ematchDiagSource_4095_; lean_object* v_simp_4096_; lean_object* v_simpMethods_4097_; lean_object* v_config_4098_; lean_object* v_anchorRefs_x3f_4099_; uint8_t v_cheapCases_4100_; uint8_t v_reportMVarIssue_4101_; lean_object* v_symPrios_4102_; lean_object* v_extensions_4103_; uint8_t v_debug_4104_; uint8_t v_ematchDiag_4105_; lean_object* v___x_4107_; 
v_val_4088_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_val_4088_);
lean_dec_ref_known(v___x_4084_, 1);
v_fst_4089_ = lean_ctor_get(v_val_4088_, 0);
lean_inc(v_fst_4089_);
v_snd_4090_ = lean_ctor_get(v_val_4088_, 1);
lean_inc(v_snd_4090_);
lean_dec(v_val_4088_);
v_proof_4091_ = lean_ctor_get(v_fst_4089_, 0);
lean_inc_ref(v_proof_4091_);
v_prop_4092_ = lean_ctor_get(v_fst_4089_, 1);
lean_inc_ref(v_prop_4092_);
v_generation_4093_ = lean_ctor_get(v_fst_4089_, 2);
lean_inc(v_generation_4093_);
v_splitSource_4094_ = lean_ctor_get(v_fst_4089_, 3);
lean_inc(v_splitSource_4094_);
v_ematchDiagSource_4095_ = lean_ctor_get(v_fst_4089_, 4);
lean_inc(v_ematchDiagSource_4095_);
lean_dec(v_fst_4089_);
v_simp_4096_ = lean_ctor_get(v_a_4052_, 0);
v_simpMethods_4097_ = lean_ctor_get(v_a_4052_, 1);
v_config_4098_ = lean_ctor_get(v_a_4052_, 2);
v_anchorRefs_x3f_4099_ = lean_ctor_get(v_a_4052_, 3);
v_cheapCases_4100_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*8);
v_reportMVarIssue_4101_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*8 + 1);
v_symPrios_4102_ = lean_ctor_get(v_a_4052_, 6);
v_extensions_4103_ = lean_ctor_get(v_a_4052_, 7);
v_debug_4104_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*8 + 2);
v_ematchDiag_4105_ = lean_ctor_get_uint8(v_a_4052_, sizeof(void*)*8 + 3);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 9, v_snd_4090_);
v___x_4107_ = v___x_4082_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_nextDeclIdx_4064_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_enodeMap_4065_);
lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_exprs_4066_);
lean_ctor_set(v_reuseFailAlloc_4113_, 3, v_parents_4067_);
lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_congrTable_4068_);
lean_ctor_set(v_reuseFailAlloc_4113_, 5, v_appMap_4069_);
lean_ctor_set(v_reuseFailAlloc_4113_, 6, v_indicesFound_4070_);
lean_ctor_set(v_reuseFailAlloc_4113_, 7, v_newFacts_4071_);
lean_ctor_set(v_reuseFailAlloc_4113_, 8, v_nextIdx_4072_);
lean_ctor_set(v_reuseFailAlloc_4113_, 9, v_snd_4090_);
lean_ctor_set(v_reuseFailAlloc_4113_, 10, v_facts_4074_);
lean_ctor_set(v_reuseFailAlloc_4113_, 11, v_extThms_4075_);
lean_ctor_set(v_reuseFailAlloc_4113_, 12, v_ematch_4076_);
lean_ctor_set(v_reuseFailAlloc_4113_, 13, v_inj_4077_);
lean_ctor_set(v_reuseFailAlloc_4113_, 14, v_split_4078_);
lean_ctor_set(v_reuseFailAlloc_4113_, 15, v_clean_4079_);
lean_ctor_set(v_reuseFailAlloc_4113_, 16, v_sstates_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4113_, sizeof(void*)*17, v_inconsistent_4062_);
v___x_4107_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v_goal_4109_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v___x_4107_);
v_goal_4109_ = v___x_4086_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4107_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_mvarId_4063_);
v_goal_4109_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_inc_ref(v_extensions_4103_);
lean_inc_ref(v_symPrios_4102_);
lean_inc(v_anchorRefs_x3f_4099_);
lean_inc_ref(v_config_4098_);
lean_inc_ref(v_simpMethods_4097_);
lean_inc_ref(v_simp_4096_);
v___x_4110_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_4110_, 0, v_simp_4096_);
lean_ctor_set(v___x_4110_, 1, v_simpMethods_4097_);
lean_ctor_set(v___x_4110_, 2, v_config_4098_);
lean_ctor_set(v___x_4110_, 3, v_anchorRefs_x3f_4099_);
lean_ctor_set(v___x_4110_, 4, v_splitSource_4094_);
lean_ctor_set(v___x_4110_, 5, v_ematchDiagSource_4095_);
lean_ctor_set(v___x_4110_, 6, v_symPrios_4102_);
lean_ctor_set(v___x_4110_, 7, v_extensions_4103_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*8, v_cheapCases_4100_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*8 + 1, v_reportMVarIssue_4101_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*8 + 2, v_debug_4104_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*8 + 3, v_ematchDiag_4105_);
v___x_4111_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4091_, v_prop_4092_, v_generation_4093_, v_goal_4109_, v_kna_4049_, v_kp_4050_, v_a_4051_, v___x_4110_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec_ref_known(v___x_4110_, 8);
return v___x_4111_;
}
}
}
}
else
{
lean_object* v___x_4117_; 
lean_dec(v___x_4084_);
lean_del_object(v___x_4082_);
lean_dec_ref(v_sstates_4080_);
lean_dec_ref(v_clean_4079_);
lean_dec_ref(v_split_4078_);
lean_dec_ref(v_inj_4077_);
lean_dec_ref(v_ematch_4076_);
lean_dec_ref(v_extThms_4075_);
lean_dec_ref(v_facts_4074_);
lean_dec(v_nextIdx_4072_);
lean_dec_ref(v_newFacts_4071_);
lean_dec_ref(v_indicesFound_4070_);
lean_dec_ref(v_appMap_4069_);
lean_dec_ref(v_congrTable_4068_);
lean_dec_ref(v_parents_4067_);
lean_dec_ref(v_exprs_4066_);
lean_dec_ref(v_enodeMap_4065_);
lean_dec(v_nextDeclIdx_4064_);
lean_dec_ref(v_kp_4050_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
lean_inc(v_a_4057_);
lean_inc_ref(v_a_4056_);
lean_inc(v_a_4055_);
lean_inc_ref(v_a_4054_);
lean_inc(v_a_4053_);
lean_inc_ref(v_a_4052_);
lean_inc(v_a_4051_);
v___x_4117_ = lean_apply_11(v_kna_4049_, v_goal_4048_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, lean_box(0));
return v___x_4117_;
}
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_dec_ref(v_toGoalState_4061_);
lean_dec_ref(v_kp_4050_);
lean_dec_ref(v_kna_4049_);
lean_dec_ref(v_goal_4048_);
v___x_4119_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4121_, lean_object* v_kna_4122_, lean_object* v_kp_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4121_, v_kna_4122_, v_kp_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4135_, lean_object* v_kp_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4147_ = lean_unsigned_to_nat(1000000u);
v___x_4148_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4149_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4147_, v___x_4148_, v_a_4135_, v_kp_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4150_, lean_object* v_kp_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4150_, v_kp_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
lean_dec(v_a_4152_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4163_, lean_object* v_kna_4164_, lean_object* v_kp_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4163_, v_kp_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4177_, lean_object* v_kna_4178_, lean_object* v_kp_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4177_, v_kna_4178_, v_kp_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_kna_4178_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4191_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4206_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4219_, lean_object* v___f_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_Meta_Grind_Action_andThen(v_a_4219_, v___f_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4235_, lean_object* v___f_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4235_, v___f_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4263_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4263_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4263_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___x_4261_; 
v___f_4258_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4259_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4259_, 0, v_a_4254_);
lean_closure_set(v___f_4259_, 1, v___f_4258_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___f_4259_);
v___x_4261_ = v___x_4256_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___f_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
else
{
return v___x_4253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4265_;
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
