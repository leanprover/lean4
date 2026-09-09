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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t v_decide_148_; 
v_decide_148_ = lean_nat_dec_eq(v_a_146_, v___x_144_);
if (v_decide_148_ == 0)
{
uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_149_ = lean_string_utf8_get_fast(v_str_145_, v_a_146_);
v___x_150_ = 95;
v___x_151_ = lean_uint32_dec_eq(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(0);
v___x_153_ = lean_string_utf8_next_fast(v_str_145_, v_a_146_);
lean_dec(v_a_146_);
v_a_146_ = v___x_153_;
v_b_147_ = v___x_152_;
goto _start;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_a_146_);
return v___x_155_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_156_, lean_object* v_str_157_, lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_156_, v_str_157_, v_a_158_, v_b_159_);
lean_dec(v_b_159_);
lean_dec_ref(v_str_157_);
lean_dec(v___x_156_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_167_, lean_object* v_type_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; 
if (lean_obj_tag(v_name_167_) == 1)
{
lean_object* v_str_202_; lean_object* v___y_204_; lean_object* v_searcher_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_str_202_ = lean_ctor_get(v_name_167_, 1);
lean_inc_ref(v_str_202_);
lean_dec_ref_known(v_name_167_, 2);
v_searcher_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_utf8_byte_size(v_str_202_);
v___x_224_ = lean_box(0);
v___x_225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_223_, v_str_202_, v_searcher_222_, v___x_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
v___y_204_ = v___x_223_;
goto v___jp_203_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_225_, 1);
v___y_204_ = v_val_226_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_205_; uint8_t v_decide_206_; 
v___x_205_ = lean_string_utf8_byte_size(v_str_202_);
v_decide_206_ = lean_nat_dec_eq(v___y_204_, v___x_205_);
if (v_decide_206_ == 0)
{
lean_object* v___x_207_; lean_object* v_suffix_208_; uint8_t v___x_209_; 
v___x_207_ = lean_string_utf8_next_fast(v_str_202_, v___y_204_);
lean_inc_ref(v_str_202_);
v_suffix_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_208_, 0, v_str_202_);
lean_ctor_set(v_suffix_208_, 1, v___x_207_);
lean_ctor_set(v_suffix_208_, 2, v___x_205_);
v___x_209_ = l_String_Slice_isNat(v_suffix_208_);
lean_dec_ref_known(v_suffix_208_, 3);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v___y_204_);
lean_dec_ref(v_type_168_);
v___x_210_ = lean_box(0);
v___x_211_ = l_Lean_Name_str___override(v___x_210_, v_str_202_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_dec_eq(v___y_204_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v_type_168_);
v___x_215_ = lean_string_utf8_extract_fast(v_str_202_, v___x_213_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v_str_202_);
v___x_216_ = lean_box(0);
v___x_217_ = l_Lean_Name_str___override(v___x_216_, v___x_215_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
else
{
lean_dec(v___y_204_);
lean_dec_ref(v_str_202_);
v___y_175_ = v_a_169_;
v___y_176_ = v_a_170_;
v___y_177_ = v_a_171_;
v___y_178_ = v_a_172_;
goto v___jp_174_;
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v___y_204_);
lean_dec_ref(v_type_168_);
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_Name_str___override(v___x_219_, v_str_202_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
}
else
{
lean_dec(v_name_167_);
v___y_175_ = v_a_169_;
v___y_176_ = v_a_170_;
v___y_177_ = v_a_171_;
v___y_178_ = v_a_172_;
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_isProp(v_type_168_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_193_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_193_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
uint8_t v___x_184_; 
v___x_184_ = lean_unbox(v_a_180_);
lean_dec(v_a_180_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_189_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_179_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_179_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_227_, lean_object* v_type_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_227_, v_type_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v_str_237_, lean_object* v_inst_238_, lean_object* v_R_239_, lean_object* v_a_240_, lean_object* v_b_241_, lean_object* v_c_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_235_, v_str_237_, v_a_240_, v_b_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_244_, lean_object* v___x_245_, lean_object* v_str_246_, lean_object* v_inst_247_, lean_object* v_R_248_, lean_object* v_a_249_, lean_object* v_b_250_, lean_object* v_c_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_244_, v___x_245_, v_str_246_, v_inst_247_, v_R_248_, v_a_249_, v_b_250_, v_c_251_);
lean_dec(v_b_250_);
lean_dec_ref(v_str_246_);
lean_dec_ref(v___x_245_);
lean_dec(v___x_244_);
return v_res_252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_253_, lean_object* v_i_254_, lean_object* v_k_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_keys_253_);
v___x_257_ = lean_nat_dec_lt(v_i_254_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec(v_i_254_);
return v___x_257_;
}
else
{
lean_object* v_k_x27_258_; uint8_t v___x_259_; 
v_k_x27_258_ = lean_array_fget_borrowed(v_keys_253_, v_i_254_);
v___x_259_ = lean_name_eq(v_k_255_, v_k_x27_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_i_254_, v___x_260_);
lean_dec(v_i_254_);
v_i_254_ = v___x_261_;
goto _start;
}
else
{
lean_dec(v_i_254_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_263_, lean_object* v_i_264_, lean_object* v_k_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_263_, v_i_264_, v_k_265_);
lean_dec(v_k_265_);
lean_dec_ref(v_keys_263_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_268_, size_t v_x_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_es_271_; lean_object* v___x_272_; size_t v___x_273_; size_t v___x_274_; lean_object* v_j_275_; lean_object* v___x_276_; 
v_es_271_ = lean_ctor_get(v_x_268_, 0);
v___x_272_ = lean_box(2);
v___x_273_ = ((size_t)31ULL);
v___x_274_ = lean_usize_land(v_x_269_, v___x_273_);
v_j_275_ = lean_usize_to_nat(v___x_274_);
v___x_276_ = lean_array_get_borrowed(v___x_272_, v_es_271_, v_j_275_);
lean_dec(v_j_275_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_key_277_; uint8_t v___x_278_; 
v_key_277_ = lean_ctor_get(v___x_276_, 0);
v___x_278_ = lean_name_eq(v_x_270_, v_key_277_);
return v___x_278_;
}
case 1:
{
lean_object* v_node_279_; size_t v___x_280_; size_t v___x_281_; 
v_node_279_ = lean_ctor_get(v___x_276_, 0);
v___x_280_ = ((size_t)5ULL);
v___x_281_ = lean_usize_shift_right(v_x_269_, v___x_280_);
v_x_268_ = v_node_279_;
v_x_269_ = v___x_281_;
goto _start;
}
default: 
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
}
else
{
lean_object* v_ks_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_ks_284_ = lean_ctor_get(v_x_268_, 0);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_284_, v___x_285_, v_x_270_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
size_t v_x_32924__boxed_290_; uint8_t v_res_291_; lean_object* v_r_292_; 
v_x_32924__boxed_290_ = lean_unbox_usize(v_x_288_);
lean_dec(v_x_288_);
v_res_291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_287_, v_x_32924__boxed_290_, v_x_289_);
lean_dec(v_x_289_);
lean_dec_ref(v_x_287_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
uint64_t v___y_296_; 
if (lean_obj_tag(v_x_294_) == 0)
{
uint64_t v___x_299_; 
v___x_299_ = 1723ULL;
v___y_296_ = v___x_299_;
goto v___jp_295_;
}
else
{
uint64_t v_hash_300_; 
v_hash_300_ = lean_ctor_get_uint64(v_x_294_, sizeof(void*)*2);
v___y_296_ = v_hash_300_;
goto v___jp_295_;
}
v___jp_295_:
{
size_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_uint64_to_usize(v___y_296_);
v___x_298_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_293_, v___x_297_, v_x_294_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_301_, v_x_302_);
lean_dec(v_x_302_);
lean_dec_ref(v_x_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_toGoalState_310_; lean_object* v_clean_311_; lean_object* v_snd_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_329_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_toGoalState_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_toGoalState_310_);
lean_dec(v___x_309_);
v_clean_311_ = lean_ctor_get(v_toGoalState_310_, 15);
lean_inc_ref(v_clean_311_);
lean_dec_ref(v_toGoalState_310_);
v_snd_312_ = lean_ctor_get(v_a_306_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_a_306_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_a_306_, 0);
lean_dec(v_unused_330_);
v___x_314_ = v_a_306_;
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_snd_312_);
lean_dec(v_a_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_329_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_used_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_used_316_ = lean_ctor_get(v_clean_311_, 0);
lean_inc_ref(v_used_316_);
lean_dec_ref(v_clean_311_);
lean_inc(v_snd_312_);
lean_inc(v_a_305_);
v___x_317_ = lean_name_append_index_after(v_a_305_, v_snd_312_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_snd_312_, v___x_318_);
lean_dec(v_snd_312_);
v___x_320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_316_, v___x_317_);
lean_dec_ref(v_used_316_);
if (v___x_320_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_a_305_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_319_);
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_319_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_319_);
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_326_ = v___x_314_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_319_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
v_a_306_ = v___x_326_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_331_, v_a_332_, v___y_333_);
lean_dec(v___y_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_ks_340_; lean_object* v_vs_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_365_; 
v_ks_340_ = lean_ctor_get(v_x_336_, 0);
v_vs_341_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_365_ == 0)
{
v___x_343_ = v_x_336_;
v_isShared_344_ = v_isSharedCheck_365_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_vs_341_);
lean_inc(v_ks_340_);
lean_dec(v_x_336_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_365_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_array_get_size(v_ks_340_);
v___x_346_ = lean_nat_dec_lt(v_x_337_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec(v_x_337_);
v___x_347_ = lean_array_push(v_ks_340_, v_x_338_);
v___x_348_ = lean_array_push(v_vs_341_, v_x_339_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_348_);
lean_ctor_set(v___x_343_, 0, v___x_347_);
v___x_350_ = v___x_343_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v_k_x27_352_; uint8_t v___x_353_; 
v_k_x27_352_ = lean_array_fget_borrowed(v_ks_340_, v_x_337_);
v___x_353_ = lean_name_eq(v_x_338_, v_k_x27_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_355_; 
if (v_isShared_344_ == 0)
{
v___x_355_ = v___x_343_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_ks_340_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_vs_341_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_x_337_, v___x_356_);
lean_dec(v_x_337_);
v_x_336_ = v___x_355_;
v_x_337_ = v___x_357_;
goto _start;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = lean_array_fset(v_ks_340_, v_x_337_, v_x_338_);
v___x_361_ = lean_array_fset(v_vs_341_, v_x_337_, v_x_339_);
lean_dec(v_x_337_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_361_);
lean_ctor_set(v___x_343_, 0, v___x_360_);
v___x_363_ = v___x_343_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_366_, lean_object* v_k_367_, lean_object* v_v_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_366_, v___x_369_, v_k_367_, v_v_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_372_, size_t v_x_373_, size_t v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_es_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v_j_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_es_377_ = lean_ctor_get(v_x_372_, 0);
v___x_378_ = ((size_t)31ULL);
v___x_379_ = lean_usize_land(v_x_373_, v___x_378_);
v_j_380_ = lean_usize_to_nat(v___x_379_);
v___x_381_ = lean_array_get_size(v_es_377_);
v___x_382_ = lean_nat_dec_lt(v_j_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v_j_380_);
lean_dec(v_x_376_);
lean_dec(v_x_375_);
return v_x_372_;
}
else
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_421_; 
lean_inc_ref(v_es_377_);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_x_372_, 0);
lean_dec(v_unused_422_);
v___x_384_ = v_x_372_;
v_isShared_385_ = v_isSharedCheck_421_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_x_372_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_421_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_v_386_; lean_object* v___x_387_; lean_object* v_xs_x27_388_; lean_object* v___y_390_; 
v_v_386_ = lean_array_fget(v_es_377_, v_j_380_);
v___x_387_ = lean_box(0);
v_xs_x27_388_ = lean_array_fset(v_es_377_, v_j_380_, v___x_387_);
switch(lean_obj_tag(v_v_386_))
{
case 0:
{
lean_object* v_key_395_; lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_406_; 
v_key_395_ = lean_ctor_get(v_v_386_, 0);
v_val_396_ = lean_ctor_get(v_v_386_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_v_386_);
if (v_isSharedCheck_406_ == 0)
{
v___x_398_ = v_v_386_;
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_inc(v_key_395_);
lean_dec(v_v_386_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = lean_name_eq(v_x_375_, v_key_395_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_del_object(v___x_398_);
v___x_401_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_395_, v_val_396_, v_x_375_, v_x_376_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___y_390_ = v___x_402_;
goto v___jp_389_;
}
else
{
lean_object* v___x_404_; 
lean_dec(v_val_396_);
lean_dec(v_key_395_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v_x_376_);
lean_ctor_set(v___x_398_, 0, v_x_375_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_375_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_376_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
v___y_390_ = v___x_404_;
goto v___jp_389_;
}
}
}
}
case 1:
{
lean_object* v_node_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v_node_407_ = lean_ctor_get(v_v_386_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_v_386_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v_v_386_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_node_407_);
lean_dec(v_v_386_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_usize_shift_right(v_x_373_, v___x_411_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_x_374_, v___x_413_);
v___x_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_407_, v___x_412_, v___x_414_, v_x_375_, v_x_376_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v___y_390_ = v___x_417_;
goto v___jp_389_;
}
}
}
default: 
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_x_375_);
lean_ctor_set(v___x_420_, 1, v_x_376_);
v___y_390_ = v___x_420_;
goto v___jp_389_;
}
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_array_fset(v_xs_x27_388_, v_j_380_, v___y_390_);
lean_dec(v_j_380_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_391_);
v___x_393_ = v___x_384_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
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
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_442_; 
v_ks_423_ = lean_ctor_get(v_x_372_, 0);
v_vs_424_ = lean_ctor_get(v_x_372_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_442_ == 0)
{
v___x_426_ = v_x_372_;
v_isShared_427_ = v_isSharedCheck_442_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_vs_424_);
lean_inc(v_ks_423_);
lean_dec(v_x_372_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_442_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_ks_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_vs_424_);
v___x_429_ = v_reuseFailAlloc_441_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v_newNode_430_; size_t v___x_431_; uint8_t v___x_432_; 
v_newNode_430_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_429_, v_x_375_, v_x_376_);
v___x_431_ = ((size_t)7ULL);
v___x_432_ = lean_usize_dec_le(v___x_431_, v_x_374_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_430_);
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
lean_dec(v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v_ks_436_; lean_object* v_vs_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_ks_436_ = lean_ctor_get(v_newNode_430_, 0);
lean_inc_ref(v_ks_436_);
v_vs_437_ = lean_ctor_get(v_newNode_430_, 1);
lean_inc_ref(v_vs_437_);
lean_dec_ref(v_newNode_430_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_374_, v_ks_436_, v_vs_437_, v___x_438_, v___x_439_);
lean_dec_ref(v_vs_437_);
lean_dec_ref(v_ks_436_);
return v___x_440_;
}
else
{
return v_newNode_430_;
}
}
else
{
return v_newNode_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_443_, lean_object* v_keys_444_, lean_object* v_vals_445_, lean_object* v_i_446_, lean_object* v_entries_447_){
_start:
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_array_get_size(v_keys_444_);
v___x_449_ = lean_nat_dec_lt(v_i_446_, v___x_448_);
if (v___x_449_ == 0)
{
lean_dec(v_i_446_);
return v_entries_447_;
}
else
{
lean_object* v_k_450_; lean_object* v_v_451_; uint64_t v___y_453_; 
v_k_450_ = lean_array_fget_borrowed(v_keys_444_, v_i_446_);
v_v_451_ = lean_array_fget_borrowed(v_vals_445_, v_i_446_);
if (lean_obj_tag(v_k_450_) == 0)
{
uint64_t v___x_464_; 
v___x_464_ = 1723ULL;
v___y_453_ = v___x_464_;
goto v___jp_452_;
}
else
{
uint64_t v_hash_465_; 
v_hash_465_ = lean_ctor_get_uint64(v_k_450_, sizeof(void*)*2);
v___y_453_ = v_hash_465_;
goto v___jp_452_;
}
v___jp_452_:
{
size_t v_h_454_; size_t v___x_455_; lean_object* v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v_h_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_h_454_ = lean_uint64_to_usize(v___y_453_);
v___x_455_ = ((size_t)5ULL);
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_sub(v_depth_443_, v___x_457_);
v___x_459_ = lean_usize_mul(v___x_455_, v___x_458_);
v_h_460_ = lean_usize_shift_right(v_h_454_, v___x_459_);
v___x_461_ = lean_nat_add(v_i_446_, v___x_456_);
lean_dec(v_i_446_);
lean_inc(v_v_451_);
lean_inc(v_k_450_);
v___x_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_447_, v_h_460_, v_depth_443_, v_k_450_, v_v_451_);
v_i_446_ = v___x_461_;
v_entries_447_ = v___x_462_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_466_, lean_object* v_keys_467_, lean_object* v_vals_468_, lean_object* v_i_469_, lean_object* v_entries_470_){
_start:
{
size_t v_depth_boxed_471_; lean_object* v_res_472_; 
v_depth_boxed_471_ = lean_unbox_usize(v_depth_466_);
lean_dec(v_depth_466_);
v_res_472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_471_, v_keys_467_, v_vals_468_, v_i_469_, v_entries_470_);
lean_dec_ref(v_vals_468_);
lean_dec_ref(v_keys_467_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
size_t v_x_33104__boxed_478_; size_t v_x_33105__boxed_479_; lean_object* v_res_480_; 
v_x_33104__boxed_478_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_x_33105__boxed_479_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_473_, v_x_33104__boxed_478_, v_x_33105__boxed_479_, v_x_476_, v_x_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
uint64_t v___y_485_; 
if (lean_obj_tag(v_x_482_) == 0)
{
uint64_t v___x_489_; 
v___x_489_ = 1723ULL;
v___y_485_ = v___x_489_;
goto v___jp_484_;
}
else
{
uint64_t v_hash_490_; 
v_hash_490_ = lean_ctor_get_uint64(v_x_482_, sizeof(void*)*2);
v___y_485_ = v_hash_490_;
goto v___jp_484_;
}
v___jp_484_:
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_uint64_to_usize(v___y_485_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_481_, v___x_486_, v___x_487_, v_x_482_, v_x_483_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_get_size(v_keys_491_);
v___x_496_ = lean_nat_dec_lt(v_i_493_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v_i_493_);
v___x_497_ = lean_box(0);
return v___x_497_;
}
else
{
lean_object* v_k_x27_498_; uint8_t v___x_499_; 
v_k_x27_498_ = lean_array_fget_borrowed(v_keys_491_, v_i_493_);
v___x_499_ = lean_name_eq(v_k_494_, v_k_x27_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_i_493_, v___x_500_);
lean_dec(v_i_493_);
v_i_493_ = v___x_501_;
goto _start;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_array_fget_borrowed(v_vals_492_, v_i_493_);
lean_dec(v_i_493_);
lean_inc(v___x_503_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_i_507_, lean_object* v_k_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_505_, v_vals_506_, v_i_507_, v_k_508_);
lean_dec(v_k_508_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_510_, size_t v_x_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v_es_513_; lean_object* v___x_514_; size_t v___x_515_; size_t v___x_516_; lean_object* v_j_517_; lean_object* v___x_518_; 
v_es_513_ = lean_ctor_get(v_x_510_, 0);
v___x_514_ = lean_box(2);
v___x_515_ = ((size_t)31ULL);
v___x_516_ = lean_usize_land(v_x_511_, v___x_515_);
v_j_517_ = lean_usize_to_nat(v___x_516_);
v___x_518_ = lean_array_get_borrowed(v___x_514_, v_es_513_, v_j_517_);
lean_dec(v_j_517_);
switch(lean_obj_tag(v___x_518_))
{
case 0:
{
lean_object* v_key_519_; lean_object* v_val_520_; uint8_t v___x_521_; 
v_key_519_ = lean_ctor_get(v___x_518_, 0);
v_val_520_ = lean_ctor_get(v___x_518_, 1);
v___x_521_ = lean_name_eq(v_x_512_, v_key_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
lean_inc(v_val_520_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_val_520_);
return v___x_523_;
}
}
case 1:
{
lean_object* v_node_524_; size_t v___x_525_; size_t v___x_526_; 
v_node_524_ = lean_ctor_get(v___x_518_, 0);
v___x_525_ = ((size_t)5ULL);
v___x_526_ = lean_usize_shift_right(v_x_511_, v___x_525_);
v_x_510_ = v_node_524_;
v_x_511_ = v___x_526_;
goto _start;
}
default: 
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
}
else
{
lean_object* v_ks_529_; lean_object* v_vs_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_ks_529_ = lean_ctor_get(v_x_510_, 0);
v_vs_530_ = lean_ctor_get(v_x_510_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_529_, v_vs_530_, v___x_531_, v_x_512_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
size_t v_x_33294__boxed_536_; lean_object* v_res_537_; 
v_x_33294__boxed_536_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_537_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_533_, v_x_33294__boxed_536_, v_x_535_);
lean_dec(v_x_535_);
lean_dec_ref(v_x_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint64_t v___y_541_; 
if (lean_obj_tag(v_x_539_) == 0)
{
uint64_t v___x_544_; 
v___x_544_ = 1723ULL;
v___y_541_ = v___x_544_;
goto v___jp_540_;
}
else
{
uint64_t v_hash_545_; 
v_hash_545_ = lean_ctor_get_uint64(v_x_539_, sizeof(void*)*2);
v___y_541_ = v_hash_545_;
goto v___jp_540_;
}
v___jp_540_:
{
size_t v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_uint64_to_usize(v___y_541_);
v___x_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_538_, v___x_542_, v_x_539_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_546_, v_x_547_);
lean_dec(v_x_547_);
lean_dec_ref(v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_552_, lean_object* v_type_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_name_566_; lean_object* v___y_567_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v_name_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_556_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_780_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_780_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_780_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_780_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v_clean_745_; 
v_clean_745_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*14 + 16);
lean_dec(v_a_720_);
if (v_clean_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_552_);
if (lean_obj_tag(v___x_746_) == 1)
{
lean_object* v_val_747_; lean_object* v___x_749_; 
lean_dec_ref(v_type_553_);
lean_dec(v_name_552_);
v_val_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_746_, 1);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_val_747_);
v___x_749_ = v___x_722_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_val_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
uint8_t v___x_751_; 
lean_dec(v___x_746_);
v___x_751_ = l_Lean_Name_hasMacroScopes(v_name_552_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_type_553_);
v___x_752_ = l_Lean_Core_mkFreshUserName(v_name_552_, v_a_562_, v_a_563_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = l_Lean_Name_eraseMacroScopes(v_name_552_);
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_755_ = lean_name_eq(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_757_ = lean_name_eq(v___x_753_, v___x_756_);
lean_dec(v___x_753_);
if (v___x_757_ == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v_type_553_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_name_552_);
v___x_759_ = v___x_722_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_name_552_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_del_object(v___x_722_);
goto v___jp_724_;
}
}
else
{
lean_dec(v___x_753_);
lean_del_object(v___x_722_);
goto v___jp_724_;
}
}
}
}
else
{
uint8_t v___x_761_; 
lean_del_object(v___x_722_);
v___x_761_ = l_Lean_Name_hasMacroScopes(v_name_552_);
if (v___x_761_ == 0)
{
v_name_694_ = v_name_552_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
goto v___jp_693_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_762_ = l_Lean_Name_eraseMacroScopes(v_name_552_);
lean_dec(v_name_552_);
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_777_ = lean_name_eq(v___x_762_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_779_ = lean_name_eq(v___x_762_, v___x_778_);
if (v___x_779_ == 0)
{
v_name_694_ = v___x_762_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
goto v___jp_693_;
}
else
{
goto v___jp_763_;
}
}
else
{
goto v___jp_763_;
}
v___jp_763_:
{
lean_object* v___x_764_; 
lean_inc_ref(v_type_553_);
v___x_764_ = l_Lean_Meta_isProp(v_type_553_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; uint8_t v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = lean_unbox(v_a_765_);
lean_dec(v_a_765_);
if (v___x_766_ == 0)
{
v_name_694_ = v___x_762_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
goto v___jp_693_;
}
else
{
lean_object* v___x_767_; 
lean_dec(v___x_762_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_694_ = v___x_767_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
v___y_702_ = v_a_561_;
v___y_703_ = v_a_562_;
v___y_704_ = v_a_563_;
goto v___jp_693_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v___x_762_);
lean_dec_ref(v_type_553_);
v_a_768_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_764_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
v___jp_724_:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_isProp(v_type_553_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_736_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_736_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_736_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; 
v___x_730_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
if (v___x_730_ == 0)
{
lean_object* v___x_732_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_name_552_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_name_552_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_del_object(v___x_728_);
lean_dec(v_name_552_);
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_735_ = l_Lean_Core_mkFreshUserName(v___x_734_, v_a_562_, v_a_563_);
return v___x_735_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_name_552_);
v_a_737_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_725_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_725_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_type_553_);
lean_dec(v_name_552_);
v_a_781_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_719_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_719_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
v___jp_565_:
{
lean_object* v___x_568_; lean_object* v_toGoalState_569_; lean_object* v_clean_570_; lean_object* v_mvarId_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_616_; 
v___x_568_ = lean_st_ref_take(v___y_567_);
v_toGoalState_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_toGoalState_569_);
v_clean_570_ = lean_ctor_get(v_toGoalState_569_, 15);
lean_inc_ref(v_clean_570_);
v_mvarId_571_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_568_, 0);
lean_dec(v_unused_617_);
v___x_573_ = v___x_568_;
v_isShared_574_ = v_isSharedCheck_616_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_mvarId_571_);
lean_dec(v___x_568_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_616_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_nextDeclIdx_575_; lean_object* v_enodeMap_576_; lean_object* v_exprs_577_; lean_object* v_parents_578_; lean_object* v_congrTable_579_; lean_object* v_appMap_580_; lean_object* v_indicesFound_581_; lean_object* v_newFacts_582_; uint8_t v_inconsistent_583_; lean_object* v_nextIdx_584_; lean_object* v_newRawFacts_585_; lean_object* v_facts_586_; lean_object* v_extThms_587_; lean_object* v_ematch_588_; lean_object* v_inj_589_; lean_object* v_split_590_; lean_object* v_sstates_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_nextDeclIdx_575_ = lean_ctor_get(v_toGoalState_569_, 0);
v_enodeMap_576_ = lean_ctor_get(v_toGoalState_569_, 1);
v_exprs_577_ = lean_ctor_get(v_toGoalState_569_, 2);
v_parents_578_ = lean_ctor_get(v_toGoalState_569_, 3);
v_congrTable_579_ = lean_ctor_get(v_toGoalState_569_, 4);
v_appMap_580_ = lean_ctor_get(v_toGoalState_569_, 5);
v_indicesFound_581_ = lean_ctor_get(v_toGoalState_569_, 6);
v_newFacts_582_ = lean_ctor_get(v_toGoalState_569_, 7);
v_inconsistent_583_ = lean_ctor_get_uint8(v_toGoalState_569_, sizeof(void*)*17);
v_nextIdx_584_ = lean_ctor_get(v_toGoalState_569_, 8);
v_newRawFacts_585_ = lean_ctor_get(v_toGoalState_569_, 9);
v_facts_586_ = lean_ctor_get(v_toGoalState_569_, 10);
v_extThms_587_ = lean_ctor_get(v_toGoalState_569_, 11);
v_ematch_588_ = lean_ctor_get(v_toGoalState_569_, 12);
v_inj_589_ = lean_ctor_get(v_toGoalState_569_, 13);
v_split_590_ = lean_ctor_get(v_toGoalState_569_, 14);
v_sstates_591_ = lean_ctor_get(v_toGoalState_569_, 16);
v_isSharedCheck_614_ = !lean_is_exclusive(v_toGoalState_569_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_toGoalState_569_, 15);
lean_dec(v_unused_615_);
v___x_593_ = v_toGoalState_569_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_sstates_591_);
lean_inc(v_split_590_);
lean_inc(v_inj_589_);
lean_inc(v_ematch_588_);
lean_inc(v_extThms_587_);
lean_inc(v_facts_586_);
lean_inc(v_newRawFacts_585_);
lean_inc(v_nextIdx_584_);
lean_inc(v_newFacts_582_);
lean_inc(v_indicesFound_581_);
lean_inc(v_appMap_580_);
lean_inc(v_congrTable_579_);
lean_inc(v_parents_578_);
lean_inc(v_exprs_577_);
lean_inc(v_enodeMap_576_);
lean_inc(v_nextDeclIdx_575_);
lean_dec(v_toGoalState_569_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_used_595_; lean_object* v_next_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_613_; 
v_used_595_ = lean_ctor_get(v_clean_570_, 0);
v_next_596_ = lean_ctor_get(v_clean_570_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_clean_570_);
if (v_isSharedCheck_613_ == 0)
{
v___x_598_ = v_clean_570_;
v_isShared_599_ = v_isSharedCheck_613_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_next_596_);
lean_inc(v_used_595_);
lean_dec(v_clean_570_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_613_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_box(0);
lean_inc(v_name_566_);
v___x_601_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_595_, v_name_566_, v___x_600_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_next_596_);
v___x_603_ = v_reuseFailAlloc_612_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 15, v___x_603_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_nextDeclIdx_575_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_enodeMap_576_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_exprs_577_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_parents_578_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_congrTable_579_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_appMap_580_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_indicesFound_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_newFacts_582_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_nextIdx_584_);
lean_ctor_set(v_reuseFailAlloc_611_, 9, v_newRawFacts_585_);
lean_ctor_set(v_reuseFailAlloc_611_, 10, v_facts_586_);
lean_ctor_set(v_reuseFailAlloc_611_, 11, v_extThms_587_);
lean_ctor_set(v_reuseFailAlloc_611_, 12, v_ematch_588_);
lean_ctor_set(v_reuseFailAlloc_611_, 13, v_inj_589_);
lean_ctor_set(v_reuseFailAlloc_611_, 14, v_split_590_);
lean_ctor_set(v_reuseFailAlloc_611_, 15, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_611_, 16, v_sstates_591_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*17, v_inconsistent_583_);
v___x_605_ = v_reuseFailAlloc_611_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_605_);
v___x_607_ = v___x_573_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_mvarId_571_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_st_ref_put(v___y_567_, v___x_607_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_name_566_);
return v___x_609_;
}
}
}
}
}
}
}
v___jp_618_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_629_);
lean_ctor_set(v___x_632_, 1, v___y_631_);
lean_inc(v___y_620_);
v___x_633_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_620_, v___x_632_, v___y_624_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v_toGoalState_636_; lean_object* v_clean_637_; lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v_mvarId_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_683_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = lean_st_ref_take(v___y_624_);
v_toGoalState_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_toGoalState_636_);
v_clean_637_ = lean_ctor_get(v_toGoalState_636_, 15);
lean_inc_ref(v_clean_637_);
v_fst_638_ = lean_ctor_get(v_a_634_, 0);
lean_inc(v_fst_638_);
v_snd_639_ = lean_ctor_get(v_a_634_, 1);
lean_inc(v_snd_639_);
lean_dec(v_a_634_);
v_mvarId_640_ = lean_ctor_get(v___x_635_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_684_);
v___x_642_ = v___x_635_;
v_isShared_643_ = v_isSharedCheck_683_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_mvarId_640_);
lean_dec(v___x_635_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_683_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_nextDeclIdx_644_; lean_object* v_enodeMap_645_; lean_object* v_exprs_646_; lean_object* v_parents_647_; lean_object* v_congrTable_648_; lean_object* v_appMap_649_; lean_object* v_indicesFound_650_; lean_object* v_newFacts_651_; uint8_t v_inconsistent_652_; lean_object* v_nextIdx_653_; lean_object* v_newRawFacts_654_; lean_object* v_facts_655_; lean_object* v_extThms_656_; lean_object* v_ematch_657_; lean_object* v_inj_658_; lean_object* v_split_659_; lean_object* v_sstates_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_681_; 
v_nextDeclIdx_644_ = lean_ctor_get(v_toGoalState_636_, 0);
v_enodeMap_645_ = lean_ctor_get(v_toGoalState_636_, 1);
v_exprs_646_ = lean_ctor_get(v_toGoalState_636_, 2);
v_parents_647_ = lean_ctor_get(v_toGoalState_636_, 3);
v_congrTable_648_ = lean_ctor_get(v_toGoalState_636_, 4);
v_appMap_649_ = lean_ctor_get(v_toGoalState_636_, 5);
v_indicesFound_650_ = lean_ctor_get(v_toGoalState_636_, 6);
v_newFacts_651_ = lean_ctor_get(v_toGoalState_636_, 7);
v_inconsistent_652_ = lean_ctor_get_uint8(v_toGoalState_636_, sizeof(void*)*17);
v_nextIdx_653_ = lean_ctor_get(v_toGoalState_636_, 8);
v_newRawFacts_654_ = lean_ctor_get(v_toGoalState_636_, 9);
v_facts_655_ = lean_ctor_get(v_toGoalState_636_, 10);
v_extThms_656_ = lean_ctor_get(v_toGoalState_636_, 11);
v_ematch_657_ = lean_ctor_get(v_toGoalState_636_, 12);
v_inj_658_ = lean_ctor_get(v_toGoalState_636_, 13);
v_split_659_ = lean_ctor_get(v_toGoalState_636_, 14);
v_sstates_660_ = lean_ctor_get(v_toGoalState_636_, 16);
v_isSharedCheck_681_ = !lean_is_exclusive(v_toGoalState_636_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_toGoalState_636_, 15);
lean_dec(v_unused_682_);
v___x_662_ = v_toGoalState_636_;
v_isShared_663_ = v_isSharedCheck_681_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_sstates_660_);
lean_inc(v_split_659_);
lean_inc(v_inj_658_);
lean_inc(v_ematch_657_);
lean_inc(v_extThms_656_);
lean_inc(v_facts_655_);
lean_inc(v_newRawFacts_654_);
lean_inc(v_nextIdx_653_);
lean_inc(v_newFacts_651_);
lean_inc(v_indicesFound_650_);
lean_inc(v_appMap_649_);
lean_inc(v_congrTable_648_);
lean_inc(v_parents_647_);
lean_inc(v_exprs_646_);
lean_inc(v_enodeMap_645_);
lean_inc(v_nextDeclIdx_644_);
lean_dec(v_toGoalState_636_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_681_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_used_664_; lean_object* v_next_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_680_; 
v_used_664_ = lean_ctor_get(v_clean_637_, 0);
v_next_665_ = lean_ctor_get(v_clean_637_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_clean_637_);
if (v_isSharedCheck_680_ == 0)
{
v___x_667_ = v_clean_637_;
v_isShared_668_ = v_isSharedCheck_680_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_next_665_);
lean_inc(v_used_664_);
lean_dec(v_clean_637_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_680_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_665_, v___y_620_, v_snd_639_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_used_664_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_679_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 15, v___x_671_);
v___x_673_ = v___x_662_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_nextDeclIdx_644_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_enodeMap_645_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_exprs_646_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_parents_647_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_congrTable_648_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v_appMap_649_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_indicesFound_650_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_newFacts_651_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_nextIdx_653_);
lean_ctor_set(v_reuseFailAlloc_678_, 9, v_newRawFacts_654_);
lean_ctor_set(v_reuseFailAlloc_678_, 10, v_facts_655_);
lean_ctor_set(v_reuseFailAlloc_678_, 11, v_extThms_656_);
lean_ctor_set(v_reuseFailAlloc_678_, 12, v_ematch_657_);
lean_ctor_set(v_reuseFailAlloc_678_, 13, v_inj_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 14, v_split_659_);
lean_ctor_set(v_reuseFailAlloc_678_, 15, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 16, v_sstates_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_678_, sizeof(void*)*17, v_inconsistent_652_);
v___x_673_ = v_reuseFailAlloc_678_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_673_);
v___x_675_ = v___x_642_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_mvarId_640_);
v___x_675_ = v_reuseFailAlloc_677_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; 
v___x_676_ = lean_st_ref_put(v___y_624_, v___x_675_);
v_name_566_ = v_fst_638_;
v___y_567_ = v___y_624_;
goto v___jp_565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v___y_620_);
v_a_685_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_633_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_633_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
v___jp_693_:
{
lean_object* v___x_705_; lean_object* v_toGoalState_706_; lean_object* v_clean_707_; lean_object* v_used_708_; uint8_t v___x_709_; 
v___x_705_ = lean_st_ref_get(v___y_695_);
v_toGoalState_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref(v_toGoalState_706_);
lean_dec(v___x_705_);
v_clean_707_ = lean_ctor_get(v_toGoalState_706_, 15);
lean_inc_ref(v_clean_707_);
lean_dec_ref(v_toGoalState_706_);
v_used_708_ = lean_ctor_get(v_clean_707_, 0);
lean_inc_ref(v_used_708_);
lean_dec_ref(v_clean_707_);
v___x_709_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_708_, v_name_694_);
lean_dec_ref(v_used_708_);
if (v___x_709_ == 0)
{
lean_dec_ref(v_type_553_);
v_name_566_ = v_name_694_;
v___y_567_ = v___y_695_;
goto v___jp_565_;
}
else
{
lean_object* v___x_710_; 
lean_inc(v_name_694_);
v___x_710_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_694_, v_type_553_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v_toGoalState_713_; lean_object* v_clean_714_; lean_object* v_next_715_; lean_object* v___x_716_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_st_ref_get(v___y_695_);
v_toGoalState_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_toGoalState_713_);
lean_dec(v___x_712_);
v_clean_714_ = lean_ctor_get(v_toGoalState_713_, 15);
lean_inc_ref(v_clean_714_);
lean_dec_ref(v_toGoalState_713_);
v_next_715_ = lean_ctor_get(v_clean_714_, 1);
lean_inc_ref(v_next_715_);
lean_dec_ref(v_clean_714_);
v___x_716_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_715_, v_a_711_);
lean_dec_ref(v_next_715_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v___x_716_, 1);
v___y_619_ = v___y_702_;
v___y_620_ = v_a_711_;
v___y_621_ = v___y_704_;
v___y_622_ = v___y_701_;
v___y_623_ = v___y_696_;
v___y_624_ = v___y_695_;
v___y_625_ = v___y_703_;
v___y_626_ = v___y_698_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_697_;
v___y_629_ = v_name_694_;
v___y_630_ = v___y_700_;
v___y_631_ = v_val_717_;
goto v___jp_618_;
}
else
{
lean_object* v___x_718_; 
lean_dec(v___x_716_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___y_619_ = v___y_702_;
v___y_620_ = v_a_711_;
v___y_621_ = v___y_704_;
v___y_622_ = v___y_701_;
v___y_623_ = v___y_696_;
v___y_624_ = v___y_695_;
v___y_625_ = v___y_703_;
v___y_626_ = v___y_698_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_697_;
v___y_629_ = v_name_694_;
v___y_630_ = v___y_700_;
v___y_631_ = v___x_718_;
goto v___jp_618_;
}
}
else
{
lean_dec(v_name_694_);
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_789_, lean_object* v_type_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_789_, v_type_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_804_, v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_812_, v_x_813_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_x_813_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_817_, lean_object* v_inst_818_, lean_object* v_a_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_817_, v_a_819_, v___y_820_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_832_, lean_object* v_inst_833_, lean_object* v_a_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_832_, v_inst_833_, v_a_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v___y_835_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_851_, v_x_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, size_t v_x_857_, size_t v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
size_t v_x_33788__boxed_868_; size_t v_x_33789__boxed_869_; lean_object* v_res_870_; 
v_x_33788__boxed_868_ = lean_unbox_usize(v_x_864_);
lean_dec(v_x_864_);
v_x_33789__boxed_869_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_res_870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_862_, v_x_863_, v_x_33788__boxed_868_, v_x_33789__boxed_869_, v_x_866_, v_x_867_);
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, size_t v_x_873_, lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_872_, v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_33805__boxed_880_; uint8_t v_res_881_; lean_object* v_r_882_; 
v_x_33805__boxed_880_ = lean_unbox_usize(v_x_878_);
lean_dec(v_x_878_);
v_res_881_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_876_, v_x_877_, v_x_33805__boxed_880_, v_x_879_);
lean_dec(v_x_879_);
lean_dec_ref(v_x_877_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, size_t v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_884_, v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
size_t v_x_33816__boxed_892_; lean_object* v_res_893_; 
v_x_33816__boxed_892_ = lean_unbox_usize(v_x_890_);
lean_dec(v_x_890_);
v_res_893_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_888_, v_x_889_, v_x_33816__boxed_892_, v_x_891_);
lean_dec(v_x_891_);
lean_dec_ref(v_x_889_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_894_, lean_object* v_n_895_, lean_object* v_k_896_, lean_object* v_v_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_895_, v_k_896_, v_v_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_899_, size_t v_depth_900_, lean_object* v_keys_901_, lean_object* v_vals_902_, lean_object* v_heq_903_, lean_object* v_i_904_, lean_object* v_entries_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_900_, v_keys_901_, v_vals_902_, v_i_904_, v_entries_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_907_, lean_object* v_depth_908_, lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_heq_911_, lean_object* v_i_912_, lean_object* v_entries_913_){
_start:
{
size_t v_depth_boxed_914_; lean_object* v_res_915_; 
v_depth_boxed_914_ = lean_unbox_usize(v_depth_908_);
lean_dec(v_depth_908_);
v_res_915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_907_, v_depth_boxed_914_, v_keys_909_, v_vals_910_, v_heq_911_, v_i_912_, v_entries_913_);
lean_dec_ref(v_vals_910_);
lean_dec_ref(v_keys_909_);
return v_res_915_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_heq_919_, lean_object* v_i_920_, lean_object* v_k_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_917_, v_i_920_, v_k_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_heq_926_, lean_object* v_i_927_, lean_object* v_k_928_){
_start:
{
uint8_t v_res_929_; lean_object* v_r_930_; 
v_res_929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_923_, v_keys_924_, v_vals_925_, v_heq_926_, v_i_927_, v_k_928_);
lean_dec(v_k_928_);
lean_dec_ref(v_vals_925_);
lean_dec_ref(v_keys_924_);
v_r_930_ = lean_box(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_heq_934_, lean_object* v_i_935_, lean_object* v_k_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_932_, v_vals_933_, v_i_935_, v_k_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_938_, lean_object* v_keys_939_, lean_object* v_vals_940_, lean_object* v_heq_941_, lean_object* v_i_942_, lean_object* v_k_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_938_, v_keys_939_, v_vals_940_, v_heq_941_, v_i_942_, v_k_943_);
lean_dec(v_k_943_);
lean_dec_ref(v_vals_940_);
lean_dec_ref(v_keys_939_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_946_, v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v___x_959_; lean_object* v_mctx_960_; lean_object* v_lctx_961_; lean_object* v_options_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_957_ = lean_st_ref_get(v___y_955_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v___x_959_ = lean_st_ref_get(v___y_953_);
v_mctx_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_mctx_960_);
lean_dec(v___x_959_);
v_lctx_961_ = lean_ctor_get(v___y_952_, 2);
v_options_962_ = lean_ctor_get(v___y_954_, 1);
lean_inc_ref(v_options_962_);
lean_inc_ref(v_lctx_961_);
v___x_963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_963_, 0, v_env_958_);
lean_ctor_set(v___x_963_, 1, v_mctx_960_);
lean_ctor_set(v___x_963_, 2, v_lctx_961_);
lean_ctor_set(v___x_963_, 3, v_options_962_);
v___x_964_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_msgData_951_);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_ref_979_; lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
v_ref_979_ = lean_ctor_get(v___y_976_, 4);
v___x_980_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_989_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_inc(v_ref_979_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_ref_979_);
lean_ctor_set(v___x_985_, 1, v_a_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 1);
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___x_1066_; lean_object* v_mvarId_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_st_ref_get(v_a_1000_);
v_mvarId_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_mvarId_1067_);
lean_dec(v___x_1066_);
v___x_1068_ = l_Lean_MVarId_getType(v_mvarId_1067_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
switch(lean_obj_tag(v_a_1069_))
{
case 7:
{
lean_object* v_binderName_1070_; lean_object* v_binderType_1071_; 
v_binderName_1070_ = lean_ctor_get(v_a_1069_, 0);
lean_inc(v_binderName_1070_);
v_binderType_1071_ = lean_ctor_get(v_a_1069_, 1);
lean_inc_ref(v_binderType_1071_);
lean_dec_ref_known(v_a_1069_, 3);
v_fst_1012_ = v_binderName_1070_;
v_snd_1013_ = v_binderType_1071_;
v___y_1014_ = v_a_1000_;
v___y_1015_ = v_a_1001_;
v___y_1016_ = v_a_1002_;
v___y_1017_ = v_a_1003_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
goto v___jp_1011_;
}
case 8:
{
lean_object* v_declName_1072_; lean_object* v_type_1073_; 
v_declName_1072_ = lean_ctor_get(v_a_1069_, 0);
lean_inc(v_declName_1072_);
v_type_1073_ = lean_ctor_get(v_a_1069_, 1);
lean_inc_ref(v_type_1073_);
lean_dec_ref_known(v_a_1069_, 4);
v_fst_1012_ = v_declName_1072_;
v_snd_1013_ = v_type_1073_;
v___y_1014_ = v_a_1000_;
v___y_1015_ = v_a_1001_;
v___y_1016_ = v_a_1002_;
v___y_1017_ = v_a_1003_;
v___y_1018_ = v_a_1004_;
v___y_1019_ = v_a_1005_;
v___y_1020_ = v_a_1006_;
v___y_1021_ = v_a_1007_;
v___y_1022_ = v_a_1008_;
v___y_1023_ = v_a_1009_;
goto v___jp_1011_;
}
default: 
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1069_);
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1075_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1074_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1068_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1068_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
v___jp_1011_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1012_, v_snd_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v_mvarId_1027_; lean_object* v___x_1028_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = lean_st_ref_get(v___y_1014_);
v_mvarId_1027_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_mvarId_1027_);
lean_dec(v___x_1026_);
v___x_1028_ = l_Lean_MVarId_intro(v_mvarId_1027_, v_a_1025_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1049_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1049_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1049_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1035_; lean_object* v_toGoalState_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1047_; 
v_fst_1033_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_fst_1033_);
v_snd_1034_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_snd_1034_);
lean_dec(v_a_1029_);
v___x_1035_ = lean_st_ref_take(v___y_1014_);
v_toGoalState_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v___x_1035_, 1);
lean_dec(v_unused_1048_);
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_toGoalState_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_snd_1034_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_toGoalState_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1034_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_st_ref_put(v___y_1014_, v___x_1041_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_fst_1033_);
v___x_1044_ = v___x_1031_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_fst_1033_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1028_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1028_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1024_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1024_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec(v_a_1092_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1104_, lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1105_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1118_, v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___y_1120_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1134_);
lean_inc(v___y_1133_);
v___x_1144_ = lean_apply_11(v_x_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, lean_box(0));
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1146_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc(v___y_1160_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1171_, 0, v_x_1159_);
lean_closure_set(v___f_1171_, 1, v___y_1160_);
lean_closure_set(v___f_1171_, 2, v___y_1161_);
lean_closure_set(v___f_1171_, 3, v___y_1162_);
lean_closure_set(v___f_1171_, 4, v___y_1163_);
lean_closure_set(v___f_1171_, 5, v___y_1164_);
lean_closure_set(v___f_1171_, 6, v___y_1165_);
v___x_1172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1158_, v___f_1171_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1172_) == 0)
{
return v___x_1172_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1195_, lean_object* v_mvarId_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1196_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_mvarId_1211_, lean_object* v_x_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1210_, v_mvarId_1211_, v_x_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1227_);
lean_inc(v___y_1226_);
v___x_1236_ = lean_apply_10(v_x_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, lean_box(0));
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; 
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1261_, 0, v_x_1250_);
lean_closure_set(v___f_1261_, 1, v___y_1251_);
lean_closure_set(v___f_1261_, 2, v___y_1252_);
lean_closure_set(v___f_1261_, 3, v___y_1253_);
lean_closure_set(v___f_1261_, 4, v___y_1254_);
lean_closure_set(v___f_1261_, 5, v___y_1255_);
v___x_1262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1249_, v___f_1261_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
return v___x_1262_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1271_, v_x_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1284_, lean_object* v_mvarId_1285_, lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1285_, v_x_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_mvarId_1299_, lean_object* v_x_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1298_, v_mvarId_1299_, v_x_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1312_, lean_object* v_generation_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
lean_inc(v_a_1312_);
v___x_1325_ = l_Lean_FVarId_getDecl___redArg(v_a_1312_, v___y_1320_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = l_Lean_LocalDecl_type(v_a_1326_);
lean_dec(v_a_1326_);
lean_inc_ref(v___x_1327_);
v___x_1328_ = l_Lean_Meta_isProp(v___x_1327_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; uint8_t v___x_1330_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_unbox(v_a_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec_ref(v___x_1327_);
lean_inc(v_a_1312_);
v___x_1331_ = l_Lean_FVarId_getDecl___redArg(v_a_1312_, v___y_1320_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1333_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
v___x_1334_ = l_Lean_LocalDecl_value(v_a_1332_, v___x_1333_);
lean_dec(v_a_1332_);
v___x_1335_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1334_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
lean_inc(v_a_1312_);
v___x_1337_ = l_Lean_mkFVar(v_a_1312_);
v___x_1338_ = l_Lean_Meta_Sym_shareCommon(v___x_1337_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
lean_inc(v_a_1336_);
v___x_1340_ = l_Lean_Meta_Simp_Result_getProof(v_a_1336_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v_expr_1342_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v_expr_1342_ = lean_ctor_get(v_a_1336_, 0);
lean_inc_ref(v_expr_1342_);
lean_dec(v_a_1336_);
v___x_1343_ = l_Lean_Meta_Grind_addNewEq(v_a_1339_, v_expr_1342_, v_a_1341_, v_generation_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1352_; 
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v___x_1343_, 0);
lean_dec(v_unused_1353_);
v___x_1345_ = v___x_1343_;
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v___x_1343_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_st_ref_get(v___y_1314_);
v___x_1348_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1312_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_a_1312_);
v_a_1354_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1343_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1343_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1339_);
lean_dec(v_a_1336_);
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1362_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1340_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1340_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1336_);
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1370_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1338_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1338_);
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
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1378_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1335_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1335_);
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
lean_dec(v_a_1329_);
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1386_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1331_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1331_);
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
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_a_1329_);
lean_dec(v_generation_1313_);
v___x_1394_ = lean_st_ref_get(v___y_1314_);
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1327_);
v___x_1396_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1395_, v___x_1327_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v_mvarId_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v_mvarId_1398_ = lean_ctor_get(v___x_1394_, 1);
lean_inc(v_mvarId_1398_);
lean_dec(v___x_1394_);
v___x_1399_ = l_Lean_mkFVar(v_a_1312_);
v___x_1400_ = l_Lean_MVarId_assert(v_mvarId_1398_, v_a_1397_, v___x_1327_, v___x_1399_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1419_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1419_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1419_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v_toGoalState_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1417_; 
v___x_1405_ = lean_st_ref_get(v___y_1314_);
v_toGoalState_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v___x_1405_, 1);
lean_dec(v_unused_1418_);
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_toGoalState_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1417_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_a_1401_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_toGoalState_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1401_);
v___x_1411_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1412_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1420_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1400_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1400_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v___x_1394_);
lean_dec_ref(v___x_1327_);
lean_dec(v_a_1312_);
v_a_1428_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1396_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1396_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___x_1327_);
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1436_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1328_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1328_);
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
lean_dec(v_generation_1313_);
lean_dec(v_a_1312_);
v_a_1444_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1325_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1325_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1452_, lean_object* v_generation_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1452_, v_generation_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec(v___y_1454_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
lean_object* v_ks_1470_; lean_object* v_vs_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1495_; 
v_ks_1470_ = lean_ctor_get(v_x_1466_, 0);
v_vs_1471_ = lean_ctor_get(v_x_1466_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1473_ = v_x_1466_;
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_vs_1471_);
lean_inc(v_ks_1470_);
lean_dec(v_x_1466_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_array_get_size(v_ks_1470_);
v___x_1476_ = lean_nat_dec_lt(v_x_1467_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v_x_1467_);
v___x_1477_ = lean_array_push(v_ks_1470_, v_x_1468_);
v___x_1478_ = lean_array_push(v_vs_1471_, v_x_1469_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1478_);
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1480_ = v___x_1473_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
lean_object* v_k_x27_1482_; uint8_t v___x_1483_; 
v_k_x27_1482_ = lean_array_fget_borrowed(v_ks_1470_, v_x_1467_);
v___x_1483_ = l_Lean_instBEqMVarId_beq(v_x_1468_, v_k_x27_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1485_; 
if (v_isShared_1474_ == 0)
{
v___x_1485_ = v___x_1473_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_ks_1470_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_vs_1471_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v_x_1467_, v___x_1486_);
lean_dec(v_x_1467_);
v_x_1466_ = v___x_1485_;
v_x_1467_ = v___x_1487_;
goto _start;
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_array_fset(v_ks_1470_, v_x_1467_, v_x_1468_);
v___x_1491_ = lean_array_fset(v_vs_1471_, v_x_1467_, v_x_1469_);
lean_dec(v_x_1467_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1491_);
lean_ctor_set(v___x_1473_, 0, v___x_1490_);
v___x_1493_ = v___x_1473_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1496_, lean_object* v_k_1497_, lean_object* v_v_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1496_, v___x_1499_, v_k_1497_, v_v_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1501_, size_t v_x_1502_, size_t v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_es_1506_; size_t v___x_1507_; size_t v___x_1508_; lean_object* v_j_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_es_1506_ = lean_ctor_get(v_x_1501_, 0);
v___x_1507_ = ((size_t)31ULL);
v___x_1508_ = lean_usize_land(v_x_1502_, v___x_1507_);
v_j_1509_ = lean_usize_to_nat(v___x_1508_);
v___x_1510_ = lean_array_get_size(v_es_1506_);
v___x_1511_ = lean_nat_dec_lt(v_j_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v_j_1509_);
lean_dec(v_x_1505_);
lean_dec(v_x_1504_);
return v_x_1501_;
}
else
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1550_; 
lean_inc_ref(v_es_1506_);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_x_1501_, 0);
lean_dec(v_unused_1551_);
v___x_1513_ = v_x_1501_;
v_isShared_1514_ = v_isSharedCheck_1550_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v_x_1501_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1550_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_v_1515_; lean_object* v___x_1516_; lean_object* v_xs_x27_1517_; lean_object* v___y_1519_; 
v_v_1515_ = lean_array_fget(v_es_1506_, v_j_1509_);
v___x_1516_ = lean_box(0);
v_xs_x27_1517_ = lean_array_fset(v_es_1506_, v_j_1509_, v___x_1516_);
switch(lean_obj_tag(v_v_1515_))
{
case 0:
{
lean_object* v_key_1524_; lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1535_; 
v_key_1524_ = lean_ctor_get(v_v_1515_, 0);
v_val_1525_ = lean_ctor_get(v_v_1515_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_v_1515_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1527_ = v_v_1515_;
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_inc(v_key_1524_);
lean_dec(v_v_1515_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1535_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_instBEqMVarId_beq(v_x_1504_, v_key_1524_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1527_);
v___x_1530_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1524_, v_val_1525_, v_x_1504_, v_x_1505_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___y_1519_ = v___x_1531_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_val_1525_);
lean_dec(v_key_1524_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_x_1505_);
lean_ctor_set(v___x_1527_, 0, v_x_1504_);
v___x_1533_ = v___x_1527_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_x_1504_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_x_1505_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
v___y_1519_ = v___x_1533_;
goto v___jp_1518_;
}
}
}
}
case 1:
{
lean_object* v_node_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1548_; 
v_node_1536_ = lean_ctor_get(v_v_1515_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_v_1515_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1538_ = v_v_1515_;
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_node_1536_);
lean_dec(v_v_1515_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1540_ = ((size_t)5ULL);
v___x_1541_ = lean_usize_shift_right(v_x_1502_, v___x_1540_);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_add(v_x_1503_, v___x_1542_);
v___x_1544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1536_, v___x_1541_, v___x_1543_, v_x_1504_, v_x_1505_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1544_);
v___x_1546_ = v___x_1538_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v___y_1519_ = v___x_1546_;
goto v___jp_1518_;
}
}
}
default: 
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_x_1504_);
lean_ctor_set(v___x_1549_, 1, v_x_1505_);
v___y_1519_ = v___x_1549_;
goto v___jp_1518_;
}
}
v___jp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_array_fset(v_xs_x27_1517_, v_j_1509_, v___y_1519_);
lean_dec(v_j_1509_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1520_);
v___x_1522_ = v___x_1513_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_ks_1552_; lean_object* v_vs_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1571_; 
v_ks_1552_ = lean_ctor_get(v_x_1501_, 0);
v_vs_1553_ = lean_ctor_get(v_x_1501_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1501_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1555_ = v_x_1501_;
v_isShared_1556_ = v_isSharedCheck_1571_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_vs_1553_);
lean_inc(v_ks_1552_);
lean_dec(v_x_1501_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1571_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_ks_1552_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_vs_1553_);
v___x_1558_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v_newNode_1559_; size_t v___x_1560_; uint8_t v___x_1561_; 
v_newNode_1559_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1558_, v_x_1504_, v_x_1505_);
v___x_1560_ = ((size_t)7ULL);
v___x_1561_ = lean_usize_dec_le(v___x_1560_, v_x_1503_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1559_);
v___x_1563_ = lean_unsigned_to_nat(4u);
v___x_1564_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
lean_dec(v___x_1562_);
if (v___x_1564_ == 0)
{
lean_object* v_ks_1565_; lean_object* v_vs_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_ks_1565_ = lean_ctor_get(v_newNode_1559_, 0);
lean_inc_ref(v_ks_1565_);
v_vs_1566_ = lean_ctor_get(v_newNode_1559_, 1);
lean_inc_ref(v_vs_1566_);
lean_dec_ref(v_newNode_1559_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1503_, v_ks_1565_, v_vs_1566_, v___x_1567_, v___x_1568_);
lean_dec_ref(v_vs_1566_);
lean_dec_ref(v_ks_1565_);
return v___x_1569_;
}
else
{
return v_newNode_1559_;
}
}
else
{
return v_newNode_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1572_, lean_object* v_keys_1573_, lean_object* v_vals_1574_, lean_object* v_i_1575_, lean_object* v_entries_1576_){
_start:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_array_get_size(v_keys_1573_);
v___x_1578_ = lean_nat_dec_lt(v_i_1575_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_dec(v_i_1575_);
return v_entries_1576_;
}
else
{
lean_object* v_k_1579_; lean_object* v_v_1580_; uint64_t v___x_1581_; size_t v_h_1582_; size_t v___x_1583_; lean_object* v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; size_t v___x_1587_; size_t v_h_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_k_1579_ = lean_array_fget_borrowed(v_keys_1573_, v_i_1575_);
v_v_1580_ = lean_array_fget_borrowed(v_vals_1574_, v_i_1575_);
v___x_1581_ = l_Lean_instHashableMVarId_hash(v_k_1579_);
v_h_1582_ = lean_uint64_to_usize(v___x_1581_);
v___x_1583_ = ((size_t)5ULL);
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_sub(v_depth_1572_, v___x_1585_);
v___x_1587_ = lean_usize_mul(v___x_1583_, v___x_1586_);
v_h_1588_ = lean_usize_shift_right(v_h_1582_, v___x_1587_);
v___x_1589_ = lean_nat_add(v_i_1575_, v___x_1584_);
lean_dec(v_i_1575_);
lean_inc(v_v_1580_);
lean_inc(v_k_1579_);
v___x_1590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1576_, v_h_1588_, v_depth_1572_, v_k_1579_, v_v_1580_);
v_i_1575_ = v___x_1589_;
v_entries_1576_ = v___x_1590_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1592_, lean_object* v_keys_1593_, lean_object* v_vals_1594_, lean_object* v_i_1595_, lean_object* v_entries_1596_){
_start:
{
size_t v_depth_boxed_1597_; lean_object* v_res_1598_; 
v_depth_boxed_1597_ = lean_unbox_usize(v_depth_1592_);
lean_dec(v_depth_1592_);
v_res_1598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1597_, v_keys_1593_, v_vals_1594_, v_i_1595_, v_entries_1596_);
lean_dec_ref(v_vals_1594_);
lean_dec_ref(v_keys_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
size_t v_x_151784__boxed_1604_; size_t v_x_151785__boxed_1605_; lean_object* v_res_1606_; 
v_x_151784__boxed_1604_ = lean_unbox_usize(v_x_1600_);
lean_dec(v_x_1600_);
v_x_151785__boxed_1605_ = lean_unbox_usize(v_x_1601_);
lean_dec(v_x_1601_);
v_res_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1599_, v_x_151784__boxed_1604_, v_x_151785__boxed_1605_, v_x_1602_, v_x_1603_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
uint64_t v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v___x_1610_ = l_Lean_instHashableMVarId_hash(v_x_1608_);
v___x_1611_ = lean_uint64_to_usize(v___x_1610_);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1607_, v___x_1611_, v___x_1612_, v_x_1608_, v_x_1609_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1614_, lean_object* v_val_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v_mctx_1619_; lean_object* v_cache_1620_; lean_object* v_zetaDeltaFVarIds_1621_; lean_object* v_postponed_1622_; lean_object* v_diag_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1652_; 
v___x_1618_ = lean_st_ref_take(v___y_1616_);
v_mctx_1619_ = lean_ctor_get(v___x_1618_, 0);
v_cache_1620_ = lean_ctor_get(v___x_1618_, 1);
v_zetaDeltaFVarIds_1621_ = lean_ctor_get(v___x_1618_, 2);
v_postponed_1622_ = lean_ctor_get(v___x_1618_, 3);
v_diag_1623_ = lean_ctor_get(v___x_1618_, 4);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1625_ = v___x_1618_;
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_diag_1623_);
lean_inc(v_postponed_1622_);
lean_inc(v_zetaDeltaFVarIds_1621_);
lean_inc(v_cache_1620_);
lean_inc(v_mctx_1619_);
lean_dec(v___x_1618_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_depth_1627_; lean_object* v_levelAssignDepth_1628_; lean_object* v_lmvarCounter_1629_; lean_object* v_mvarCounter_1630_; lean_object* v_lDecls_1631_; lean_object* v_decls_1632_; lean_object* v_userNames_1633_; lean_object* v_lAssignment_1634_; lean_object* v_eAssignment_1635_; lean_object* v_dAssignment_1636_; lean_object* v_instanceTypedMVars_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1651_; 
v_depth_1627_ = lean_ctor_get(v_mctx_1619_, 0);
v_levelAssignDepth_1628_ = lean_ctor_get(v_mctx_1619_, 1);
v_lmvarCounter_1629_ = lean_ctor_get(v_mctx_1619_, 2);
v_mvarCounter_1630_ = lean_ctor_get(v_mctx_1619_, 3);
v_lDecls_1631_ = lean_ctor_get(v_mctx_1619_, 4);
v_decls_1632_ = lean_ctor_get(v_mctx_1619_, 5);
v_userNames_1633_ = lean_ctor_get(v_mctx_1619_, 6);
v_lAssignment_1634_ = lean_ctor_get(v_mctx_1619_, 7);
v_eAssignment_1635_ = lean_ctor_get(v_mctx_1619_, 8);
v_dAssignment_1636_ = lean_ctor_get(v_mctx_1619_, 9);
v_instanceTypedMVars_1637_ = lean_ctor_get(v_mctx_1619_, 10);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_mctx_1619_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1639_ = v_mctx_1619_;
v_isShared_1640_ = v_isSharedCheck_1651_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_instanceTypedMVars_1637_);
lean_inc(v_dAssignment_1636_);
lean_inc(v_eAssignment_1635_);
lean_inc(v_lAssignment_1634_);
lean_inc(v_userNames_1633_);
lean_inc(v_decls_1632_);
lean_inc(v_lDecls_1631_);
lean_inc(v_mvarCounter_1630_);
lean_inc(v_lmvarCounter_1629_);
lean_inc(v_levelAssignDepth_1628_);
lean_inc(v_depth_1627_);
lean_dec(v_mctx_1619_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1651_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1635_, v_mvarId_1614_, v_val_1615_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 8, v___x_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_depth_1627_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_levelAssignDepth_1628_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_lmvarCounter_1629_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_mvarCounter_1630_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_lDecls_1631_);
lean_ctor_set(v_reuseFailAlloc_1650_, 5, v_decls_1632_);
lean_ctor_set(v_reuseFailAlloc_1650_, 6, v_userNames_1633_);
lean_ctor_set(v_reuseFailAlloc_1650_, 7, v_lAssignment_1634_);
lean_ctor_set(v_reuseFailAlloc_1650_, 8, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1650_, 9, v_dAssignment_1636_);
lean_ctor_set(v_reuseFailAlloc_1650_, 10, v_instanceTypedMVars_1637_);
v___x_1643_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1643_);
v___x_1645_ = v___x_1625_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_cache_1620_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_zetaDeltaFVarIds_1621_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_postponed_1622_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_diag_1623_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_st_ref_put(v___y_1616_, v___x_1645_);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1653_, lean_object* v_val_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1653_, v_val_1654_, v___y_1655_);
lean_dec(v___y_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v_ngen_1661_; lean_object* v_namePrefix_1662_; lean_object* v_idx_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1692_; 
v___x_1660_ = lean_st_ref_get(v___y_1658_);
v_ngen_1661_ = lean_ctor_get(v___x_1660_, 2);
lean_inc_ref(v_ngen_1661_);
lean_dec(v___x_1660_);
v_namePrefix_1662_ = lean_ctor_get(v_ngen_1661_, 0);
v_idx_1663_ = lean_ctor_get(v_ngen_1661_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_ngen_1661_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1665_ = v_ngen_1661_;
v_isShared_1666_ = v_isSharedCheck_1692_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_idx_1663_);
lean_inc(v_namePrefix_1662_);
lean_dec(v_ngen_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1692_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v_env_1668_; lean_object* v_nextMacroScope_1669_; lean_object* v_auxDeclNGen_1670_; lean_object* v_traceState_1671_; lean_object* v_cache_1672_; lean_object* v_messages_1673_; lean_object* v_infoState_1674_; lean_object* v_snapshotTasks_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1690_; 
v___x_1667_ = lean_st_ref_take(v___y_1658_);
v_env_1668_ = lean_ctor_get(v___x_1667_, 0);
v_nextMacroScope_1669_ = lean_ctor_get(v___x_1667_, 1);
v_auxDeclNGen_1670_ = lean_ctor_get(v___x_1667_, 3);
v_traceState_1671_ = lean_ctor_get(v___x_1667_, 4);
v_cache_1672_ = lean_ctor_get(v___x_1667_, 5);
v_messages_1673_ = lean_ctor_get(v___x_1667_, 6);
v_infoState_1674_ = lean_ctor_get(v___x_1667_, 7);
v_snapshotTasks_1675_ = lean_ctor_get(v___x_1667_, 8);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1667_, 2);
lean_dec(v_unused_1691_);
v___x_1677_ = v___x_1667_;
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_snapshotTasks_1675_);
lean_inc(v_infoState_1674_);
lean_inc(v_messages_1673_);
lean_inc(v_cache_1672_);
lean_inc(v_traceState_1671_);
lean_inc(v_auxDeclNGen_1670_);
lean_inc(v_nextMacroScope_1669_);
lean_inc(v_env_1668_);
lean_dec(v___x_1667_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1690_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_r_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_inc(v_idx_1663_);
lean_inc(v_namePrefix_1662_);
v_r_1679_ = l_Lean_Name_num___override(v_namePrefix_1662_, v_idx_1663_);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_idx_1663_, v___x_1680_);
lean_dec(v_idx_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1681_);
v___x_1683_ = v___x_1665_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_namePrefix_1662_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 2, v___x_1683_);
v___x_1685_ = v___x_1677_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_env_1668_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_nextMacroScope_1669_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_auxDeclNGen_1670_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_traceState_1671_);
lean_ctor_set(v_reuseFailAlloc_1688_, 5, v_cache_1672_);
lean_ctor_set(v_reuseFailAlloc_1688_, 6, v_messages_1673_);
lean_ctor_set(v_reuseFailAlloc_1688_, 7, v_infoState_1674_);
lean_ctor_set(v_reuseFailAlloc_1688_, 8, v_snapshotTasks_1675_);
v___x_1685_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_st_ref_put(v___y_1658_, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_r_1679_);
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1693_);
lean_dec(v___y_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v___x_1707_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1705_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1733_, lean_object* v_a_1734_, uint8_t v___y_1735_, uint8_t v___x_1736_, uint8_t v___x_1737_, lean_object* v_a_1738_, lean_object* v___x_1739_, lean_object* v_expr_1740_, lean_object* v___x_1741_, lean_object* v_val_1742_, lean_object* v_mvarId_1743_, lean_object* v___x_1744_, lean_object* v_a_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_mkLambdaFVars(v___x_1733_, v_a_1734_, v___y_1735_, v___x_1736_, v___y_1735_, v___x_1736_, v___x_1737_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1738_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_mkConst(v___x_1759_, v___x_1761_);
v___x_1763_ = lean_unsigned_to_nat(5u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
v___x_1765_ = lean_array_push(v___x_1764_, v___x_1739_);
v___x_1766_ = lean_array_push(v___x_1765_, v_expr_1740_);
v___x_1767_ = lean_array_push(v___x_1766_, v___x_1741_);
v___x_1768_ = lean_array_push(v___x_1767_, v_val_1742_);
v___x_1769_ = lean_array_push(v___x_1768_, v_a_1758_);
v___x_1770_ = l_Lean_mkAppN(v___x_1762_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1743_, v___x_1770_, v___y_1753_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1789_; 
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1790_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1789_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v_toGoalState_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1787_; 
v___x_1775_ = lean_st_ref_get(v___y_1746_);
v_toGoalState_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v___x_1775_, 1);
lean_dec(v_unused_1788_);
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1787_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_toGoalState_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1787_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v___x_1744_);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_toGoalState_1776_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1744_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1745_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1782_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_a_1745_);
lean_dec(v___x_1744_);
v_a_1791_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1771_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1771_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1745_);
lean_dec(v___x_1744_);
lean_dec(v_mvarId_1743_);
lean_dec_ref(v_val_1742_);
lean_dec_ref(v___x_1741_);
lean_dec_ref(v_expr_1740_);
lean_dec_ref(v___x_1739_);
lean_dec(v_a_1738_);
v_a_1799_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1757_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1757_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1807_ = _args[0];
lean_object* v_a_1808_ = _args[1];
lean_object* v___y_1809_ = _args[2];
lean_object* v___x_1810_ = _args[3];
lean_object* v___x_1811_ = _args[4];
lean_object* v_a_1812_ = _args[5];
lean_object* v___x_1813_ = _args[6];
lean_object* v_expr_1814_ = _args[7];
lean_object* v___x_1815_ = _args[8];
lean_object* v_val_1816_ = _args[9];
lean_object* v_mvarId_1817_ = _args[10];
lean_object* v___x_1818_ = _args[11];
lean_object* v_a_1819_ = _args[12];
lean_object* v___y_1820_ = _args[13];
lean_object* v___y_1821_ = _args[14];
lean_object* v___y_1822_ = _args[15];
lean_object* v___y_1823_ = _args[16];
lean_object* v___y_1824_ = _args[17];
lean_object* v___y_1825_ = _args[18];
lean_object* v___y_1826_ = _args[19];
lean_object* v___y_1827_ = _args[20];
lean_object* v___y_1828_ = _args[21];
lean_object* v___y_1829_ = _args[22];
lean_object* v___y_1830_ = _args[23];
_start:
{
uint8_t v___y_152106__boxed_1831_; uint8_t v___x_152107__boxed_1832_; uint8_t v___x_152108__boxed_1833_; lean_object* v_res_1834_; 
v___y_152106__boxed_1831_ = lean_unbox(v___y_1809_);
v___x_152107__boxed_1832_ = lean_unbox(v___x_1810_);
v___x_152108__boxed_1833_ = lean_unbox(v___x_1811_);
v_res_1834_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1807_, v_a_1808_, v___y_152106__boxed_1831_, v___x_152107__boxed_1832_, v___x_152108__boxed_1833_, v_a_1812_, v___x_1813_, v_expr_1814_, v___x_1815_, v_val_1816_, v_mvarId_1817_, v___x_1818_, v_a_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___x_1807_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1840_, lean_object* v_a_1841_, uint8_t v___x_1842_, uint8_t v___x_1843_, uint8_t v___x_1844_, lean_object* v_a_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_expr_1848_, lean_object* v___x_1849_, lean_object* v_val_1850_, lean_object* v_mvarId_1851_, lean_object* v___x_1852_, lean_object* v_a_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Meta_mkLambdaFVars(v___x_1840_, v_a_1841_, v___x_1842_, v___x_1843_, v___x_1842_, v___x_1843_, v___x_1844_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1845_);
lean_ctor_set(v___x_1868_, 1, v___x_1846_);
v___x_1869_ = l_Lean_mkConst(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_unsigned_to_nat(5u);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___x_1870_);
v___x_1872_ = lean_array_push(v___x_1871_, v___x_1847_);
v___x_1873_ = lean_array_push(v___x_1872_, v_expr_1848_);
v___x_1874_ = lean_array_push(v___x_1873_, v___x_1849_);
v___x_1875_ = lean_array_push(v___x_1874_, v_val_1850_);
v___x_1876_ = lean_array_push(v___x_1875_, v_a_1866_);
v___x_1877_ = l_Lean_mkAppN(v___x_1869_, v___x_1876_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1851_, v___x_1877_, v___y_1861_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1878_, 0);
lean_dec(v_unused_1897_);
v___x_1880_ = v___x_1878_;
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v___x_1878_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_toGoalState_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1894_; 
v___x_1882_ = lean_st_ref_get(v___y_1854_);
v_toGoalState_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1882_, 1);
lean_dec(v_unused_1895_);
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_toGoalState_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1852_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_toGoalState_1883_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1852_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_a_1853_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1889_);
v___x_1891_ = v___x_1880_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1853_);
lean_dec(v___x_1852_);
v_a_1898_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1878_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1878_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1853_);
lean_dec(v___x_1852_);
lean_dec(v_mvarId_1851_);
lean_dec_ref(v_val_1850_);
lean_dec_ref(v___x_1849_);
lean_dec_ref(v_expr_1848_);
lean_dec_ref(v___x_1847_);
lean_dec(v___x_1846_);
lean_dec(v_a_1845_);
v_a_1906_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1865_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1865_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1914_ = _args[0];
lean_object* v_a_1915_ = _args[1];
lean_object* v___x_1916_ = _args[2];
lean_object* v___x_1917_ = _args[3];
lean_object* v___x_1918_ = _args[4];
lean_object* v_a_1919_ = _args[5];
lean_object* v___x_1920_ = _args[6];
lean_object* v___x_1921_ = _args[7];
lean_object* v_expr_1922_ = _args[8];
lean_object* v___x_1923_ = _args[9];
lean_object* v_val_1924_ = _args[10];
lean_object* v_mvarId_1925_ = _args[11];
lean_object* v___x_1926_ = _args[12];
lean_object* v_a_1927_ = _args[13];
lean_object* v___y_1928_ = _args[14];
lean_object* v___y_1929_ = _args[15];
lean_object* v___y_1930_ = _args[16];
lean_object* v___y_1931_ = _args[17];
lean_object* v___y_1932_ = _args[18];
lean_object* v___y_1933_ = _args[19];
lean_object* v___y_1934_ = _args[20];
lean_object* v___y_1935_ = _args[21];
lean_object* v___y_1936_ = _args[22];
lean_object* v___y_1937_ = _args[23];
lean_object* v___y_1938_ = _args[24];
_start:
{
uint8_t v___x_152288__boxed_1939_; uint8_t v___x_152289__boxed_1940_; uint8_t v___x_152290__boxed_1941_; lean_object* v_res_1942_; 
v___x_152288__boxed_1939_ = lean_unbox(v___x_1916_);
v___x_152289__boxed_1940_ = lean_unbox(v___x_1917_);
v___x_152290__boxed_1941_ = lean_unbox(v___x_1918_);
v_res_1942_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1914_, v_a_1915_, v___x_152288__boxed_1939_, v___x_152289__boxed_1940_, v___x_152290__boxed_1941_, v_a_1919_, v___x_1920_, v___x_1921_, v_expr_1922_, v___x_1923_, v_val_1924_, v_mvarId_1925_, v___x_1926_, v_a_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___x_1914_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1943_, lean_object* v_a_1944_, uint8_t v___y_1945_, uint8_t v___x_1946_, uint8_t v___x_1947_, lean_object* v_mvarId_1948_, lean_object* v___x_1949_, lean_object* v_a_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Meta_mkLambdaFVars(v___x_1943_, v_a_1944_, v___y_1945_, v___x_1946_, v___y_1945_, v___x_1946_, v___x_1947_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1948_, v_a_1963_, v___y_1958_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1983_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1982_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1982_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v_toGoalState_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v___x_1968_ = lean_st_ref_get(v___y_1951_);
v_toGoalState_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v___x_1968_, 1);
lean_dec(v_unused_1981_);
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toGoalState_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_1949_);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_toGoalState_1969_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1949_);
v___x_1974_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1950_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1975_);
v___x_1977_ = v___x_1966_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1950_);
lean_dec(v___x_1949_);
v_a_1984_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1964_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1964_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1950_);
lean_dec(v___x_1949_);
lean_dec(v_mvarId_1948_);
v_a_1992_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1962_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1962_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2000_ = _args[0];
lean_object* v_a_2001_ = _args[1];
lean_object* v___y_2002_ = _args[2];
lean_object* v___x_2003_ = _args[3];
lean_object* v___x_2004_ = _args[4];
lean_object* v_mvarId_2005_ = _args[5];
lean_object* v___x_2006_ = _args[6];
lean_object* v_a_2007_ = _args[7];
lean_object* v___y_2008_ = _args[8];
lean_object* v___y_2009_ = _args[9];
lean_object* v___y_2010_ = _args[10];
lean_object* v___y_2011_ = _args[11];
lean_object* v___y_2012_ = _args[12];
lean_object* v___y_2013_ = _args[13];
lean_object* v___y_2014_ = _args[14];
lean_object* v___y_2015_ = _args[15];
lean_object* v___y_2016_ = _args[16];
lean_object* v___y_2017_ = _args[17];
lean_object* v___y_2018_ = _args[18];
_start:
{
uint8_t v___y_152459__boxed_2019_; uint8_t v___x_152460__boxed_2020_; uint8_t v___x_152461__boxed_2021_; lean_object* v_res_2022_; 
v___y_152459__boxed_2019_ = lean_unbox(v___y_2002_);
v___x_152460__boxed_2020_ = lean_unbox(v___x_2003_);
v___x_152461__boxed_2021_ = lean_unbox(v___x_2004_);
v_res_2022_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2000_, v_a_2001_, v___y_152459__boxed_2019_, v___x_152460__boxed_2020_, v___x_152461__boxed_2021_, v_mvarId_2005_, v___x_2006_, v_a_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
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
lean_dec_ref(v___x_2000_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2025_, lean_object* v___x_2026_, lean_object* v_generation_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
lean_inc(v_mvarId_2025_);
v___x_2039_ = l_Lean_MVarId_getTag(v_mvarId_2025_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2026_, v_a_2040_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_n(v_a_2042_, 2);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2025_, v_a_2042_, v___y_2035_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2044_; lean_object* v_toGoalState_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2044_ = lean_st_ref_get(v___y_2028_);
v_toGoalState_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2044_, 1);
lean_dec(v_unused_2055_);
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_toGoalState_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_Expr_mvarId_x21(v_a_2042_);
lean_dec(v_a_2042_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_toGoalState_2045_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2051_, v_generation_2027_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_a_2042_);
lean_dec(v_generation_2027_);
v_a_2056_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2043_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2043_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_generation_2027_);
lean_dec(v_mvarId_2025_);
v_a_2064_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2041_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2041_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_generation_2027_);
lean_dec_ref(v___x_2026_);
lean_dec(v_mvarId_2025_);
v_a_2072_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2039_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2039_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2080_, lean_object* v___x_2081_, lean_object* v_generation_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2080_, v___x_2081_, v_generation_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec(v___y_2083_);
return v_res_2094_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2102_ = l_Lean_mkConst(v___x_2101_, v___x_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2103_, lean_object* v_generation_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v_a_2117_; lean_object* v___y_2122_; lean_object* v___x_2132_; lean_object* v_mvarId_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2421_; 
lean_inc_ref(v_goal_2103_);
v___x_2115_ = lean_st_mk_ref(v_goal_2103_);
v___x_2132_ = lean_st_ref_get(v___x_2115_);
v_mvarId_2133_ = lean_ctor_get(v___x_2132_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v___x_2132_, 0);
lean_dec(v_unused_2422_);
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2421_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_mvarId_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2421_;
goto v_resetjp_2134_;
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_st_ref_get(v___x_2115_);
lean_dec(v___x_2115_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_a_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
v___jp_2121_:
{
if (lean_obj_tag(v___y_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___y_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___y_2122_, 1);
v_a_2117_ = v_a_2123_;
goto v___jp_2116_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v___x_2115_);
v_a_2124_ = lean_ctor_get(v___y_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___y_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___y_2122_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___y_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_MVarId_getType(v_mvarId_2133_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; uint8_t v___x_2140_; lean_object* v___y_2142_; lean_object* v___y_2143_; uint8_t v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_Expr_isForall(v_a_2138_);
v___x_2140_ = 1;
if (v___x_2139_ == 0)
{
uint8_t v___x_2182_; 
lean_del_object(v___x_2135_);
v___x_2182_ = l_Lean_Expr_isLet(v_a_2138_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_a_2138_);
lean_dec_ref(v___y_2110_);
lean_dec(v_generation_2104_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_goal_2103_);
v_a_2117_ = v___x_2183_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2184_; 
lean_dec_ref(v_goal_2103_);
v___x_2184_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2106_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; uint8_t v_zetaDelta_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v_zetaDelta_2186_ = lean_ctor_get_uint8(v_a_2185_, sizeof(void*)*14 + 19);
lean_dec(v_a_2185_);
if (v_zetaDelta_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_a_2138_);
v___x_2187_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v_mvarId_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = lean_st_ref_get(v___x_2115_);
v_mvarId_2190_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_mvarId_2190_);
lean_dec(v___x_2189_);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2191_, 0, v_a_2188_);
lean_closure_set(v___f_2191_, 1, v_generation_2104_);
v___x_2192_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2190_, v___f_2191_, v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec_ref(v___y_2110_);
v___y_2122_ = v___x_2192_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
lean_dec(v_generation_2104_);
v_a_2193_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2187_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2187_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v_mvarId_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; 
v___x_2201_ = lean_st_ref_get(v___x_2115_);
v_mvarId_2202_ = lean_ctor_get(v___x_2201_, 1);
lean_inc_n(v_mvarId_2202_, 2);
lean_dec(v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2204_ = l_Lean_Meta_expandLet(v_a_2138_, v___x_2203_, v___x_2140_);
lean_dec(v_a_2138_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2205_, 0, v_mvarId_2202_);
lean_closure_set(v___f_2205_, 1, v___x_2204_);
lean_closure_set(v___f_2205_, 2, v_generation_2104_);
v___x_2206_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2202_, v___f_2205_, v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec_ref(v___y_2110_);
v___y_2122_ = v___x_2206_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
lean_dec(v_generation_2104_);
v_a_2207_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2184_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2184_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; uint8_t v___y_2221_; uint8_t v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v_localInsts_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___x_2313_; 
lean_dec(v_generation_2104_);
lean_dec_ref(v_goal_2103_);
v___x_2215_ = l_Lean_Expr_bindingDomain_x21(v_a_2138_);
lean_inc_ref(v___x_2215_);
v___x_2313_ = l_Lean_Meta_isProp(v___x_2215_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; uint8_t v___y_2316_; uint8_t v___x_2389_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2389_ = lean_unbox(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2389_ == 0)
{
if (v___x_2139_ == 0)
{
lean_del_object(v___x_2135_);
v___y_2316_ = v___x_2139_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2390_; 
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
v___x_2390_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec_ref(v___y_2110_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = lean_st_ref_get(v___x_2115_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 3);
lean_ctor_set(v___x_2135_, 1, v___x_2392_);
lean_ctor_set(v___x_2135_, 0, v_a_2391_);
v___x_2394_ = v___x_2135_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2391_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
v_a_2117_ = v___x_2394_;
goto v___jp_2116_;
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_del_object(v___x_2135_);
lean_dec(v___x_2115_);
v_a_2396_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2390_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2390_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
uint8_t v___x_2404_; 
lean_del_object(v___x_2135_);
v___x_2404_ = 0;
v___y_2316_ = v___x_2404_;
goto v___jp_2315_;
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v_mvarId_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2387_; 
v___x_2317_ = lean_st_ref_get(v___x_2115_);
v_mvarId_2318_ = lean_ctor_get(v___x_2317_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v___x_2317_, 0);
lean_dec(v_unused_2388_);
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2387_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_mvarId_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2387_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; 
lean_inc(v_mvarId_2318_);
v___x_2322_ = l_Lean_MVarId_getTag(v_mvarId_2318_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
lean_inc_ref(v___x_2215_);
v___x_2326_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2215_, v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_expr_2328_; lean_object* v_proof_x3f_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_expr_2328_ = lean_ctor_get(v_a_2327_, 0);
lean_inc_ref_n(v_expr_2328_, 2);
v_proof_x3f_2329_ = lean_ctor_get(v_a_2327_, 1);
lean_inc(v_proof_x3f_2329_);
lean_dec(v_a_2327_);
v___x_2330_ = l_Lean_Expr_bindingName_x21(v_a_2138_);
lean_inc(v___x_2330_);
v___x_2331_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2330_, v_expr_2328_, v___x_2115_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_lctx_2333_; lean_object* v_localInstances_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_lctx_2333_ = lean_ctor_get(v___y_2110_, 2);
v_localInstances_2334_ = lean_ctor_get(v___y_2110_, 3);
lean_inc_n(v_a_2325_, 2);
v___x_2335_ = l_Lean_mkFVar(v_a_2325_);
v___x_2336_ = l_Lean_Expr_bindingInfo_x21(v_a_2138_);
v___x_2337_ = 0;
lean_inc_ref_n(v_expr_2328_, 2);
lean_inc_ref(v_lctx_2333_);
v___x_2338_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2333_, v_a_2325_, v_a_2332_, v_expr_2328_, v___x_2336_, v___x_2337_);
v___x_2339_ = l_Lean_Meta_isClass_x3f(v_expr_2328_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_Expr_bindingBody_x21(v_a_2138_);
if (lean_obj_tag(v_a_2340_) == 1)
{
lean_object* v_val_2342_; lean_object* v___x_2344_; 
v_val_2342_ = lean_ctor_get(v_a_2340_, 0);
lean_inc(v_val_2342_);
lean_dec_ref_known(v_a_2340_, 1);
lean_inc_ref(v___x_2335_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2335_);
lean_ctor_set(v___x_2320_, 0, v_val_2342_);
v___x_2344_ = v___x_2320_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_val_2342_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2335_);
v___x_2344_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
lean_inc_ref(v_localInstances_2334_);
v___x_2345_ = lean_array_push(v_localInstances_2334_, v___x_2344_);
lean_inc(v___x_2115_);
lean_inc_ref(v_expr_2328_);
v___y_2217_ = v_expr_2328_;
v___y_2218_ = v_mvarId_2318_;
v___y_2219_ = v___x_2341_;
v___y_2220_ = v_a_2325_;
v___y_2221_ = v___y_2316_;
v___y_2222_ = v___x_2336_;
v___y_2223_ = v___x_2335_;
v___y_2224_ = v___x_2338_;
v___y_2225_ = v_proof_x3f_2329_;
v___y_2226_ = v_a_2323_;
v___y_2227_ = v_expr_2328_;
v___y_2228_ = v___x_2330_;
v_localInsts_2229_ = v___x_2345_;
v___y_2230_ = v___x_2115_;
v___y_2231_ = v___y_2105_;
v___y_2232_ = v___y_2106_;
v___y_2233_ = v___y_2107_;
v___y_2234_ = v___y_2108_;
v___y_2235_ = v___y_2109_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
goto v___jp_2216_;
}
}
else
{
lean_inc_ref(v_localInstances_2334_);
lean_dec(v_a_2340_);
lean_del_object(v___x_2320_);
lean_inc(v___x_2115_);
lean_inc_ref(v_expr_2328_);
v___y_2217_ = v_expr_2328_;
v___y_2218_ = v_mvarId_2318_;
v___y_2219_ = v___x_2341_;
v___y_2220_ = v_a_2325_;
v___y_2221_ = v___y_2316_;
v___y_2222_ = v___x_2336_;
v___y_2223_ = v___x_2335_;
v___y_2224_ = v___x_2338_;
v___y_2225_ = v_proof_x3f_2329_;
v___y_2226_ = v_a_2323_;
v___y_2227_ = v_expr_2328_;
v___y_2228_ = v___x_2330_;
v_localInsts_2229_ = v_localInstances_2334_;
v___y_2230_ = v___x_2115_;
v___y_2231_ = v___y_2105_;
v___y_2232_ = v___y_2106_;
v___y_2233_ = v___y_2107_;
v___y_2234_ = v___y_2108_;
v___y_2235_ = v___y_2109_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
goto v___jp_2216_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2335_);
lean_dec(v___x_2330_);
lean_dec(v_proof_x3f_2329_);
lean_dec_ref(v_expr_2328_);
lean_dec(v_a_2325_);
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_mvarId_2318_);
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2347_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2339_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2339_);
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
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___x_2330_);
lean_dec(v_proof_x3f_2329_);
lean_dec_ref(v_expr_2328_);
lean_dec(v_a_2325_);
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_mvarId_2318_);
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2355_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2331_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2331_);
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
lean_dec(v_a_2325_);
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_mvarId_2318_);
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2363_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2326_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2326_);
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
lean_dec(v_a_2323_);
lean_del_object(v___x_2320_);
lean_dec(v_mvarId_2318_);
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2371_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2324_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2324_);
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
lean_del_object(v___x_2320_);
lean_dec(v_mvarId_2318_);
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2379_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2322_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2322_);
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
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v___x_2215_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2135_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
v_a_2405_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2313_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2313_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
v___jp_2216_:
{
if (lean_obj_tag(v___y_2225_) == 0)
{
uint8_t v___x_2240_; 
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___x_2215_);
v___x_2240_ = l_Lean_Expr_isArrow(v_a_2138_);
lean_dec(v_a_2138_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_expr_instantiate1(v___y_2219_, v___y_2223_);
lean_dec_ref(v___y_2219_);
v___y_2142_ = v___y_2218_;
v___y_2143_ = v___y_2220_;
v___y_2144_ = v___y_2221_;
v___y_2145_ = v___y_2223_;
v___y_2146_ = v_localInsts_2229_;
v___y_2147_ = v___y_2239_;
v___y_2148_ = v___y_2237_;
v___y_2149_ = v___y_2238_;
v___y_2150_ = v___y_2235_;
v___y_2151_ = v___y_2236_;
v___y_2152_ = v___y_2232_;
v___y_2153_ = v___y_2234_;
v___y_2154_ = v___y_2224_;
v___y_2155_ = v___y_2230_;
v___y_2156_ = v___y_2226_;
v___y_2157_ = v___y_2233_;
v___y_2158_ = v___y_2231_;
v___y_2159_ = v___x_2241_;
goto v___jp_2141_;
}
else
{
v___y_2142_ = v___y_2218_;
v___y_2143_ = v___y_2220_;
v___y_2144_ = v___y_2221_;
v___y_2145_ = v___y_2223_;
v___y_2146_ = v_localInsts_2229_;
v___y_2147_ = v___y_2239_;
v___y_2148_ = v___y_2237_;
v___y_2149_ = v___y_2238_;
v___y_2150_ = v___y_2235_;
v___y_2151_ = v___y_2236_;
v___y_2152_ = v___y_2232_;
v___y_2153_ = v___y_2234_;
v___y_2154_ = v___y_2224_;
v___y_2155_ = v___y_2230_;
v___y_2156_ = v___y_2226_;
v___y_2157_ = v___y_2233_;
v___y_2158_ = v___y_2231_;
v___y_2159_ = v___y_2219_;
goto v___jp_2141_;
}
}
else
{
lean_object* v_val_2242_; uint8_t v___x_2243_; 
v_val_2242_ = lean_ctor_get(v___y_2225_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v___y_2225_, 1);
v___x_2243_ = l_Lean_Expr_isArrow(v_a_2138_);
lean_dec(v_a_2138_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_inc_ref(v___y_2219_);
lean_inc_ref_n(v___x_2215_, 2);
v___x_2244_ = l_Lean_mkLambda(v___y_2228_, v___y_2222_, v___x_2215_, v___y_2219_);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2223_);
lean_inc(v_val_2242_);
v___x_2247_ = l_Lean_mkApp4(v___x_2246_, v___x_2215_, v___y_2227_, v_val_2242_, v___y_2223_);
v___x_2248_ = lean_expr_instantiate1(v___y_2219_, v___x_2247_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___y_2219_);
lean_inc_ref(v___x_2248_);
v___x_2249_ = l_Lean_Meta_getLevel(v___x_2248_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = 2;
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2224_, v_localInsts_2229_, v___x_2248_, v___x_2251_, v___y_2226_, v___x_2252_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2255_ = l_Lean_Expr_mvarId_x21(v_a_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_mk_empty_array_with_capacity(v___x_2256_);
v___x_2258_ = lean_array_push(v___x_2257_, v___y_2223_);
v___x_2259_ = 1;
v___x_2260_ = lean_box(v___x_2243_);
v___x_2261_ = lean_box(v___x_2140_);
v___x_2262_ = lean_box(v___x_2259_);
lean_inc(v___x_2255_);
v___f_2263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2263_, 0, v___x_2258_);
lean_closure_set(v___f_2263_, 1, v_a_2254_);
lean_closure_set(v___f_2263_, 2, v___x_2260_);
lean_closure_set(v___f_2263_, 3, v___x_2261_);
lean_closure_set(v___f_2263_, 4, v___x_2262_);
lean_closure_set(v___f_2263_, 5, v_a_2250_);
lean_closure_set(v___f_2263_, 6, v___x_2245_);
lean_closure_set(v___f_2263_, 7, v___x_2215_);
lean_closure_set(v___f_2263_, 8, v___y_2217_);
lean_closure_set(v___f_2263_, 9, v___x_2244_);
lean_closure_set(v___f_2263_, 10, v_val_2242_);
lean_closure_set(v___f_2263_, 11, v___y_2218_);
lean_closure_set(v___f_2263_, 12, v___x_2255_);
lean_closure_set(v___f_2263_, 13, v___y_2220_);
v___x_2264_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2255_, v___f_2263_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
v___y_2122_ = v___x_2264_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2250_);
lean_dec_ref(v___x_2244_);
lean_dec(v_val_2242_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2220_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___x_2215_);
lean_dec(v___x_2115_);
v_a_2265_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2253_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2253_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2244_);
lean_dec(v_val_2242_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
lean_dec_ref(v_localInsts_2229_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2220_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___x_2215_);
lean_dec(v___x_2115_);
v_a_2273_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2249_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2249_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v___x_2281_; 
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_inc_ref(v___y_2219_);
v___x_2281_ = l_Lean_Meta_getLevel(v___y_2219_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = 2;
v___x_2284_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2219_);
v___x_2285_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2224_, v_localInsts_2229_, v___y_2219_, v___x_2283_, v___y_2226_, v___x_2284_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = l_Lean_Expr_mvarId_x21(v_a_2286_);
v___x_2288_ = lean_unsigned_to_nat(1u);
v___x_2289_ = lean_mk_empty_array_with_capacity(v___x_2288_);
v___x_2290_ = lean_array_push(v___x_2289_, v___y_2223_);
v___x_2291_ = 1;
v___x_2292_ = lean_box(v___y_2221_);
v___x_2293_ = lean_box(v___x_2140_);
v___x_2294_ = lean_box(v___x_2291_);
lean_inc(v___x_2287_);
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2295_, 0, v___x_2290_);
lean_closure_set(v___f_2295_, 1, v_a_2286_);
lean_closure_set(v___f_2295_, 2, v___x_2292_);
lean_closure_set(v___f_2295_, 3, v___x_2293_);
lean_closure_set(v___f_2295_, 4, v___x_2294_);
lean_closure_set(v___f_2295_, 5, v_a_2282_);
lean_closure_set(v___f_2295_, 6, v___x_2215_);
lean_closure_set(v___f_2295_, 7, v___y_2217_);
lean_closure_set(v___f_2295_, 8, v___y_2219_);
lean_closure_set(v___f_2295_, 9, v_val_2242_);
lean_closure_set(v___f_2295_, 10, v___y_2218_);
lean_closure_set(v___f_2295_, 11, v___x_2287_);
lean_closure_set(v___f_2295_, 12, v___y_2220_);
v___x_2296_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2287_, v___f_2295_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
v___y_2122_ = v___x_2296_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_a_2282_);
lean_dec(v_val_2242_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___x_2215_);
lean_dec(v___x_2115_);
v_a_2297_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2285_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2285_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_val_2242_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2230_);
lean_dec_ref(v_localInsts_2229_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___x_2215_);
lean_dec(v___x_2115_);
v_a_2305_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2281_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2281_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
}
v___jp_2141_:
{
uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = 2;
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2154_, v___y_2146_, v___y_2159_, v___x_2160_, v___y_2156_, v___x_2161_, v___y_2151_, v___y_2148_, v___y_2149_, v___y_2147_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = l_Lean_Expr_mvarId_x21(v_a_2163_);
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_mk_empty_array_with_capacity(v___x_2165_);
v___x_2167_ = lean_array_push(v___x_2166_, v___y_2145_);
v___x_2168_ = 1;
v___x_2169_ = lean_box(v___y_2144_);
v___x_2170_ = lean_box(v___x_2140_);
v___x_2171_ = lean_box(v___x_2168_);
lean_inc(v___x_2164_);
v___f_2172_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2172_, 0, v___x_2167_);
lean_closure_set(v___f_2172_, 1, v_a_2163_);
lean_closure_set(v___f_2172_, 2, v___x_2169_);
lean_closure_set(v___f_2172_, 3, v___x_2170_);
lean_closure_set(v___f_2172_, 4, v___x_2171_);
lean_closure_set(v___f_2172_, 5, v___y_2142_);
lean_closure_set(v___f_2172_, 6, v___x_2164_);
lean_closure_set(v___f_2172_, 7, v___y_2143_);
v___x_2173_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2164_, v___f_2172_, v___y_2155_, v___y_2158_, v___y_2152_, v___y_2157_, v___y_2153_, v___y_2150_, v___y_2151_, v___y_2148_, v___y_2149_, v___y_2147_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2155_);
v___y_2122_ = v___x_2173_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2151_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec(v___x_2115_);
v_a_2174_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2162_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2162_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_del_object(v___x_2135_);
lean_dec(v___x_2115_);
lean_dec_ref(v___y_2110_);
lean_dec(v_generation_2104_);
lean_dec_ref(v_goal_2103_);
v_a_2413_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2137_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2137_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2423_, lean_object* v_generation_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2423_, v_generation_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2436_, lean_object* v_generation_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_mvarId_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; 
v_mvarId_2448_ = lean_ctor_get(v_goal_2436_, 1);
lean_inc(v_mvarId_2448_);
v___f_2449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2449_, 0, v_goal_2436_);
lean_closure_set(v___f_2449_, 1, v_generation_2437_);
v___x_2450_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2448_, v___f_2449_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_fst_2455_; lean_object* v___x_2457_; 
v_fst_2455_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_fst_2455_);
lean_dec(v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_fst_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_fst_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2450_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2450_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2468_, lean_object* v_generation_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2468_, v_generation_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2481_, lean_object* v_val_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2481_, v_val_2482_, v___y_2490_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2495_, lean_object* v_val_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2495_, v_val_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2518_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v___y_2521_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2533_, lean_object* v_x_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2534_, v_x_2535_, v_x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2538_, lean_object* v_x_2539_, size_t v_x_2540_, size_t v_x_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2539_, v_x_2540_, v_x_2541_, v_x_2542_, v_x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
size_t v_x_153486__boxed_2551_; size_t v_x_153487__boxed_2552_; lean_object* v_res_2553_; 
v_x_153486__boxed_2551_ = lean_unbox_usize(v_x_2547_);
lean_dec(v_x_2547_);
v_x_153487__boxed_2552_ = lean_unbox_usize(v_x_2548_);
lean_dec(v_x_2548_);
v_res_2553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2545_, v_x_2546_, v_x_153486__boxed_2551_, v_x_153487__boxed_2552_, v_x_2549_, v_x_2550_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2554_, lean_object* v_n_2555_, lean_object* v_k_2556_, lean_object* v_v_2557_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2555_, v_k_2556_, v_v_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2559_, size_t v_depth_2560_, lean_object* v_keys_2561_, lean_object* v_vals_2562_, lean_object* v_heq_2563_, lean_object* v_i_2564_, lean_object* v_entries_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2560_, v_keys_2561_, v_vals_2562_, v_i_2564_, v_entries_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2567_, lean_object* v_depth_2568_, lean_object* v_keys_2569_, lean_object* v_vals_2570_, lean_object* v_heq_2571_, lean_object* v_i_2572_, lean_object* v_entries_2573_){
_start:
{
size_t v_depth_boxed_2574_; lean_object* v_res_2575_; 
v_depth_boxed_2574_ = lean_unbox_usize(v_depth_2568_);
lean_dec(v_depth_2568_);
v_res_2575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2567_, v_depth_boxed_2574_, v_keys_2569_, v_vals_2570_, v_heq_2571_, v_i_2572_, v_entries_2573_);
lean_dec_ref(v_vals_2570_);
lean_dec_ref(v_keys_2569_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2577_, v_x_2578_, v_x_2579_, v_x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Expr_getAppFn(v_type_2582_);
if (lean_obj_tag(v___x_2585_) == 4)
{
lean_object* v_declName_2586_; lean_object* v___x_2587_; 
v_declName_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_declName_2586_);
lean_dec_ref_known(v___x_2585_, 2);
v___x_2587_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2586_, v_a_2583_);
lean_dec(v_declName_2586_);
return v___x_2587_;
}
else
{
uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref(v___x_2585_);
v___x_2588_ = 0;
v___x_2589_ = lean_box(v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2591_, v_a_2592_);
lean_dec_ref(v_a_2592_);
lean_dec_ref(v_type_2591_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2595_, v_a_2597_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_type_2607_);
return v_res_2618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
lean_ctor_set(v___x_2624_, 3, v___x_2623_);
lean_ctor_set(v___x_2624_, 4, v___x_2622_);
lean_ctor_set(v___x_2624_, 5, v___x_2622_);
lean_ctor_set(v___x_2624_, 6, v___x_2622_);
lean_ctor_set(v___x_2624_, 7, v___x_2622_);
lean_ctor_set(v___x_2624_, 8, v___x_2622_);
lean_ctor_set(v___x_2624_, 9, v___x_2622_);
lean_ctor_set(v___x_2624_, 10, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_unsigned_to_nat(32u);
v___x_2626_ = lean_mk_empty_array_with_capacity(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2628_ = ((size_t)5ULL);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_unsigned_to_nat(32u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2633_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2631_);
lean_ctor_set(v___x_2633_, 2, v___x_2629_);
lean_ctor_set(v___x_2633_, 3, v___x_2629_);
lean_ctor_set_usize(v___x_2633_, 4, v___x_2628_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2634_ = lean_box(1);
v___x_2635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2635_);
lean_ctor_set(v___x_2637_, 2, v___x_2634_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2658_ = l_Lean_stringToMessageData(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2659_, lean_object* v_declHint_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v_env_2664_; uint8_t v___x_2665_; 
v___x_2663_ = lean_st_ref_get(v___y_2661_);
v_env_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc_ref(v_env_2664_);
lean_dec(v___x_2663_);
v___x_2665_ = l_Lean_Name_isAnonymous(v_declHint_2660_);
if (v___x_2665_ == 0)
{
uint8_t v_isExporting_2666_; 
v_isExporting_2666_ = lean_ctor_get_uint8(v_env_2664_, sizeof(void*)*8);
if (v_isExporting_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v_env_2664_);
lean_dec(v_declHint_2660_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_msg_2659_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
lean_inc_ref(v_env_2664_);
v___x_2668_ = l_Lean_Environment_setExporting(v_env_2664_, v___x_2665_);
lean_inc(v_declHint_2660_);
lean_inc_ref(v___x_2668_);
v___x_2669_ = l_Lean_Environment_contains(v___x_2668_, v_declHint_2660_, v_isExporting_2666_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v___x_2668_);
lean_dec_ref(v_env_2664_);
lean_dec(v_declHint_2660_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_msg_2659_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_c_2676_; lean_object* v___x_2677_; 
v___x_2671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2673_ = l_Lean_Options_empty;
v___x_2674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2668_);
lean_ctor_set(v___x_2674_, 1, v___x_2671_);
lean_ctor_set(v___x_2674_, 2, v___x_2672_);
lean_ctor_set(v___x_2674_, 3, v___x_2673_);
lean_inc(v_declHint_2660_);
v___x_2675_ = l_Lean_MessageData_ofConstName(v_declHint_2660_, v___x_2665_);
v_c_2676_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2676_, 0, v___x_2674_);
lean_ctor_set(v_c_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2664_, v_declHint_2660_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_dec_ref(v_env_2664_);
lean_dec(v_declHint_2660_);
v___x_2678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v_c_2676_);
v___x_2680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = l_Lean_MessageData_note(v___x_2681_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_msg_2659_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2720_; 
v_val_2685_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2687_ = v___x_2677_;
v_isShared_2688_ = v_isSharedCheck_2720_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v___x_2677_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2720_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_mod_2692_; uint8_t v___x_2693_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = l_Lean_Environment_header(v_env_2664_);
lean_dec_ref(v_env_2664_);
v___x_2691_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2690_);
v_mod_2692_ = lean_array_get(v___x_2689_, v___x_2691_, v_val_2685_);
lean_dec(v_val_2685_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = l_Lean_isPrivateName(v_declHint_2660_);
lean_dec(v_declHint_2660_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v_c_2676_);
v___x_2696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_ofName(v_mod_2692_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_MessageData_note(v___x_2701_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_msg_2659_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2703_);
v___x_2705_ = v___x_2687_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v_c_2676_);
v___x_2709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = l_Lean_MessageData_ofName(v_mod_2692_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = l_Lean_MessageData_note(v___x_2714_);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_msg_2659_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2716_);
v___x_2718_ = v___x_2687_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2721_; 
lean_dec_ref(v_env_2664_);
lean_dec(v_declHint_2660_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_msg_2659_);
return v___x_2721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2722_, lean_object* v_declHint_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2722_, v_declHint_2723_, v___y_2724_);
lean_dec(v___y_2724_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2727_, lean_object* v_declHint_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2742_; 
v___x_2732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2727_, v_declHint_2728_, v___y_2730_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2742_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2737_ = l_Lean_unknownIdentifierMessageTag;
v___x_2738_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_a_2733_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2738_);
v___x_2740_ = v___x_2735_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2743_, lean_object* v_declHint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2743_, v_declHint_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v_env_2754_; lean_object* v_options_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2753_ = lean_st_ref_get(v___y_2751_);
v_env_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_ref(v_env_2754_);
lean_dec(v___x_2753_);
v_options_2755_ = lean_ctor_get(v___y_2750_, 1);
v___x_2756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2757_ = lean_unsigned_to_nat(32u);
v___x_2758_ = lean_mk_empty_array_with_capacity(v___x_2757_);
lean_dec_ref(v___x_2758_);
v___x_2759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2755_);
v___x_2760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2760_, 0, v_env_2754_);
lean_ctor_set(v___x_2760_, 1, v___x_2756_);
lean_ctor_set(v___x_2760_, 2, v___x_2759_);
lean_ctor_set(v___x_2760_, 3, v_options_2755_);
v___x_2761_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v_msgData_2749_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_ref_2772_; lean_object* v___x_2773_; lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2782_; 
v_ref_2772_ = lean_ctor_get(v___y_2769_, 4);
v___x_2773_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2768_, v___y_2769_, v___y_2770_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_inc(v_ref_2772_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_ref_2772_);
lean_ctor_set(v___x_2778_, 1, v_a_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 1);
lean_ctor_set(v___x_2776_, 0, v___x_2778_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2788_, lean_object* v_msg_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_toCold_2793_; lean_object* v_options_2794_; lean_object* v_currRecDepth_2795_; lean_object* v_maxRecDepth_2796_; lean_object* v_ref_2797_; lean_object* v_currNamespace_2798_; lean_object* v_openDecls_2799_; lean_object* v_initHeartbeats_2800_; lean_object* v_maxHeartbeats_2801_; lean_object* v_currMacroScope_2802_; uint8_t v_diag_2803_; uint8_t v_suppressElabErrors_2804_; lean_object* v_ref_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_toCold_2793_ = lean_ctor_get(v___y_2790_, 0);
v_options_2794_ = lean_ctor_get(v___y_2790_, 1);
v_currRecDepth_2795_ = lean_ctor_get(v___y_2790_, 2);
v_maxRecDepth_2796_ = lean_ctor_get(v___y_2790_, 3);
v_ref_2797_ = lean_ctor_get(v___y_2790_, 4);
v_currNamespace_2798_ = lean_ctor_get(v___y_2790_, 5);
v_openDecls_2799_ = lean_ctor_get(v___y_2790_, 6);
v_initHeartbeats_2800_ = lean_ctor_get(v___y_2790_, 7);
v_maxHeartbeats_2801_ = lean_ctor_get(v___y_2790_, 8);
v_currMacroScope_2802_ = lean_ctor_get(v___y_2790_, 9);
v_diag_2803_ = lean_ctor_get_uint8(v___y_2790_, sizeof(void*)*10);
v_suppressElabErrors_2804_ = lean_ctor_get_uint8(v___y_2790_, sizeof(void*)*10 + 1);
v_ref_2805_ = l_Lean_replaceRef(v_ref_2788_, v_ref_2797_);
lean_inc(v_currMacroScope_2802_);
lean_inc(v_maxHeartbeats_2801_);
lean_inc(v_initHeartbeats_2800_);
lean_inc(v_openDecls_2799_);
lean_inc(v_currNamespace_2798_);
lean_inc(v_maxRecDepth_2796_);
lean_inc(v_currRecDepth_2795_);
lean_inc_ref(v_options_2794_);
lean_inc_ref(v_toCold_2793_);
v___x_2806_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2806_, 0, v_toCold_2793_);
lean_ctor_set(v___x_2806_, 1, v_options_2794_);
lean_ctor_set(v___x_2806_, 2, v_currRecDepth_2795_);
lean_ctor_set(v___x_2806_, 3, v_maxRecDepth_2796_);
lean_ctor_set(v___x_2806_, 4, v_ref_2805_);
lean_ctor_set(v___x_2806_, 5, v_currNamespace_2798_);
lean_ctor_set(v___x_2806_, 6, v_openDecls_2799_);
lean_ctor_set(v___x_2806_, 7, v_initHeartbeats_2800_);
lean_ctor_set(v___x_2806_, 8, v_maxHeartbeats_2801_);
lean_ctor_set(v___x_2806_, 9, v_currMacroScope_2802_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*10, v_diag_2803_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*10 + 1, v_suppressElabErrors_2804_);
v___x_2807_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2789_, v___x_2806_, v___y_2791_);
lean_dec_ref_known(v___x_2806_, 10);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2808_, lean_object* v_msg_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2808_, v_msg_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v_ref_2808_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2814_, lean_object* v_msg_2815_, lean_object* v_declHint_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; lean_object* v_a_2821_; lean_object* v___x_2822_; 
v___x_2820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2815_, v_declHint_2816_, v___y_2817_, v___y_2818_);
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2814_, v_a_2821_, v___y_2817_, v___y_2818_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2823_, lean_object* v_msg_2824_, lean_object* v_declHint_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2823_, v_msg_2824_, v_declHint_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v_ref_2823_);
return v_res_2829_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2836_, lean_object* v_constName_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2841_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2842_ = 0;
lean_inc(v_constName_2837_);
v___x_2843_ = l_Lean_MessageData_ofConstName(v_constName_2837_, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2841_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2836_, v___x_2846_, v_constName_2837_, v___y_2838_, v___y_2839_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2848_, lean_object* v_constName_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2848_, v_constName_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_ref_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_ref_2858_; lean_object* v___x_2859_; 
v_ref_2858_ = lean_ctor_get(v___y_2855_, 4);
v___x_2859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2858_, v_constName_2854_, v___y_2855_, v___y_2856_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v_env_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_st_ref_get(v___y_2867_);
v_env_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc_ref(v_env_2870_);
lean_dec(v___x_2869_);
v___x_2871_ = 0;
lean_inc(v_constName_2865_);
v___x_2872_ = l_Lean_Environment_find_x3f(v_env_2870_, v_constName_2865_, v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2865_, v___y_2866_, v___y_2867_);
return v___x_2873_;
}
else
{
lean_object* v_val_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_constName_2865_);
v_val_2874_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2872_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_val_2874_);
lean_dec(v___x_2872_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set_tag(v___x_2876_, 0);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_val_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Expr_getAppFn(v_type_2887_);
if (lean_obj_tag(v___x_2891_) == 4)
{
lean_object* v_declName_2892_; lean_object* v___x_2893_; 
v_declName_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_declName_2892_);
lean_dec_ref_known(v___x_2891_, 2);
v___x_2893_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2892_, v_a_2888_, v_a_2889_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2911_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2911_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2911_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
if (lean_obj_tag(v_a_2894_) == 5)
{
lean_object* v_val_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v_val_2898_ = lean_ctor_get(v_a_2894_, 0);
lean_inc_ref(v_val_2898_);
lean_dec_ref_known(v_a_2894_, 1);
v___x_2899_ = l_Lean_InductiveVal_numCtors(v_val_2898_);
lean_dec_ref(v_val_2898_);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = lean_nat_dec_le(v___x_2899_, v___x_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(v___x_2901_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2902_);
v___x_2904_ = v___x_2896_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
else
{
uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v_a_2894_);
v___x_2906_ = 0;
v___x_2907_ = lean_box(v___x_2906_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2907_);
v___x_2909_ = v___x_2896_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2893_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2893_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
uint8_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v___x_2891_);
v___x_2920_ = 0;
v___x_2921_ = lean_box(v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec_ref(v_type_2923_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2928_, lean_object* v_constName_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2929_, v___y_2930_, v___y_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2934_, lean_object* v_constName_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2934_, v_constName_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2940_, lean_object* v_ref_2941_, lean_object* v_constName_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2941_, v_constName_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_ref_2948_, lean_object* v_constName_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2947_, v_ref_2948_, v_constName_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v_ref_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2954_, lean_object* v_ref_2955_, lean_object* v_msg_2956_, lean_object* v_declHint_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2955_, v_msg_2956_, v_declHint_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v_msg_2964_, lean_object* v_declHint_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2962_, v_ref_2963_, v_msg_2964_, v_declHint_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_ref_2963_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2970_, lean_object* v_declHint_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2970_, v_declHint_2971_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2976_, lean_object* v_declHint_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2976_, v_declHint_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2983_, v_msg_2984_, v___y_2985_, v___y_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_ref_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2989_, v_ref_2990_, v_msg_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_ref_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2997_, v___y_2998_, v___y_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_msg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3002_, v_msg_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3008_, lean_object* v_fvarId_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_toGoalState_3015_; lean_object* v_mvarId_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3052_; 
v_toGoalState_3015_ = lean_ctor_get(v_goal_3008_, 0);
v_mvarId_3016_ = lean_ctor_get(v_goal_3008_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_goal_3008_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3018_ = v_goal_3008_;
v_isShared_3019_ = v_isSharedCheck_3052_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_mvarId_3016_);
lean_inc(v_toGoalState_3015_);
lean_dec(v_goal_3008_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3052_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3016_, v_fvarId_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3043_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3043_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3043_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
if (lean_obj_tag(v_a_3021_) == 1)
{
lean_object* v_val_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3038_; 
v_val_3025_ = lean_ctor_get(v_a_3021_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_3021_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3027_ = v_a_3021_;
v_isShared_3028_ = v_isSharedCheck_3038_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_val_3025_);
lean_dec(v_a_3021_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3038_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v_val_3025_);
v___x_3030_ = v___x_3018_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_toGoalState_3015_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_val_3025_);
v___x_3030_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3030_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3032_);
v___x_3034_ = v___x_3023_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_a_3021_);
lean_del_object(v___x_3018_);
lean_dec_ref(v_toGoalState_3015_);
v___x_3039_ = lean_box(0);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3039_);
v___x_3041_ = v___x_3023_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_del_object(v___x_3018_);
lean_dec_ref(v_toGoalState_3015_);
v_a_3044_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3020_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3020_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3053_, lean_object* v_fvarId_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3053_, v_fvarId_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3061_, v_x_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
v_a_3077_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3068_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3068_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3085_, lean_object* v_x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3085_, v_x_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3093_, lean_object* v_mvarId_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3094_, v_x_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_mvarId_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3102_, v_mvarId_3103_, v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3111_, lean_object* v_toGoalState_3112_, lean_object* v_goal_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
lean_inc(v_mvarId_3111_);
v___x_3119_ = l_Lean_MVarId_getType(v_mvarId_3111_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l_Lean_Meta_isProp(v_a_3120_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3148_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3148_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3148_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_unbox(v_a_3122_);
lean_dec(v_a_3122_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_del_object(v___x_3124_);
lean_dec_ref(v_goal_3113_);
v___x_3127_ = l_Lean_MVarId_exfalso(v_mvarId_3111_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_toGoalState_3112_);
lean_ctor_set(v___x_3132_, 1, v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_toGoalState_3112_);
v_a_3137_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3127_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3127_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v___x_3146_; 
lean_dec_ref(v_toGoalState_3112_);
lean_dec(v_mvarId_3111_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v_goal_3113_);
v___x_3146_ = v___x_3124_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_goal_3113_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v_goal_3113_);
lean_dec_ref(v_toGoalState_3112_);
lean_dec(v_mvarId_3111_);
v_a_3149_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3121_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3121_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v_goal_3113_);
lean_dec_ref(v_toGoalState_3112_);
lean_dec(v_mvarId_3111_);
v_a_3157_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3119_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3119_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3165_, lean_object* v_toGoalState_3166_, lean_object* v_goal_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3165_, v_toGoalState_3166_, v_goal_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_toGoalState_3180_; lean_object* v_mvarId_3181_; lean_object* v___f_3182_; lean_object* v___x_3183_; 
v_toGoalState_3180_ = lean_ctor_get(v_goal_3174_, 0);
lean_inc_ref(v_toGoalState_3180_);
v_mvarId_3181_ = lean_ctor_get(v_goal_3174_, 1);
lean_inc_n(v_mvarId_3181_, 2);
v___f_3182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3182_, 0, v_mvarId_3181_);
lean_closure_set(v___f_3182_, 1, v_toGoalState_3180_);
lean_closure_set(v___f_3182_, 2, v_goal_3174_);
v___x_3183_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3181_, v___f_3182_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_mvarId_3197_; lean_object* v___x_3198_; 
v_mvarId_3197_ = lean_ctor_get(v_goal_3191_, 1);
lean_inc(v_mvarId_3197_);
lean_dec_ref(v_goal_3191_);
v___x_3198_ = l_Lean_MVarId_getDecl(v_mvarId_3197_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3208_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_lctx_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v_lctx_3203_ = lean_ctor_get(v_a_3199_, 1);
lean_inc_ref(v_lctx_3203_);
lean_dec(v_a_3199_);
v___x_3204_ = l_Lean_LocalContext_lastDecl(v_lctx_3203_);
lean_dec_ref(v_lctx_3203_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3204_);
v___x_3206_ = v___x_3201_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v_a_3209_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3198_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3198_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
if (lean_obj_tag(v_a_3225_) == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = l_List_reverse___redArg(v_a_3226_);
return v___x_3227_;
}
else
{
lean_object* v_head_3228_; lean_object* v_tail_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3239_; 
v_head_3228_ = lean_ctor_get(v_a_3225_, 0);
v_tail_3229_ = lean_ctor_get(v_a_3225_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_a_3225_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3231_ = v_a_3225_;
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_tail_3229_);
lean_inc(v_head_3228_);
lean_dec(v_a_3225_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v_toGoalState_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v_toGoalState_3233_ = lean_ctor_get(v_goal_3224_, 0);
lean_inc_ref(v_toGoalState_3233_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_toGoalState_3233_);
lean_ctor_set(v___x_3234_, 1, v_head_3228_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v_a_3226_);
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_a_3226_);
v___x_3236_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
v_a_3225_ = v_tail_3229_;
v_a_3226_ = v___x_3236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3240_, v_a_3241_, v_a_3242_);
lean_dec_ref(v_goal_3240_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3244_, lean_object* v_as_x27_3245_, lean_object* v_b_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
if (lean_obj_tag(v_as_x27_3245_) == 0)
{
lean_object* v___x_3257_; 
lean_dec_ref(v_kp_3244_);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_b_3246_);
return v___x_3257_;
}
else
{
lean_object* v_head_3258_; lean_object* v_tail_3259_; lean_object* v___x_3260_; 
v_head_3258_ = lean_ctor_get(v_as_x27_3245_, 0);
v_tail_3259_ = lean_ctor_get(v_as_x27_3245_, 1);
lean_inc_ref(v_kp_3244_);
lean_inc(v___y_3255_);
lean_inc_ref(v___y_3254_);
lean_inc(v___y_3253_);
lean_inc_ref(v___y_3252_);
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
lean_inc(v_head_3258_);
v___x_3260_ = lean_apply_11(v_kp_3244_, v_head_3258_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, lean_box(0));
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
if (lean_obj_tag(v_a_3261_) == 0)
{
lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3273_; 
v_fst_3262_ = lean_ctor_get(v_b_3246_, 0);
v_snd_3263_ = lean_ctor_get(v_b_3246_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_b_3246_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3265_ = v_b_3246_;
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_snd_3263_);
lean_inc(v_fst_3262_);
lean_dec(v_b_3246_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3273_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_seq_3267_; lean_object* v___x_3268_; lean_object* v___x_3270_; 
v_seq_3267_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_seq_3267_);
lean_dec_ref_known(v_a_3261_, 1);
v___x_3268_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3262_, v_seq_3267_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3268_);
v___x_3270_ = v___x_3265_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_snd_3263_);
v___x_3270_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
v_as_x27_3245_ = v_tail_3259_;
v_b_3246_ = v___x_3270_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3285_; 
v_fst_3274_ = lean_ctor_get(v_b_3246_, 0);
v_snd_3275_ = lean_ctor_get(v_b_3246_, 1);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_b_3246_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3277_ = v_b_3246_;
v_isShared_3278_ = v_isSharedCheck_3285_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_snd_3275_);
lean_inc(v_fst_3274_);
lean_dec(v_b_3246_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3285_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_gs_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v_gs_3279_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_gs_3279_);
lean_dec_ref_known(v_a_3261_, 1);
v___x_3280_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3275_, v_gs_3279_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3280_);
v___x_3282_ = v___x_3277_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_fst_3274_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
v_as_x27_3245_ = v_tail_3259_;
v_b_3246_ = v___x_3282_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v_b_3246_);
lean_dec_ref(v_kp_3244_);
v_a_3286_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3260_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3260_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3294_, lean_object* v_as_x27_3295_, lean_object* v_b_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3294_, v_as_x27_3295_, v_b_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v_as_x27_3295_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3312_, lean_object* v_mvarId_3313_, lean_object* v_goal_3314_, lean_object* v_kp_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___x_3381_; 
lean_inc(v_fvarId_3312_);
v___x_3381_ = l_Lean_FVarId_getType___redArg(v_fvarId_3312_, v___y_3321_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
lean_inc(v___y_3324_);
lean_inc_ref(v___y_3323_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
v___x_3383_ = lean_whnf(v_a_3382_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___x_3406_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3406_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3384_, v___y_3317_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3446_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3446_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3446_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_unbox(v_a_3407_);
lean_dec(v_a_3407_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_dec(v_a_3384_);
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v___x_3412_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3412_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
else
{
lean_object* v___x_3416_; 
lean_del_object(v___x_3409_);
v___x_3416_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3317_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; uint8_t v___x_3418_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v___x_3418_ = lean_unbox(v_a_3417_);
lean_dec(v_a_3417_);
if (v___x_3418_ == 0)
{
v___y_3386_ = v___y_3316_;
v___y_3387_ = v___y_3317_;
v___y_3388_ = v___y_3318_;
v___y_3389_ = v___y_3319_;
v___y_3390_ = v___y_3320_;
v___y_3391_ = v___y_3321_;
v___y_3392_ = v___y_3322_;
v___y_3393_ = v___y_3323_;
v___y_3394_ = v___y_3324_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3384_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3429_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_unbox(v_a_3420_);
lean_dec(v_a_3420_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_dec(v_a_3384_);
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v___x_3425_ = lean_box(0);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
else
{
lean_del_object(v___x_3422_);
v___y_3386_ = v___y_3316_;
v___y_3387_ = v___y_3317_;
v___y_3388_ = v___y_3318_;
v___y_3389_ = v___y_3319_;
v___y_3390_ = v___y_3320_;
v___y_3391_ = v___y_3321_;
v___y_3392_ = v___y_3322_;
v___y_3393_ = v___y_3323_;
v___y_3394_ = v___y_3324_;
goto v___jp_3385_;
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_a_3384_);
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3430_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3419_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3419_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_a_3384_);
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3438_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3416_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3416_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_a_3384_);
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3447_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3406_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3406_);
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
v___jp_3385_:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Expr_getAppFn(v_a_3384_);
lean_dec(v_a_3384_);
if (lean_obj_tag(v___x_3395_) == 4)
{
lean_object* v_declName_3396_; lean_object* v___x_3397_; 
v_declName_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_declName_3396_);
lean_dec_ref_known(v___x_3395_, 2);
v___x_3397_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3396_, v___y_3388_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_dec_ref_known(v___x_3397_, 1);
v___y_3327_ = v___y_3386_;
v___y_3328_ = v___y_3387_;
v___y_3329_ = v___y_3388_;
v___y_3330_ = v___y_3389_;
v___y_3331_ = v___y_3390_;
v___y_3332_ = v___y_3391_;
v___y_3333_ = v___y_3392_;
v___y_3334_ = v___y_3393_;
v___y_3335_ = v___y_3394_;
goto v___jp_3326_;
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_dec_ref(v___x_3395_);
v___y_3327_ = v___y_3386_;
v___y_3328_ = v___y_3387_;
v___y_3329_ = v___y_3388_;
v___y_3330_ = v___y_3389_;
v___y_3331_ = v___y_3390_;
v___y_3332_ = v___y_3391_;
v___y_3333_ = v___y_3392_;
v___y_3334_ = v___y_3393_;
v___y_3335_ = v___y_3394_;
goto v___jp_3326_;
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3455_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3383_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3383_);
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
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v_kp_3315_);
lean_dec(v_mvarId_3313_);
lean_dec(v_fvarId_3312_);
v_a_3463_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3381_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3381_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
v___jp_3326_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = l_Lean_mkFVar(v_fvarId_3312_);
v___x_3337_ = l_Lean_Meta_Grind_cases(v_mvarId_3313_, v___x_3336_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = lean_box(0);
v___x_3340_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3314_, v_a_3338_, v___x_3339_);
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3343_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3315_, v___x_3340_, v___x_3342_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___x_3340_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3364_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3364_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3364_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_fst_3348_; lean_object* v_snd_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_fst_3348_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_fst_3348_);
v_snd_3349_ = lean_ctor_get(v_a_3344_, 1);
lean_inc(v_snd_3349_);
lean_dec(v_a_3344_);
v___x_3350_ = lean_array_get_size(v_snd_3349_);
v___x_3351_ = lean_nat_dec_eq(v___x_3350_, v___x_3341_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_fst_3348_);
v___x_3352_ = lean_array_to_list(v_snd_3349_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3354_);
v___x_3356_ = v___x_3346_;
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
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_dec(v_snd_3349_);
v___x_3358_ = lean_array_to_list(v_fst_3348_);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3360_);
v___x_3362_ = v___x_3346_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
v_a_3365_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3343_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3343_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v_kp_3315_);
v_a_3373_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3337_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3337_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3471_, lean_object* v_mvarId_3472_, lean_object* v_goal_3473_, lean_object* v_kp_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3471_, v_mvarId_3472_, v_goal_3473_, v_kp_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v_goal_3473_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3486_, lean_object* v_fvarId_3487_, lean_object* v_kp_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_mvarId_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; 
v_mvarId_3499_ = lean_ctor_get(v_goal_3486_, 1);
lean_inc_n(v_mvarId_3499_, 2);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3500_, 0, v_fvarId_3487_);
lean_closure_set(v___f_3500_, 1, v_mvarId_3499_);
lean_closure_set(v___f_3500_, 2, v_goal_3486_);
lean_closure_set(v___f_3500_, 3, v_kp_3488_);
v___x_3501_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3499_, v___f_3500_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3502_, lean_object* v_fvarId_3503_, lean_object* v_kp_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3502_, v_fvarId_3503_, v_kp_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3516_, lean_object* v_as_3517_, lean_object* v_as_x27_3518_, lean_object* v_b_3519_, lean_object* v_a_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3516_, v_as_x27_3518_, v_b_3519_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3532_, lean_object* v_as_3533_, lean_object* v_as_x27_3534_, lean_object* v_b_3535_, lean_object* v_a_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3532_, v_as_3533_, v_as_x27_3534_, v_b_3535_, v_a_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec(v_as_x27_3534_);
lean_dec(v_as_3533_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3548_, lean_object* v_fvarId_3549_, lean_object* v_generation_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_st_mk_ref(v_goal_3548_);
v___x_3562_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3549_, v_generation_3550_, v___x_3561_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3571_; 
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v___x_3562_, 0);
lean_dec(v_unused_3572_);
v___x_3564_ = v___x_3562_;
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
else
{
lean_dec(v___x_3562_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3566_ = lean_st_ref_get(v___x_3561_);
v___x_3567_ = lean_st_ref_get(v___x_3561_);
lean_dec(v___x_3561_);
lean_dec(v___x_3567_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3566_);
v___x_3569_ = v___x_3564_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3566_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v___x_3561_);
v_a_3573_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3562_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3562_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3581_, lean_object* v_fvarId_3582_, lean_object* v_generation_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3581_, v_fvarId_3582_, v_generation_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3597_, lean_object* v_goal_3598_, lean_object* v_kna_3599_, lean_object* v_kp_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_toGoalState_3611_; uint8_t v_inconsistent_3612_; 
v_toGoalState_3611_ = lean_ctor_get(v_goal_3598_, 0);
v_inconsistent_3612_ = lean_ctor_get_uint8(v_toGoalState_3611_, sizeof(void*)*17);
if (v_inconsistent_3612_ == 0)
{
lean_object* v_mvarId_3613_; lean_object* v___x_3614_; 
v_mvarId_3613_ = lean_ctor_get(v_goal_3598_, 1);
lean_inc(v_mvarId_3613_);
v___x_3614_ = l_Lean_MVarId_getType(v_mvarId_3613_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; uint8_t v___x_3616_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
v___x_3616_ = l_Lean_Expr_isFalse(v_a_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref(v_kna_3599_);
lean_inc(v_generation_3597_);
v___x_3617_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3598_, v_generation_3597_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
switch(lean_obj_tag(v_a_3618_))
{
case 0:
{
lean_object* v_goal_3619_; lean_object* v___x_3620_; 
lean_dec(v_generation_3597_);
v_goal_3619_ = lean_ctor_get(v_a_3618_, 0);
lean_inc_ref(v_goal_3619_);
lean_dec_ref_known(v_a_3618_, 1);
v___x_3620_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3619_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_toGoalState_3622_; lean_object* v_mvarId_3623_; lean_object* v___x_3624_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v_toGoalState_3622_ = lean_ctor_get(v_a_3621_, 0);
v_mvarId_3623_ = lean_ctor_get(v_a_3621_, 1);
lean_inc(v_mvarId_3623_);
v___x_3624_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3623_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
if (lean_obj_tag(v_a_3625_) == 1)
{
lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3634_; 
lean_inc_ref(v_toGoalState_3622_);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_a_3621_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; lean_object* v_unused_3636_; 
v_unused_3635_ = lean_ctor_get(v_a_3621_, 1);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_a_3621_, 0);
lean_dec(v_unused_3636_);
v___x_3627_ = v_a_3621_;
v_isShared_3628_ = v_isSharedCheck_3634_;
goto v_resetjp_3626_;
}
else
{
lean_dec(v_a_3621_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3634_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_val_3629_; lean_object* v___x_3631_; 
v_val_3629_ = lean_ctor_get(v_a_3625_, 0);
lean_inc(v_val_3629_);
lean_dec_ref_known(v_a_3625_, 1);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 1, v_val_3629_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_toGoalState_3622_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_val_3629_);
v___x_3631_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; 
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3632_ = lean_apply_11(v_kp_3600_, v___x_3631_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3632_;
}
}
}
else
{
lean_object* v___x_3637_; 
lean_dec(v_a_3625_);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3637_ = lean_apply_11(v_kp_3600_, v_a_3621_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3637_;
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3621_);
lean_dec_ref(v_kp_3600_);
v_a_3638_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3624_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3624_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_kp_3600_);
v_a_3646_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3620_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3620_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3654_; lean_object* v_goal_3655_; lean_object* v___x_3656_; 
v_fvarId_3654_ = lean_ctor_get(v_a_3618_, 0);
lean_inc_n(v_fvarId_3654_, 2);
v_goal_3655_ = lean_ctor_get(v_a_3618_, 1);
lean_inc_ref_n(v_goal_3655_, 2);
lean_dec_ref_known(v_a_3618_, 2);
v___x_3656_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3655_, v_fvarId_3654_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
if (lean_obj_tag(v_a_3657_) == 1)
{
lean_object* v_val_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_goal_3655_);
lean_dec(v_fvarId_3654_);
lean_dec(v_generation_3597_);
v_val_3658_ = lean_ctor_get(v_a_3657_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v_a_3657_, 1);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3659_ = lean_apply_11(v_kp_3600_, v_val_3658_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3659_;
}
else
{
lean_object* v___x_3660_; 
lean_dec(v_a_3657_);
lean_inc_ref(v_kp_3600_);
lean_inc(v_fvarId_3654_);
lean_inc_ref(v_goal_3655_);
v___x_3660_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3655_, v_fvarId_3654_, v_kp_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3682_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3682_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3682_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
if (lean_obj_tag(v_a_3661_) == 1)
{
lean_object* v_val_3665_; lean_object* v___x_3667_; 
lean_dec_ref(v_goal_3655_);
lean_dec(v_fvarId_3654_);
lean_dec_ref(v_kp_3600_);
lean_dec(v_generation_3597_);
v_val_3665_ = lean_ctor_get(v_a_3661_, 0);
lean_inc(v_val_3665_);
lean_dec_ref_known(v_a_3661_, 1);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v_val_3665_);
v___x_3667_ = v___x_3663_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_val_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
else
{
lean_object* v_mvarId_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; 
lean_del_object(v___x_3663_);
lean_dec(v_a_3661_);
v_mvarId_3669_ = lean_ctor_get(v_goal_3655_, 1);
lean_inc(v_mvarId_3669_);
v___f_3670_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3670_, 0, v_goal_3655_);
lean_closure_set(v___f_3670_, 1, v_fvarId_3654_);
lean_closure_set(v___f_3670_, 2, v_generation_3597_);
v___x_3671_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3669_, v___f_3670_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3673_ = lean_apply_11(v_kp_3600_, v_a_3672_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3673_;
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_kp_3600_);
v_a_3674_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3671_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3671_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v_goal_3655_);
lean_dec(v_fvarId_3654_);
lean_dec_ref(v_kp_3600_);
lean_dec(v_generation_3597_);
v_a_3683_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3660_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3660_);
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
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_goal_3655_);
lean_dec(v_fvarId_3654_);
lean_dec_ref(v_kp_3600_);
lean_dec(v_generation_3597_);
v_a_3691_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3656_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3656_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
case 2:
{
lean_object* v_goal_3699_; lean_object* v___x_3700_; 
lean_dec(v_generation_3597_);
v_goal_3699_ = lean_ctor_get(v_a_3618_, 0);
lean_inc_ref(v_goal_3699_);
lean_dec_ref_known(v_a_3618_, 1);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3700_ = lean_apply_11(v_kp_3600_, v_goal_3699_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3700_;
}
default: 
{
lean_object* v_fvarId_3701_; lean_object* v_goal_3702_; lean_object* v___x_3703_; 
lean_dec(v_generation_3597_);
v_fvarId_3701_ = lean_ctor_get(v_a_3618_, 0);
lean_inc(v_fvarId_3701_);
v_goal_3702_ = lean_ctor_get(v_a_3618_, 1);
lean_inc_ref_n(v_goal_3702_, 2);
lean_dec_ref_known(v_a_3618_, 2);
lean_inc_ref(v_kp_3600_);
v___x_3703_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3702_, v_fvarId_3701_, v_kp_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3713_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3713_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3713_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
if (lean_obj_tag(v_a_3704_) == 1)
{
lean_object* v_val_3708_; lean_object* v___x_3710_; 
lean_dec_ref(v_goal_3702_);
lean_dec_ref(v_kp_3600_);
v_val_3708_ = lean_ctor_get(v_a_3704_, 0);
lean_inc(v_val_3708_);
lean_dec_ref_known(v_a_3704_, 1);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v_val_3708_);
v___x_3710_ = v___x_3706_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_val_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3712_; 
lean_del_object(v___x_3706_);
lean_dec(v_a_3704_);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3712_ = lean_apply_11(v_kp_3600_, v_goal_3702_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3712_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v_goal_3702_);
lean_dec_ref(v_kp_3600_);
v_a_3714_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3703_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3703_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v_kp_3600_);
lean_dec(v_generation_3597_);
v_a_3722_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3617_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3617_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref(v_kp_3600_);
lean_dec(v_generation_3597_);
lean_inc(v_a_3609_);
lean_inc_ref(v_a_3608_);
lean_inc(v_a_3607_);
lean_inc_ref(v_a_3606_);
lean_inc(v_a_3605_);
lean_inc_ref(v_a_3604_);
lean_inc(v_a_3603_);
lean_inc_ref(v_a_3602_);
lean_inc(v_a_3601_);
v___x_3730_ = lean_apply_11(v_kna_3599_, v_goal_3598_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, lean_box(0));
return v___x_3730_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v_kp_3600_);
lean_dec_ref(v_kna_3599_);
lean_dec_ref(v_goal_3598_);
lean_dec(v_generation_3597_);
v_a_3731_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3614_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3614_);
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
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec_ref(v_kp_3600_);
lean_dec_ref(v_kna_3599_);
lean_dec_ref(v_goal_3598_);
lean_dec(v_generation_3597_);
v___x_3739_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3741_, lean_object* v_goal_3742_, lean_object* v_kna_3743_, lean_object* v_kp_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Meta_Grind_Action_intro(v_generation_3741_, v_goal_3742_, v_kna_3743_, v_kp_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
return v_res_3755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_unsigned_to_nat(1000000u);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3757_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3772_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3785_, lean_object* v___f_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3800_ = lean_unsigned_to_nat(1000000u);
v___x_3801_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3801_, 0, v_generation_3785_);
v___x_3802_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3802_, 0, v___x_3800_);
lean_closure_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l_Lean_Meta_Grind_Action_andThen(v___x_3802_, v___f_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3804_, lean_object* v___f_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3804_, v___f_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3822_, lean_object* v_a_3823_, lean_object* v_kna_3824_, lean_object* v_kp_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___f_3836_; lean_object* v___f_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___f_3836_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3837_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3837_, 0, v_generation_3822_);
lean_closure_set(v___f_3837_, 1, v___f_3836_);
v___x_3838_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3839_ = l_Lean_Meta_Grind_Action_andThen(v___x_3838_, v___f_3837_, v_a_3823_, v_kna_3824_, v_kp_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3840_, lean_object* v_a_3841_, lean_object* v_kna_3842_, lean_object* v_kp_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Meta_Grind_Action_intros(v_generation_3840_, v_a_3841_, v_kna_3842_, v_kp_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
return v_res_3854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3864_ = l_Lean_mkConst(v___x_3863_, v___x_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3865_, lean_object* v_prop_3866_, lean_object* v_proof_3867_, lean_object* v_generation_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_st_mk_ref(v_goal_3865_);
lean_inc(v___y_3877_);
lean_inc_ref(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
lean_inc(v___y_3873_);
lean_inc_ref(v___y_3872_);
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc(v___x_3879_);
lean_inc_ref(v_prop_3866_);
v___x_3880_ = lean_grind_preprocess(v_prop_3866_, v___x_3879_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v_expr_3882_; lean_object* v___x_3883_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v_expr_3882_ = lean_ctor_get(v_a_3881_, 0);
lean_inc_ref(v_expr_3882_);
v___x_3883_ = l_Lean_Meta_Simp_Result_getProof(v_a_3881_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3882_);
v___x_3886_ = l_Lean_mkApp4(v___x_3885_, v_prop_3866_, v_expr_3882_, v_a_3884_, v_proof_3867_);
v___x_3887_ = l_Lean_Meta_Grind_add(v_expr_3882_, v___x_3886_, v_generation_3868_, v___x_3879_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3896_; 
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v___x_3887_, 0);
lean_dec(v_unused_3897_);
v___x_3889_ = v___x_3887_;
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v___x_3887_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3891_ = lean_st_ref_get(v___x_3879_);
v___x_3892_ = lean_st_ref_get(v___x_3879_);
lean_dec(v___x_3879_);
lean_dec(v___x_3892_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3891_);
v___x_3894_ = v___x_3889_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3891_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec(v___x_3879_);
v_a_3898_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3887_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3887_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v_expr_3882_);
lean_dec(v___x_3879_);
lean_dec(v_generation_3868_);
lean_dec_ref(v_proof_3867_);
lean_dec_ref(v_prop_3866_);
v_a_3906_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3883_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3883_);
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
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v___x_3879_);
lean_dec(v_generation_3868_);
lean_dec_ref(v_proof_3867_);
lean_dec_ref(v_prop_3866_);
v_a_3914_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3880_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3880_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3922_, lean_object* v_prop_3923_, lean_object* v_proof_3924_, lean_object* v_generation_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3922_, v_prop_3923_, v_proof_3924_, v_generation_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3937_, lean_object* v___f_3938_, lean_object* v_kp_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3937_, v___f_3938_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3952_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
lean_inc(v___y_3948_);
lean_inc_ref(v___y_3947_);
lean_inc(v___y_3946_);
lean_inc_ref(v___y_3945_);
lean_inc(v___y_3944_);
lean_inc_ref(v___y_3943_);
lean_inc(v___y_3942_);
lean_inc_ref(v___y_3941_);
lean_inc(v___y_3940_);
v___x_3952_ = lean_apply_11(v_kp_3939_, v_a_3951_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, lean_box(0));
return v___x_3952_;
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v_kp_3939_);
v_a_3953_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3950_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3950_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3961_, lean_object* v___f_3962_, lean_object* v_kp_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3961_, v___f_3962_, v_kp_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3975_, lean_object* v_prop_3976_, lean_object* v_generation_3977_, lean_object* v_goal_3978_, lean_object* v_kna_3979_, lean_object* v_kp_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3976_, v_a_3982_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; uint8_t v___x_3993_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v___x_3993_ = lean_unbox(v_a_3992_);
lean_dec(v_a_3992_);
if (v___x_3993_ == 0)
{
lean_object* v_mvarId_3994_; lean_object* v___f_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; 
lean_dec_ref(v_kna_3979_);
v_mvarId_3994_ = lean_ctor_get(v_goal_3978_, 1);
lean_inc_n(v_mvarId_3994_, 2);
v___f_3995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3995_, 0, v_goal_3978_);
lean_closure_set(v___f_3995_, 1, v_prop_3976_);
lean_closure_set(v___f_3995_, 2, v_proof_3975_);
lean_closure_set(v___f_3995_, 3, v_generation_3977_);
v___f_3996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_3996_, 0, v_mvarId_3994_);
lean_closure_set(v___f_3996_, 1, v___f_3995_);
lean_closure_set(v___f_3996_, 2, v_kp_3980_);
v___x_3997_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3994_, v___f_3996_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_3999_ = l_Lean_Core_mkFreshUserName(v___x_3998_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_toGoalState_4001_; lean_object* v_mvarId_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4020_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_toGoalState_4001_ = lean_ctor_get(v_goal_3978_, 0);
v_mvarId_4002_ = lean_ctor_get(v_goal_3978_, 1);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_goal_3978_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4004_ = v_goal_3978_;
v_isShared_4005_ = v_isSharedCheck_4020_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_mvarId_4002_);
lean_inc(v_toGoalState_4001_);
lean_dec(v_goal_3978_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4020_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_MVarId_assert(v_mvarId_4002_, v_a_4000_, v_prop_3976_, v_proof_3975_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4009_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 1, v_a_4007_);
v___x_4009_ = v___x_4004_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_toGoalState_4001_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_a_4007_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Meta_Grind_Action_intros(v_generation_3977_, v___x_4009_, v_kna_3979_, v_kp_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
return v___x_4010_;
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_del_object(v___x_4004_);
lean_dec_ref(v_toGoalState_4001_);
lean_dec_ref(v_kp_3980_);
lean_dec_ref(v_kna_3979_);
lean_dec(v_generation_3977_);
v_a_4012_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4006_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4006_);
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
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v_kp_3980_);
lean_dec_ref(v_kna_3979_);
lean_dec_ref(v_goal_3978_);
lean_dec(v_generation_3977_);
lean_dec_ref(v_prop_3976_);
lean_dec_ref(v_proof_3975_);
v_a_4021_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3999_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3999_);
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
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v_kp_3980_);
lean_dec_ref(v_kna_3979_);
lean_dec_ref(v_goal_3978_);
lean_dec(v_generation_3977_);
lean_dec_ref(v_prop_3976_);
lean_dec_ref(v_proof_3975_);
v_a_4029_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_3991_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_3991_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4037_, lean_object* v_prop_4038_, lean_object* v_generation_4039_, lean_object* v_goal_4040_, lean_object* v_kna_4041_, lean_object* v_kp_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4037_, v_prop_4038_, v_generation_4039_, v_goal_4040_, v_kna_4041_, v_kp_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4054_, lean_object* v_kna_4055_, lean_object* v_kp_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_toGoalState_4067_; uint8_t v_inconsistent_4068_; 
v_toGoalState_4067_ = lean_ctor_get(v_goal_4054_, 0);
lean_inc_ref(v_toGoalState_4067_);
v_inconsistent_4068_ = lean_ctor_get_uint8(v_toGoalState_4067_, sizeof(void*)*17);
if (v_inconsistent_4068_ == 0)
{
lean_object* v_mvarId_4069_; lean_object* v_nextDeclIdx_4070_; lean_object* v_enodeMap_4071_; lean_object* v_exprs_4072_; lean_object* v_parents_4073_; lean_object* v_congrTable_4074_; lean_object* v_appMap_4075_; lean_object* v_indicesFound_4076_; lean_object* v_newFacts_4077_; lean_object* v_nextIdx_4078_; lean_object* v_newRawFacts_4079_; lean_object* v_facts_4080_; lean_object* v_extThms_4081_; lean_object* v_ematch_4082_; lean_object* v_inj_4083_; lean_object* v_split_4084_; lean_object* v_clean_4085_; lean_object* v_sstates_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4124_; 
v_mvarId_4069_ = lean_ctor_get(v_goal_4054_, 1);
v_nextDeclIdx_4070_ = lean_ctor_get(v_toGoalState_4067_, 0);
v_enodeMap_4071_ = lean_ctor_get(v_toGoalState_4067_, 1);
v_exprs_4072_ = lean_ctor_get(v_toGoalState_4067_, 2);
v_parents_4073_ = lean_ctor_get(v_toGoalState_4067_, 3);
v_congrTable_4074_ = lean_ctor_get(v_toGoalState_4067_, 4);
v_appMap_4075_ = lean_ctor_get(v_toGoalState_4067_, 5);
v_indicesFound_4076_ = lean_ctor_get(v_toGoalState_4067_, 6);
v_newFacts_4077_ = lean_ctor_get(v_toGoalState_4067_, 7);
v_nextIdx_4078_ = lean_ctor_get(v_toGoalState_4067_, 8);
v_newRawFacts_4079_ = lean_ctor_get(v_toGoalState_4067_, 9);
v_facts_4080_ = lean_ctor_get(v_toGoalState_4067_, 10);
v_extThms_4081_ = lean_ctor_get(v_toGoalState_4067_, 11);
v_ematch_4082_ = lean_ctor_get(v_toGoalState_4067_, 12);
v_inj_4083_ = lean_ctor_get(v_toGoalState_4067_, 13);
v_split_4084_ = lean_ctor_get(v_toGoalState_4067_, 14);
v_clean_4085_ = lean_ctor_get(v_toGoalState_4067_, 15);
v_sstates_4086_ = lean_ctor_get(v_toGoalState_4067_, 16);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_toGoalState_4067_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4088_ = v_toGoalState_4067_;
v_isShared_4089_ = v_isSharedCheck_4124_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_sstates_4086_);
lean_inc(v_clean_4085_);
lean_inc(v_split_4084_);
lean_inc(v_inj_4083_);
lean_inc(v_ematch_4082_);
lean_inc(v_extThms_4081_);
lean_inc(v_facts_4080_);
lean_inc(v_newRawFacts_4079_);
lean_inc(v_nextIdx_4078_);
lean_inc(v_newFacts_4077_);
lean_inc(v_indicesFound_4076_);
lean_inc(v_appMap_4075_);
lean_inc(v_congrTable_4074_);
lean_inc(v_parents_4073_);
lean_inc(v_exprs_4072_);
lean_inc(v_enodeMap_4071_);
lean_inc(v_nextDeclIdx_4070_);
lean_dec(v_toGoalState_4067_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4124_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4079_);
if (lean_obj_tag(v___x_4090_) == 1)
{
lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4120_; 
lean_inc(v_mvarId_4069_);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_goal_4054_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; lean_object* v_unused_4122_; 
v_unused_4121_ = lean_ctor_get(v_goal_4054_, 1);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_goal_4054_, 0);
lean_dec(v_unused_4122_);
v___x_4092_ = v_goal_4054_;
v_isShared_4093_ = v_isSharedCheck_4120_;
goto v_resetjp_4091_;
}
else
{
lean_dec(v_goal_4054_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4120_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v_val_4094_; lean_object* v_fst_4095_; lean_object* v_snd_4096_; lean_object* v_proof_4097_; lean_object* v_prop_4098_; lean_object* v_generation_4099_; lean_object* v_splitSource_4100_; lean_object* v_ematchDiagSource_4101_; lean_object* v_simp_4102_; lean_object* v_simpMethods_4103_; lean_object* v_config_4104_; lean_object* v_anchorRefs_x3f_4105_; uint8_t v_cheapCases_4106_; uint8_t v_reportMVarIssue_4107_; lean_object* v_symPrios_4108_; lean_object* v_extensions_4109_; uint8_t v_debug_4110_; uint8_t v_ematchDiag_4111_; lean_object* v___x_4113_; 
v_val_4094_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_val_4094_);
lean_dec_ref_known(v___x_4090_, 1);
v_fst_4095_ = lean_ctor_get(v_val_4094_, 0);
lean_inc(v_fst_4095_);
v_snd_4096_ = lean_ctor_get(v_val_4094_, 1);
lean_inc(v_snd_4096_);
lean_dec(v_val_4094_);
v_proof_4097_ = lean_ctor_get(v_fst_4095_, 0);
lean_inc_ref(v_proof_4097_);
v_prop_4098_ = lean_ctor_get(v_fst_4095_, 1);
lean_inc_ref(v_prop_4098_);
v_generation_4099_ = lean_ctor_get(v_fst_4095_, 2);
lean_inc(v_generation_4099_);
v_splitSource_4100_ = lean_ctor_get(v_fst_4095_, 3);
lean_inc(v_splitSource_4100_);
v_ematchDiagSource_4101_ = lean_ctor_get(v_fst_4095_, 4);
lean_inc(v_ematchDiagSource_4101_);
lean_dec(v_fst_4095_);
v_simp_4102_ = lean_ctor_get(v_a_4058_, 0);
v_simpMethods_4103_ = lean_ctor_get(v_a_4058_, 1);
v_config_4104_ = lean_ctor_get(v_a_4058_, 2);
v_anchorRefs_x3f_4105_ = lean_ctor_get(v_a_4058_, 3);
v_cheapCases_4106_ = lean_ctor_get_uint8(v_a_4058_, sizeof(void*)*8);
v_reportMVarIssue_4107_ = lean_ctor_get_uint8(v_a_4058_, sizeof(void*)*8 + 1);
v_symPrios_4108_ = lean_ctor_get(v_a_4058_, 6);
v_extensions_4109_ = lean_ctor_get(v_a_4058_, 7);
v_debug_4110_ = lean_ctor_get_uint8(v_a_4058_, sizeof(void*)*8 + 2);
v_ematchDiag_4111_ = lean_ctor_get_uint8(v_a_4058_, sizeof(void*)*8 + 3);
if (v_isShared_4089_ == 0)
{
lean_ctor_set(v___x_4088_, 9, v_snd_4096_);
v___x_4113_ = v___x_4088_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_nextDeclIdx_4070_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_enodeMap_4071_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_exprs_4072_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_parents_4073_);
lean_ctor_set(v_reuseFailAlloc_4119_, 4, v_congrTable_4074_);
lean_ctor_set(v_reuseFailAlloc_4119_, 5, v_appMap_4075_);
lean_ctor_set(v_reuseFailAlloc_4119_, 6, v_indicesFound_4076_);
lean_ctor_set(v_reuseFailAlloc_4119_, 7, v_newFacts_4077_);
lean_ctor_set(v_reuseFailAlloc_4119_, 8, v_nextIdx_4078_);
lean_ctor_set(v_reuseFailAlloc_4119_, 9, v_snd_4096_);
lean_ctor_set(v_reuseFailAlloc_4119_, 10, v_facts_4080_);
lean_ctor_set(v_reuseFailAlloc_4119_, 11, v_extThms_4081_);
lean_ctor_set(v_reuseFailAlloc_4119_, 12, v_ematch_4082_);
lean_ctor_set(v_reuseFailAlloc_4119_, 13, v_inj_4083_);
lean_ctor_set(v_reuseFailAlloc_4119_, 14, v_split_4084_);
lean_ctor_set(v_reuseFailAlloc_4119_, 15, v_clean_4085_);
lean_ctor_set(v_reuseFailAlloc_4119_, 16, v_sstates_4086_);
lean_ctor_set_uint8(v_reuseFailAlloc_4119_, sizeof(void*)*17, v_inconsistent_4068_);
v___x_4113_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v_goal_4115_; 
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4113_);
v_goal_4115_ = v___x_4092_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_mvarId_4069_);
v_goal_4115_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_inc_ref(v_extensions_4109_);
lean_inc_ref(v_symPrios_4108_);
lean_inc(v_anchorRefs_x3f_4105_);
lean_inc_ref(v_config_4104_);
lean_inc_ref(v_simpMethods_4103_);
lean_inc_ref(v_simp_4102_);
v___x_4116_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_4116_, 0, v_simp_4102_);
lean_ctor_set(v___x_4116_, 1, v_simpMethods_4103_);
lean_ctor_set(v___x_4116_, 2, v_config_4104_);
lean_ctor_set(v___x_4116_, 3, v_anchorRefs_x3f_4105_);
lean_ctor_set(v___x_4116_, 4, v_splitSource_4100_);
lean_ctor_set(v___x_4116_, 5, v_ematchDiagSource_4101_);
lean_ctor_set(v___x_4116_, 6, v_symPrios_4108_);
lean_ctor_set(v___x_4116_, 7, v_extensions_4109_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*8, v_cheapCases_4106_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*8 + 1, v_reportMVarIssue_4107_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*8 + 2, v_debug_4110_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*8 + 3, v_ematchDiag_4111_);
v___x_4117_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4097_, v_prop_4098_, v_generation_4099_, v_goal_4115_, v_kna_4055_, v_kp_4056_, v_a_4057_, v___x_4116_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
lean_dec_ref_known(v___x_4116_, 8);
return v___x_4117_;
}
}
}
}
else
{
lean_object* v___x_4123_; 
lean_dec(v___x_4090_);
lean_del_object(v___x_4088_);
lean_dec_ref(v_sstates_4086_);
lean_dec_ref(v_clean_4085_);
lean_dec_ref(v_split_4084_);
lean_dec_ref(v_inj_4083_);
lean_dec_ref(v_ematch_4082_);
lean_dec_ref(v_extThms_4081_);
lean_dec_ref(v_facts_4080_);
lean_dec(v_nextIdx_4078_);
lean_dec_ref(v_newFacts_4077_);
lean_dec_ref(v_indicesFound_4076_);
lean_dec_ref(v_appMap_4075_);
lean_dec_ref(v_congrTable_4074_);
lean_dec_ref(v_parents_4073_);
lean_dec_ref(v_exprs_4072_);
lean_dec_ref(v_enodeMap_4071_);
lean_dec(v_nextDeclIdx_4070_);
lean_dec_ref(v_kp_4056_);
lean_inc(v_a_4065_);
lean_inc_ref(v_a_4064_);
lean_inc(v_a_4063_);
lean_inc_ref(v_a_4062_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
lean_inc(v_a_4057_);
v___x_4123_ = lean_apply_11(v_kna_4055_, v_goal_4054_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, lean_box(0));
return v___x_4123_;
}
}
}
else
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_dec_ref(v_toGoalState_4067_);
lean_dec_ref(v_kp_4056_);
lean_dec_ref(v_kna_4055_);
lean_dec_ref(v_goal_4054_);
v___x_4125_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4127_, lean_object* v_kna_4128_, lean_object* v_kp_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4127_, v_kna_4128_, v_kp_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4141_, lean_object* v_kp_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = lean_unsigned_to_nat(1000000u);
v___x_4154_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4155_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4153_, v___x_4154_, v_a_4141_, v_kp_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4156_, lean_object* v_kp_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4156_, v_kp_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4169_, lean_object* v_kna_4170_, lean_object* v_kp_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4169_, v_kp_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4183_, lean_object* v_kna_4184_, lean_object* v_kp_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4183_, v_kna_4184_, v_kp_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_kna_4184_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4197_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4212_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4225_, lean_object* v___f_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Lean_Meta_Grind_Action_andThen(v_a_4225_, v___f_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4241_, lean_object* v___f_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4241_, v___f_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4269_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4269_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4269_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___f_4264_; lean_object* v___f_4265_; lean_object* v___x_4267_; 
v___f_4264_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4265_, 0, v_a_4260_);
lean_closure_set(v___f_4265_, 1, v___f_4264_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___f_4265_);
v___x_4267_ = v___x_4262_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___f_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
else
{
return v___x_4259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4271_;
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
